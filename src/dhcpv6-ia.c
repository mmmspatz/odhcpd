/**
 * Copyright (C) 2013 Steven Barth <steven@midlink.org>
 * Copyright (C) 2016 Hans Dedecker <dedeckeh@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 */

#include "odhcpd.h"
#include "dhcpv6.h"
#include "dhcpv4.h"
#include "dhcpv6-ia.h"
#include "statefiles.h"

#include <time.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <resolv.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <arpa/inet.h>

#include <libubox/md5.h>

static void dhcpv6_netevent_cb(unsigned long event, struct netevent_handler_info *info);
static void apply_lease(struct dhcpv6_lease *a, bool add);
static void set_border_assignment_size(struct interface *iface, struct dhcpv6_lease *b);
static void handle_addrlist_change(struct netevent_handler_info *info);
static void start_reconf(struct dhcpv6_lease *a);
static void stop_reconf(struct dhcpv6_lease *a);
static void valid_until_cb(struct uloop_timeout *event);

static struct netevent_handler dhcpv6_netevent_handler = { .cb = dhcpv6_netevent_cb, };
static struct uloop_timeout valid_until_timeout = {.cb = valid_until_cb};
static uint32_t serial = 0;

static struct dhcpv6_lease *
dhcpv6_alloc_lease(size_t extra_len)
{
	struct dhcpv6_lease *a = calloc(1, sizeof(*a) + extra_len);

	if (!a)
		return NULL;

	a->iface_avl.key = &a->ia;
	INIT_LIST_HEAD(&a->lease_cfg_list);

	return a;
}

void dhcpv6_free_lease(struct dhcpv6_lease *a)
{
	if (!a)
		return;

	if (avl_find(&a->iface->ia_assignments, &a->ia) == &a->iface_avl) {
		debug("free_lease: removing %s %08x/%" PRIx64 " from tree on %s",
		      (a->ia.flags & DHCPV6_IA_NA) ? "NA" : "PD",
		      a->ia.assigned_subnet_id, a->ia.assigned_host_id,
		      a->iface->name);
		avl_delete(&a->iface->ia_assignments, &a->iface_avl);
	} else {
		debug("free_lease: %s %08x/%" PRIx64 " not in tree (iface=%p)",
		      (a->ia.flags & DHCPV6_IA_NA) ? "NA" : "PD",
		      a->ia.assigned_subnet_id, a->ia.assigned_host_id,
		      a->iface);
	}
	list_del(&a->lease_cfg_list);

	if (a->bound && (a->ia.flags & DHCPV6_IA_PD))
		apply_lease(a, false);

	if (a->fr_cnt)
		stop_reconf(a);

	free(a->hostname);
	free(a);
}

int dhcpv6_ia_init(void)
{
	uloop_timeout_set(&valid_until_timeout, 1000);

	netlink_add_netevent_handler(&dhcpv6_netevent_handler);

	return 0;
}

int dhcpv6_ia_setup_interface(struct interface *iface, bool enable)
{
	enable = enable && (iface->dhcpv6 == MODE_SERVER);

	if (enable) {
		struct dhcpv6_lease *border;

		if (avl_is_empty(&iface->ia_assignments)) {
			border = dhcpv6_alloc_lease(0);

			if (!border) {
				warn("Failed to alloc border on %s", iface->name);
				return -1;
			}

			border->iface = iface;
			border->ia.flags = DHCPV6_IA_PD;
			border->ia.length = 64;
		} else {
			border = avl_last_element(&iface->ia_assignments, border, iface_avl);
			avl_delete(&iface->ia_assignments, &border->iface_avl);
		}

		set_border_assignment_size(iface, border);
		avl_insert(&iface->ia_assignments, &border->iface_avl);
		debug("ia_setup: %s enabled, border subnet_id %08x",
		      iface->name, border->ia.assigned_subnet_id);
	} else {
		struct dhcpv6_lease *c, *n;
		debug("ia_setup: %s disabled, freeing %d leases",
		      iface->name, iface->ia_assignments.count);
		avl_for_each_element_safe(&iface->ia_assignments, c, iface_avl, n)
			dhcpv6_free_lease(c);
	}

	return 0;
}


static void dhcpv6_netevent_cb(unsigned long event, struct netevent_handler_info *info)
{
	struct interface *iface = info->iface;

	if (!iface || iface->dhcpv6 != MODE_SERVER)
		return;

	switch (event) {
	case NETEV_ADDR6LIST_CHANGE:
		handle_addrlist_change(info);
		break;
	default:
		break;
	}
}

size_t get_preferred_addr(const struct odhcpd_ipaddr *addrs, const size_t addrlen)
{
	size_t i, m;

	for (i = 0, m = 0; i < addrlen; ++i) {
		if (addrs[i].preferred_lt > addrs[m].preferred_lt ||
				(addrs[i].preferred_lt == addrs[m].preferred_lt &&
				memcmp(&addrs[i].addr, &addrs[m].addr, 16) > 0))
			m = i;
	}

	return m;
}

enum {
	IOV_HDR = 0,
	IOV_SERVERID,
	IOV_CLIENTID,
	IOV_MESSAGE,
	IOV_AUTH,
	IOV_TOTAL
};

static int send_reconf(struct dhcpv6_lease *assign)
{
	struct interface *iface = assign->iface;
	struct dhcpv6_client_header hdr = {
		.msg_type = DHCPV6_MSG_RECONFIGURE,
		.transaction_id = { 0, 0, 0 },
	};
	struct {
		uint16_t code;
		uint16_t len;
		uint8_t data[DUID_MAX_LEN];
	} _o_packed serverid = {
		.code = htons(DHCPV6_OPT_SERVERID),
		.len = 0,
		.data = { 0 },
	};
	struct {
		uint16_t code;
		uint16_t len;
		uint8_t data[DUID_MAX_LEN];
	} _o_packed clientid = {
		.code = htons(DHCPV6_OPT_CLIENTID),
		.len = htons(assign->duid_len),
		.data = { 0 },
	};
	struct {
		uint16_t code;
		uint16_t len;
		uint8_t id;
	} _o_packed message = {
		.code = htons(DHCPV6_OPT_RECONF_MSG),
		.len = htons(1),
		.id = DHCPV6_MSG_RENEW,
	};
	struct dhcpv6_auth_reconfigure auth = {
		.type = htons(DHCPV6_OPT_AUTH),
		.len = htons(sizeof(struct dhcpv6_auth_reconfigure)),
		.protocol = 3,
		.algorithm = 1,
		.rdm = 0,
		.replay = { htonl(time(NULL)), htonl(++serial) },
		.reconf_type = 2,
		.key = { 0 },
	};

	if (config.default_duid_len > 0) {
		memcpy(serverid.data, config.default_duid, config.default_duid_len);
		serverid.len = htons(config.default_duid_len);
	} else {
		uint16_t duid_ll_hdr[] = { htons(DUID_TYPE_LL), htons(ARPHRD_ETHER) };
		memcpy(serverid.data, duid_ll_hdr, sizeof(duid_ll_hdr));
		odhcpd_get_mac(iface, &serverid.data[sizeof(duid_ll_hdr)]);
		serverid.len = htons(sizeof(duid_ll_hdr) + ETH_ALEN);
	}

	memcpy(clientid.data, assign->duid, assign->duid_len);

	size_t serverid_len, clientid_len;
	serverid_len = sizeof(serverid.code) + sizeof(serverid.len) + ntohs(serverid.len);
	clientid_len = sizeof(clientid.code) + sizeof(clientid.len) + ntohs(clientid.len);

	struct iovec iov[IOV_TOTAL] = {
		[IOV_HDR] = { &hdr, sizeof(hdr) },
		[IOV_SERVERID] = { &serverid, serverid_len },
		[IOV_CLIENTID] = { &clientid, clientid_len },
		[IOV_MESSAGE] = { &message, sizeof(message) },
		[IOV_AUTH] = { &auth, sizeof(auth) },
	};

	md5_ctx_t md5;
	uint8_t secretbytes[64];
	memset(secretbytes, 0, sizeof(secretbytes));
	memcpy(secretbytes, assign->key, sizeof(assign->key));

	for (size_t i = 0; i < sizeof(secretbytes); ++i)
		secretbytes[i] ^= 0x36;

	md5_begin(&md5);
	md5_hash(secretbytes, sizeof(secretbytes), &md5);
	for (size_t i = 0; i < ARRAY_SIZE(iov); i++)
		md5_hash(iov[i].iov_base, iov[i].iov_len, &md5);
	md5_end(auth.key, &md5);

	for (size_t i = 0; i < sizeof(secretbytes); ++i) {
		secretbytes[i] ^= 0x36;
		secretbytes[i] ^= 0x5c;
	}

	md5_begin(&md5);
	md5_hash(secretbytes, sizeof(secretbytes), &md5);
	md5_hash(auth.key, 16, &md5);
	md5_end(auth.key, &md5);

	return odhcpd_send(iface->dhcpv6_event.uloop.fd, &assign->peer, iov, ARRAY_SIZE(iov), iface);
}

static void in6_copy_iid(struct in6_addr *dest, uint64_t iid, unsigned n)
{
	uint64_t iid_be = htobe64(iid);
	uint8_t *iid_bytes = (uint8_t *)&iid_be;
	unsigned bytes = n / 8;
	unsigned bits = n % 8;

	if (n == 0 || n > 64)
		return;

	memcpy(&dest->s6_addr[16 - bytes], &iid_bytes[8 - bytes], bytes);

	if (bits > 0) {
		unsigned dest_idx = 16 - bytes - 1;
		unsigned src_idx = 8 - bytes - 1;
		uint8_t mask = (1 << bits) - 1;
		dest->s6_addr[dest_idx] = (dest->s6_addr[dest_idx] & ~mask) |
					  (iid_bytes[src_idx] & mask);
	}
}

struct in6_addr in6_from_prefix_and_iid(const struct odhcpd_ipaddr *prefix, uint64_t iid)
{
	struct in6_addr addr;
	uint8_t iid_len = min(128 - prefix->prefix_len, 64);

	addr = prefix->addr.in6;
	in6_copy_iid(&addr, iid, iid_len);

	return addr;
}

static void __apply_lease(struct dhcpv6_lease *a,
		struct odhcpd_ipaddr *addrs, ssize_t addr_len, bool add)
{
	if (a->ia.flags & DHCPV6_IA_NA)
		return;

	for (ssize_t i = 0; i < addr_len; ++i) {
		struct in6_addr prefix;

		if (ADDR_MATCH_PIO_FILTER(&addrs[i], a->iface))
			continue;

		prefix = addrs[i].addr.in6;
		prefix.s6_addr32[1] |= htonl(a->ia.assigned_subnet_id);
		prefix.s6_addr32[2] = prefix.s6_addr32[3] = 0;
		netlink_setup_route(&prefix, a->ia.length, a->iface->ifindex,
				    &a->peer.sin6_addr, 1024, add);
	}
}

static void apply_lease(struct dhcpv6_lease *a, bool add)
{
	struct interface *iface = a->iface;
	struct odhcpd_ipaddr *addrs = iface->addr6;
	ssize_t addrlen = (ssize_t)iface->addr6_len;

	__apply_lease(a, addrs, addrlen, add);
}

/* Set border assignment size based on the IPv6 address prefixes */
static void set_border_assignment_size(struct interface *iface, struct dhcpv6_lease *b)
{
	time_t now = odhcpd_time();
	int minprefix = -1;

	for (size_t i = 0; i < iface->addr6_len; ++i) {
		struct odhcpd_ipaddr *addr = &iface->addr6[i];

		if (ADDR_MATCH_PIO_FILTER(addr, iface))
			continue;

		if (addr->preferred_lt > (uint32_t)now &&
		    addr->prefix_len < 64 &&
		    addr->prefix_len > minprefix)
			minprefix = addr->prefix_len;
	}

	if (minprefix > 32 && minprefix <= 64)
		b->ia.assigned_subnet_id = 1U << (64 - minprefix);
	else
		b->ia.assigned_subnet_id = 0;
}

static bool assign_pd(struct interface *iface, struct dhcpv6_lease *assign)
{
	if (iface->addr6_len < 1)
		return false;

	uint32_t left_end, candidate;
	const struct dhcpv6_lease * left, *right;

	const uint32_t asize = (1U << (64 - assign->ia.length)) - 1;
	const struct dhcpv6_lease * const border = avl_last_element(&iface->ia_assignments, border, iface_avl);
	const struct dhcpv6_ia first_delegation_key = {.flags = DHCPV6_IA_PD};
	const struct dhcpv6_lease * const first_delegation = avl_find_ge_element(
		&iface->ia_assignments, &first_delegation_key, first_delegation, iface_avl);

	debug("assign_pd: /%u hint %08x border %08x asize %08x on %s",
	      assign->ia.length, assign->ia.assigned_subnet_id,
	      border->ia.assigned_subnet_id, asize, iface->name);

	/* Try honoring the hint first */
	candidate = assign->ia.assigned_subnet_id &
		(border->ia.assigned_subnet_id - 1) & // clear bits above the delegatable space
		~asize; // clear bits below the delegation size
	const struct dhcpv6_ia candidate_key = {.assigned_subnet_id = candidate, .flags = DHCPV6_IA_PD};
	left = avl_find_le_element(&iface->ia_assignments, &candidate_key, left, iface_avl);
	left_end = (left && (left->ia.flags & DHCPV6_IA_PD))
			? left->ia.assigned_subnet_id + (1U << (64 - left->ia.length))
			: 1;
	right = left ? avl_next_element(left, iface_avl) : first_delegation;

	debug("assign_pd: hint candidate %08x left_end %08x right %08x",
	      candidate, left_end, right->ia.assigned_subnet_id);

	if (candidate >= left_end &&
	    candidate + asize < right->ia.assigned_subnet_id) {
		assign->ia.assigned_subnet_id = candidate;
		if (avl_insert(&iface->ia_assignments, &assign->iface_avl))
			return false;

		debug("assign_pd chose subnet_id %08x on %s (hint honored)",
			assign->ia.assigned_subnet_id, iface->name);

		if (assign->bound)
			apply_lease(assign, true);

		return true;
	}

	/* Fallback to first-fit assignment */
	left_end = 1;
	avl_for_element_to_last(&iface->ia_assignments, first_delegation, right, iface_avl) {
		candidate = (left_end + asize) & (~asize);

		if (candidate + asize < right->ia.assigned_subnet_id) {
			assign->ia.assigned_subnet_id = candidate;
			if (avl_insert(&iface->ia_assignments, &assign->iface_avl))
				return false;

			debug("assign_pd chose subnet_id %08x on %s",
				assign->ia.assigned_subnet_id, iface->name);

			if (assign->bound)
				apply_lease(assign, true);

			return true;
		}

		left_end = right->ia.assigned_subnet_id + (1U << (64 - right->ia.length));
	}

	debug("assign_pd: no space for /%u on %s", assign->ia.length, iface->name);
	return false;
}

/* Check iid against reserved IPv6 interface identifiers.
 * Refer to: http://www.iana.org/assignments/ipv6-interface-ids
 */
static bool is_reserved_ipv6_iid(uint64_t iid)
{
	if (iid == 0x0000000000000000)
		/* Subnet-Router Anycast [RFC4291] */
		return true;

	if ((iid & 0xFFFFFFFFFF000000) == 0x02005EFFFE000000)
		/* Reserved IPv6 Interface Identifiers corresponding
		 * to the IANA Ethernet Block [RFC4291]
		 */
		return true;

	if ((iid & 0xFFFFFFFFFFFFFF80) == 0xFDFFFFFFFFFFFF80)
		/* Reserved Subnet Anycast Addresses [RFC2526] */
		return true;

	return false;
}

static bool assign_na(struct interface *iface, struct dhcpv6_lease *a)
{
	uint64_t pool_start = 0x100;
	uint64_t pool_end = (iface->dhcpv6_hostid_len >= 64) ? UINT64_MAX : ((1ULL << iface->dhcpv6_hostid_len) - 1);
	uint64_t pool_size = pool_end - pool_start + 1;
	uint64_t try;
	unsigned short xsubi[3] = { 0 };

	/* Preconfigured assignment by static lease */
	if (a->ia.assigned_host_id) {
		bool ok = !avl_insert(&iface->ia_assignments, &a->iface_avl);
		debug("assign_na: static host_id %" PRIx64 " on %s: %s",
		      a->ia.assigned_host_id, iface->name,
		      ok ? "ok" : "duplicate");
		return ok;
	}

	/* Pick a starting point, using the last bytes of the DUID as seed... */
	memcpy(xsubi,
	       a->duid + (a->duid_len > sizeof(xsubi) ? a->duid_len - sizeof(xsubi) : 0),
	       min(a->duid_len, sizeof(xsubi)));
	try = ((uint64_t)jrand48(xsubi) << 32) | (jrand48(xsubi) & UINT32_MAX);
	try = pool_start + try % pool_size;

	/* ...then try to assign sequentially from that starting point... */
	for (size_t i = 0; i < 100; i++, try++) {
		if (try > pool_end)
			try = pool_start;

		if (is_reserved_ipv6_iid(try))
			continue;

		if (config_find_lease_cfg_by_hostid(try))
			continue;

		a->ia.assigned_host_id = try;
		if (!avl_insert(&iface->ia_assignments, &a->iface_avl)) {
			debug("assign_na: chose host_id %" PRIx64 " on %s",
			      a->ia.assigned_host_id, iface->name);
			return true;
		}
	}

	debug("assign_na: exhausted 100 tries on %s", iface->name);
	return false;
}

static void handle_addrlist_change(struct netevent_handler_info *info)
{
	struct interface *iface = info->iface;
	struct dhcpv6_lease *c, *d, *border;
	struct list_head reassign = LIST_HEAD_INIT(reassign);
	time_t now = odhcpd_time();

	border = avl_last_element(&iface->ia_assignments, border, iface_avl);

	avl_for_each_element(&iface->ia_assignments, c, iface_avl) {
		if ((c->ia.flags & DHCPV6_IA_PD) && !(iface->ra_flags & ND_RA_FLAG_MANAGED)
		    && (c->bound))
			__apply_lease(c, info->addrs_old.addrs,
					info->addrs_old.len, false);
	}

	debug("addrlist_change: old border %08x on %s",
	      border->ia.assigned_subnet_id, iface->name);
	avl_delete(&iface->ia_assignments, &border->iface_avl);
	set_border_assignment_size(iface, border);
	avl_insert(&iface->ia_assignments, &border->iface_avl);
	debug("addrlist_change: new border %08x on %s",
	      border->ia.assigned_subnet_id, iface->name);

	avl_for_each_element_safe(&iface->ia_assignments, c, iface_avl, d) {
		if (c->duid_len == 0 ||
			!(c->ia.flags & DHCPV6_IA_PD)	||
		    (!INFINITE_VALID(c->valid_until) && c->valid_until < now))
			continue;

		if (c->ia.assigned_subnet_id >= border->ia.assigned_subnet_id) {
			debug("addrlist_change: subnet_id %08x >= border, queuing for reassign on %s",
			      c->ia.assigned_subnet_id, iface->name);
			avl_delete(&iface->ia_assignments, &c->iface_avl);
			list_add(&c->iface_avl.list, &reassign);
		} else if (c->bound)
			apply_lease(c, true);

		if (c->accept_fr_nonce && c->fr_cnt == 0) {
			struct dhcpv6_lease *a;

			start_reconf(c);

			/* Leave all other assignments of that client alone */
			avl_for_each_element(&iface->ia_assignments, a, iface_avl)
				if (a != c && a->duid_len == c->duid_len &&
						!memcmp(a->duid, c->duid, a->duid_len))
					a->fr_cnt = INT_MAX;
		}
	}

	list_for_each_entry_safe(c, d, &reassign, iface_avl.list) {
		list_del_init(&c->iface_avl.list);
		if (!assign_pd(iface, c)) {
			debug("addrlist_change: reassign failed for subnet_id %08x on %s, freeing",
			      c->ia.assigned_subnet_id, iface->name);
			dhcpv6_free_lease(c);
		}
	}

	statefiles_write();
}

static void reconf_timeout_cb(struct uloop_timeout *event)
{
	struct dhcpv6_lease *a = container_of(event, struct dhcpv6_lease, fr_timer);

	if (a->fr_cnt > 0 && a->fr_cnt < DHCPV6_REC_MAX_RC) {
		send_reconf(a);
		uloop_timeout_set(&a->fr_timer,
				  DHCPV6_REC_TIMEOUT << a->fr_cnt);
		a->fr_cnt++;
	} else
		stop_reconf(a);
}

static void start_reconf(struct dhcpv6_lease *a)
{
	uloop_timeout_set(&a->fr_timer,
			  DHCPV6_REC_TIMEOUT << a->fr_cnt);
	a->fr_timer.cb = reconf_timeout_cb;
	a->fr_cnt++;

	send_reconf(a);
}

static void stop_reconf(struct dhcpv6_lease *a)
{
	uloop_timeout_cancel(&a->fr_timer);
	a->fr_cnt = 0;
	a->fr_timer.cb = NULL;
}

static void valid_until_cb(struct uloop_timeout *event)
{
	struct interface *iface;
	time_t now = odhcpd_time();

	avl_for_each_element(&interfaces, iface, avl) {
		struct dhcpv6_lease *a, *n;

		if (iface->dhcpv6 != MODE_SERVER)
			continue;

		avl_for_each_element_safe(&iface->ia_assignments, a, iface_avl, n) {
			if (a->duid_len > 0 && !INFINITE_VALID(a->valid_until) && a->valid_until < now) {
				debug("valid_until: expiring %s %08x/%" PRIx64 " on %s",
				      (a->ia.flags & DHCPV6_IA_NA) ? "NA" : "PD",
				      a->ia.assigned_subnet_id, a->ia.assigned_host_id,
				      iface->name);
				dhcpv6_free_lease(a);
			}
		}
	}
	uloop_timeout_set(event, 1000);
}

static size_t build_ia(uint8_t *buf, size_t buflen, uint16_t status,
		const struct dhcpv6_ia_hdr *ia, struct dhcpv6_lease *a,
		struct interface *iface, bool request)
{
	struct dhcpv6_ia_hdr o_ia = {
		.type = ia->type,
		.len = 0,
		.iaid = ia->iaid,
		.t1 = 0,
		.t2 = 0,
	};
	size_t ia_len = sizeof(o_ia);
	time_t now = odhcpd_time();

	if (buflen < ia_len)
		return 0;

	if (status) {
		struct _o_packed {
			uint16_t type;
			uint16_t len;
			uint16_t val;
		} o_status = {
			.type = htons(DHCPV6_OPT_STATUS),
			.len = htons(sizeof(o_status) - DHCPV6_OPT_HDR_SIZE),
			.val = htons(status),
		};

		memcpy(buf + ia_len, &o_status, sizeof(o_status));
		ia_len += sizeof(o_status);

		o_ia.len = htons(ia_len - DHCPV6_OPT_HDR_SIZE);
		memcpy(buf, &o_ia, sizeof(o_ia));

		return ia_len;
	}

	if (a) {
		uint32_t leasetime;

		if (a->leasetime) {
			leasetime = a->leasetime;
		} else {
			leasetime = iface->dhcp_leasetime;
		}

		uint32_t floor_preferred_lifetime, floor_valid_lifetime; /* For calculating T1 / T2 */

		if (iface->max_preferred_lifetime && iface->max_preferred_lifetime < leasetime) {
			floor_preferred_lifetime = iface->max_preferred_lifetime;
		} else {
			floor_preferred_lifetime = leasetime;
		}

		if (iface->max_valid_lifetime && iface->max_valid_lifetime < leasetime) {
			floor_valid_lifetime = iface->max_valid_lifetime;
		} else {
			floor_valid_lifetime = leasetime;
		}

		struct odhcpd_ipaddr *addrs = iface->addr6;
		size_t addrlen = iface->addr6_len;
		size_t m = get_preferred_addr(addrs, addrlen);

		for (size_t i = 0; i < addrlen; ++i) {
			uint32_t prefix_preferred_lt, prefix_valid_lt;

			if (!valid_addr(&addrs[i], now))
				continue;

			/* Filter Out Prefixes */
			if (ADDR_MATCH_PIO_FILTER(&addrs[i], iface)) {
				char addrbuf[INET6_ADDRSTRLEN];
				info("Address %s filtered out on %s",
				     inet_ntop(AF_INET6, &addrs[i].addr.in6, addrbuf, sizeof(addrbuf)),
				     iface->name);
				continue;
			}

			prefix_preferred_lt = addrs[i].preferred_lt;
			prefix_valid_lt = addrs[i].valid_lt;

			if (prefix_preferred_lt != UINT32_MAX) {
				prefix_preferred_lt -= now;

				if (iface->max_preferred_lifetime && prefix_preferred_lt > iface->max_preferred_lifetime)
					prefix_preferred_lt = iface->max_preferred_lifetime;
			}

			if (prefix_valid_lt != UINT32_MAX) {
				prefix_valid_lt -= now;

				if (iface->max_valid_lifetime && prefix_valid_lt > iface->max_valid_lifetime)
					prefix_valid_lt = iface->max_valid_lifetime;
			}

			if (prefix_valid_lt > leasetime)
				prefix_valid_lt = leasetime;

			if (prefix_preferred_lt > prefix_valid_lt)
				prefix_preferred_lt = prefix_valid_lt;

			if (a->ia.flags & DHCPV6_IA_PD) {
				struct dhcpv6_ia_prefix o_ia_p = {
					.type = htons(DHCPV6_OPT_IA_PREFIX),
					.len = htons(sizeof(o_ia_p) - DHCPV6_OPT_HDR_SIZE),
					.preferred_lt = htonl(prefix_preferred_lt),
					.valid_lt = htonl(prefix_valid_lt),
					.prefix_len = a->ia.length,
					.addr = addrs[i].addr.in6,
				};

				o_ia_p.addr.s6_addr32[1] |= htonl(a->ia.assigned_subnet_id);
				o_ia_p.addr.s6_addr32[2] = o_ia_p.addr.s6_addr32[3] = 0;

				if (!valid_prefix_length(a, addrs[i].prefix_len))
					continue;

				if (buflen < ia_len + sizeof(o_ia_p))
					return 0;

				memcpy(buf + ia_len, &o_ia_p, sizeof(o_ia_p));
				ia_len += sizeof(o_ia_p);
			}

			if (a->ia.flags & DHCPV6_IA_NA) {
				struct dhcpv6_ia_addr o_ia_a = {
					.type = htons(DHCPV6_OPT_IA_ADDR),
					.len = htons(sizeof(o_ia_a) - DHCPV6_OPT_HDR_SIZE),
					.addr = in6_from_prefix_and_iid(&addrs[i], a->ia.assigned_host_id),
					.preferred_lt = htonl(prefix_preferred_lt),
					.valid_lt = htonl(prefix_valid_lt)
				};

				if (!ADDR_ENTRY_VALID_IA_ADDR(iface, i, m, addrs))
					continue;

				if (buflen < ia_len + sizeof(o_ia_a))
					return 0;

				memcpy(buf + ia_len, &o_ia_a, sizeof(o_ia_a));
				ia_len += sizeof(o_ia_a);
			}

			/* Calculate T1 / T2 based on non-deprecated addresses */
			if (prefix_preferred_lt > 0) {
				if (floor_preferred_lifetime > prefix_preferred_lt)
					floor_preferred_lifetime = prefix_preferred_lt;

				if (floor_valid_lifetime > prefix_valid_lt)
					floor_valid_lifetime = prefix_valid_lt;
			}
		}

		if (!INFINITE_VALID(a->valid_until))
			/* UINT32_MAX is RFC defined as infinite lease-time */
			a->valid_until = (floor_valid_lifetime == UINT32_MAX) ? 0 : floor_valid_lifetime + now;

		if (!INFINITE_VALID(a->preferred_until))
			/* UINT32_MAX is RFC defined as infinite lease-time */
			a->preferred_until = (floor_preferred_lifetime == UINT32_MAX) ? 0 : floor_preferred_lifetime + now;

		o_ia.t1 = htonl((floor_preferred_lifetime == UINT32_MAX) ? floor_preferred_lifetime : floor_preferred_lifetime * 5 / 10);
		o_ia.t2 = htonl((floor_preferred_lifetime == UINT32_MAX) ? floor_preferred_lifetime : floor_preferred_lifetime * 8 / 10);

		if (!o_ia.t1)
			o_ia.t1 = htonl(1);

		if (!o_ia.t2)
			o_ia.t2 = htonl(1);
	}

	if (!request) {
		uint8_t *odata, *end = ((uint8_t*)ia) + htons(ia->len) + DHCPV6_OPT_HDR_SIZE;
		uint16_t otype, olen;

		dhcpv6_for_each_option((uint8_t*)&ia[1], end, otype, olen, odata) {
			struct dhcpv6_ia_prefix *ia_p = (struct dhcpv6_ia_prefix *)&odata[-DHCPV6_OPT_HDR_SIZE];
			struct dhcpv6_ia_addr *ia_a = (struct dhcpv6_ia_addr *)&odata[-DHCPV6_OPT_HDR_SIZE];
			bool found = false;

			if ((otype != DHCPV6_OPT_IA_PREFIX || olen < sizeof(*ia_p) - DHCPV6_OPT_HDR_SIZE) &&
					(otype != DHCPV6_OPT_IA_ADDR || olen < sizeof(*ia_a) - DHCPV6_OPT_HDR_SIZE))
				continue;

			if (a) {
				struct odhcpd_ipaddr *addrs = iface->addr6;
				size_t addrlen = iface->addr6_len;

				for (size_t i = 0; i < addrlen; ++i) {
					struct in6_addr addr;

					if (!valid_addr(&addrs[i], now))
						continue;

					if (!valid_prefix_length(a, addrs[i].prefix_len))
						continue;

					if (ADDR_MATCH_PIO_FILTER(&addrs[i], iface))
						continue;

					if (ia->type == htons(DHCPV6_OPT_IA_PD)) {
						addr = addrs[i].addr.in6;
						addr.s6_addr32[1] |= htonl(a->ia.assigned_subnet_id);
						addr.s6_addr32[2] = addr.s6_addr32[3] = 0;

						if (!memcmp(&ia_p->addr, &addr, sizeof(addr)) &&
							    ia_p->prefix_len == a->ia.length)
							found = true;
					} else {
						addr = in6_from_prefix_and_iid(&addrs[i], a->ia.assigned_host_id);

						if (!memcmp(&ia_a->addr, &addr, sizeof(addr)))
							found = true;
					}
				}
			}

			if (!found) {
				if (otype == DHCPV6_OPT_IA_PREFIX) {
					struct dhcpv6_ia_prefix o_ia_p = {
						.type = htons(DHCPV6_OPT_IA_PREFIX),
						.len = htons(sizeof(o_ia_p) - DHCPV6_OPT_HDR_SIZE),
						.preferred_lt = 0,
						.valid_lt = 0,
						.prefix_len = ia_p->prefix_len,
						.addr = ia_p->addr,
					};

					if (buflen < ia_len + sizeof(o_ia_p))
						return 0;

					memcpy(buf + ia_len, &o_ia_p, sizeof(o_ia_p));
					ia_len += sizeof(o_ia_p);
				} else {
					struct dhcpv6_ia_addr o_ia_a = {
						.type = htons(DHCPV6_OPT_IA_ADDR),
						.len = htons(sizeof(o_ia_a) - DHCPV6_OPT_HDR_SIZE),
						.addr = ia_a->addr,
						.preferred_lt = 0,
						.valid_lt = 0,
					};

					if (buflen < ia_len + sizeof(o_ia_a))
						continue;

					memcpy(buf + ia_len, &o_ia_a, sizeof(o_ia_a));
					ia_len += sizeof(o_ia_a);
				}
			}
		}
	}

	o_ia.len = htons(ia_len - DHCPV6_OPT_HDR_SIZE);
	memcpy(buf, &o_ia, sizeof(o_ia));
	return ia_len;
}

struct log_ctxt {
	char *buf;
	int buf_len;
	/* if full, buf_idx will point to the last valid memory in buf */
	int buf_idx;
};

static void dhcpv6_log_ia_addr(_o_unused struct dhcpv6_lease *lease, struct in6_addr *addr, uint8_t prefix_len,
			       _o_unused uint32_t pref_lt, _o_unused uint32_t valid_lt, void *arg)
{
	struct log_ctxt *ctxt = (struct log_ctxt *)arg;
	char addrbuf[INET6_ADDRSTRLEN];
	int ret;

	/* Log buffer full */
	if (ctxt->buf_idx >= ctxt->buf_len - 1)
		return;

	inet_ntop(AF_INET6, addr, addrbuf, sizeof(addrbuf));
	ret = snprintf(ctxt->buf + ctxt->buf_idx, ctxt->buf_len - ctxt->buf_idx,
		       " %s/%" PRIu8, addrbuf, prefix_len);

	if (ret + ctxt->buf_idx < ctxt->buf_len - 1)
		ctxt->buf_idx += ret;
	else
		ctxt->buf_idx = ctxt->buf_len - 1;
}

static void dhcpv6_log(uint8_t msgtype, struct interface *iface, time_t now,
		const char *duidbuf, bool is_pd, struct dhcpv6_lease *a, int code)
{
	const char *type = "UNKNOWN";
	const char *status = "UNKNOWN";

	switch (msgtype) {
	case DHCPV6_MSG_SOLICIT:
		type = "SOLICIT";
		break;
	case DHCPV6_MSG_REQUEST:
		type = "REQUEST";
		break;
	case DHCPV6_MSG_CONFIRM:
		type = "CONFIRM";
		break;
	case DHCPV6_MSG_RENEW:
		type = "RENEW";
		break;
	case DHCPV6_MSG_REBIND:
		type = "REBIND";
		break;
	case DHCPV6_MSG_RELEASE:
		type = "RELEASE";
		break;
	case DHCPV6_MSG_DECLINE:
		type = "DECLINE";
		break;
	}

	switch (code) {
	case DHCPV6_STATUS_OK:
		status = "ok";
		break;
	case DHCPV6_STATUS_NOADDRSAVAIL:
		status = "no addresses available";
		break;
	case DHCPV6_STATUS_NOBINDING:
		status = "no binding";
		break;
	case DHCPV6_STATUS_NOTONLINK:
		status = "not on-link";
		break;
	case DHCPV6_STATUS_NOPREFIXAVAIL:
		status = "no prefix available";
		break;
	}

	char leasebuf[256] = "";

	if (a) {
		struct log_ctxt ctxt = {.buf = leasebuf,
					.buf_len = sizeof(leasebuf),
					.buf_idx = 0 };

		odhcpd_enum_addr6(iface, a, now, dhcpv6_log_ia_addr, &ctxt);
	}

	info("DHCPV6 %s %s from %s on %s: %s%s", type, (is_pd) ? "IA_PD" : "IA_NA",
	     duidbuf, iface->name, status, leasebuf);
}

static bool dhcpv6_ia_on_link(const struct dhcpv6_ia_hdr *ia, struct dhcpv6_lease *a,
		struct interface *iface)
{
	struct odhcpd_ipaddr *addrs = iface->addr6;
	size_t addrlen = iface->addr6_len;
	time_t now = odhcpd_time();
	uint8_t *odata, *end = ((uint8_t*)ia) + htons(ia->len) + DHCPV6_OPT_HDR_SIZE;
	uint16_t otype, olen;
	bool onlink = true;

	dhcpv6_for_each_option((uint8_t*)&ia[1], end, otype, olen, odata) {
		struct dhcpv6_ia_prefix *p = (struct dhcpv6_ia_prefix *)&odata[-DHCPV6_OPT_HDR_SIZE];
		struct dhcpv6_ia_addr *n = (struct dhcpv6_ia_addr *)&odata[-DHCPV6_OPT_HDR_SIZE];

		if ((otype != DHCPV6_OPT_IA_PREFIX || olen < sizeof(*p) - DHCPV6_OPT_HDR_SIZE) &&
				(otype != DHCPV6_OPT_IA_ADDR || olen < sizeof(*n) - DHCPV6_OPT_HDR_SIZE))
			continue;

		onlink = false;
		for (size_t i = 0; i < addrlen; ++i) {
			if (!valid_addr(&addrs[i], now))
				continue;

			if (ADDR_MATCH_PIO_FILTER(&addrs[i], iface))
				continue;

			if (ia->type == htons(DHCPV6_OPT_IA_PD)) {
				if (p->prefix_len < addrs[i].prefix_len ||
				    odhcpd_bmemcmp(&p->addr, &addrs[i].addr.in6, addrs[i].prefix_len))
					continue;

			} else if (odhcpd_bmemcmp(&n->addr, &addrs[i].addr.in6, addrs[i].prefix_len))
				continue;

			onlink = true;
		}

		if (!onlink)
			break;
	}

	return onlink;
}

ssize_t dhcpv6_ia_handle_IAs(uint8_t *buf, size_t buflen, struct interface *iface,
		const struct sockaddr_in6 *addr, const void *data, const uint8_t *end)
{
	struct dhcpv6_lease *first = NULL;
	const struct dhcpv6_client_header *hdr = data;
	time_t now = odhcpd_time();
	uint16_t otype, olen, duid_len = 0;
	uint8_t *start = (uint8_t *)&hdr[1], *odata;
	uint8_t *duid = NULL, mac[6] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
	size_t hostname_len = 0, response_len = 0;
	bool notonlink = false, rapid_commit = false, accept_reconf = false;
	char duidbuf[DUID_HEXSTRLEN], hostname[256];

	dhcpv6_for_each_option(start, end, otype, olen, odata) {
		switch (otype) {
		case DHCPV6_OPT_CLIENTID:
			duid = odata;
			duid_len = olen;

			if (olen == 14 && odata[0] == 0 && odata[1] == 1)
				memcpy(mac, &odata[8], sizeof(mac));
			else if (olen == 10 && odata[0] == 0 && odata[1] == 3)
				memcpy(mac, &odata[4], sizeof(mac));

			if (olen <= DUID_MAX_LEN)
				odhcpd_hexlify(duidbuf, odata, olen);
			break;

		case DHCPV6_OPT_FQDN:
			if (olen < 2 || olen > 255)
				break;

			uint8_t fqdn_buf[256];
			memcpy(fqdn_buf, odata, olen);
			fqdn_buf[olen++] = 0;

			if (dn_expand(&fqdn_buf[1], &fqdn_buf[olen], &fqdn_buf[1], hostname, sizeof(hostname)) > 0)
				hostname_len = strcspn(hostname, ".");

			break;

		case DHCPV6_OPT_RECONF_ACCEPT:
			accept_reconf = true;
			break;

		case DHCPV6_OPT_RAPID_COMMIT:
			if (hdr->msg_type == DHCPV6_MSG_SOLICIT)
				rapid_commit = true;
			break;

		default:
			break;
		}
	}

	if (!duid || duid_len < DUID_MIN_LEN || duid_len > DUID_MAX_LEN)
		goto out;

	dhcpv6_for_each_option(start, end, otype, olen, odata) {
		bool ia_addr_present = false;
		struct dhcpv6_ia_hdr *ia = (struct dhcpv6_ia_hdr*)&odata[-DHCPV6_OPT_HDR_SIZE];
		struct dhcpv6_ia req = {0};

		size_t ia_response_len = 0;

		struct lease_cfg *lease_cfg;

		lease_cfg = config_find_lease_cfg_by_duid_and_iaid(duid, duid_len, ntohl(ia->iaid));
		if (!lease_cfg)
			lease_cfg = config_find_lease_cfg_by_mac(mac);

		if (lease_cfg && lease_cfg->ignore6)
			return -1;

		uint8_t *sdata;
		uint16_t stype, slen;
		switch (otype) {
		case DHCPV6_OPT_IA_PD:
			req.flags = DHCPV6_IA_PD;
			req.length = 62;

			dhcpv6_for_each_sub_option(&ia[1], odata + olen, stype, slen, sdata) {
				if (stype != DHCPV6_OPT_IA_PREFIX || slen < sizeof(struct dhcpv6_ia_prefix) - DHCPV6_OPT_HDR_SIZE)
					continue;

				struct dhcpv6_ia_prefix *p = (struct dhcpv6_ia_prefix*)&sdata[-DHCPV6_OPT_HDR_SIZE];
				if (p->prefix_len) {
					req.length = p->prefix_len;
					req.assigned_subnet_id = ntohl(p->addr.s6_addr32[1]);
				}
			}

			if (req.length < 33)
				req.length = 33;
			if (req.length > 64)
				req.length = 64;

			/*
			 * A requesting router can include a desired prefix length for its
			 * delegation. The delegating router (us) is not required to honor
			 * the hint (RFC3633, section 11.2, we MAY choose to use the
			 * information in the option; RFC8168, section 3.2 has several SHOULDs
			 * about desired choices for selecting a prefix to delegate).
			 *
			 * We support a policy setting to conserve prefix space, which purposely
			 * assigns prefixes that might not match the requesting router's hint.
			 *
			 * If the minimum prefix length is set in this interface's
			 * configuration, we use it as a floor for the requested (hinted)
			 * prefix length. This allows us to conserve prefix space so that
			 * any single router can't grab too much of it. Consider if we have
			 * an interface with a /56 prefix. A requesting router could ask for
			 * a /58 and take 1/4 of our total address space. But if we set a
			 * minimum of /60, we can limit each requesting router to get only
			 * 1/16 of our total address space.
			 */
			if (iface->dhcpv6_pd_min_len && req.length < iface->dhcpv6_pd_min_len) {
				info("clamping requested PD from %d to %d", req.length,
				     iface->dhcpv6_pd_min_len);
				req.length = iface->dhcpv6_pd_min_len;
			}

			break;
		case DHCPV6_OPT_IA_NA:
			req.flags = DHCPV6_IA_NA;
			req.length = 128;
			if (lease_cfg)
				req.assigned_host_id = lease_cfg->hostid;

			dhcpv6_for_each_sub_option(&ia[1], odata + olen, stype, slen, sdata) {
				if (stype != DHCPV6_OPT_IA_ADDR || slen < sizeof(struct dhcpv6_ia_addr) - DHCPV6_OPT_HDR_SIZE)
					continue;

				ia_addr_present = true;
			}

			break;
		default:
			continue;
		}

		/* Find an existing assignment */
		struct dhcpv6_lease *c, *a = NULL;
		avl_for_each_element(&iface->ia_assignments, c, iface_avl) {
			/* Is this the right type of IA? */
			if (((req.flags ^ c->ia.flags) & (DHCPV6_IA_PD | DHCPV6_IA_NA)))
				continue;

			/* Is this assignment still valid? */
			if (!INFINITE_VALID(c->valid_until) && now >= c->valid_until)
				continue;

			/* Does the DUID match? */
			if (c->duid_len != duid_len || memcmp(c->duid, duid, duid_len))
				continue;

			/* Does the IAID match? */
			if (c->iaid != ia->iaid) {
				if (req.flags & DHCPV6_IA_PD)
					continue;

				if (!lease_cfg)
					continue;

				/* Does the existing assignment stem from the same static lease cfg? */
				if (c->lease_cfg != lease_cfg)
					continue;

				/*
				 * If there's a DUID configured for this static lease, but without
				 * an IAID, we will proceed under the assumption that a request
				 * with the right DUID but with *any* IAID should be able to take
				 * over the assignment. E.g. when switching from WiFi to Ethernet
				 * on the same client. This is similar to how multiple MAC addresses
				 * are handled for DHCPv4.
				 */
				for (size_t i = 0; i < lease_cfg->duid_count; i++) {
					if (lease_cfg->duids[i].iaid_set && lease_cfg->duids[i].iaid != htonl(ia->iaid))
						continue;

					if (lease_cfg->duids[i].len != duid_len)
						continue;

					if (memcmp(lease_cfg->duids[i].id, duid, duid_len))
						continue;

					/*
					 * Reconf doesn't specify the IAID, so we have to assume the client
					 * already knows or doesn't care about the old assignment.
					 */
					debug("handle_IAs: static lease reconfig, freeing old assignment on %s",
					      iface->name);
					stop_reconf(c);
					dhcpv6_free_lease(c);
					goto proceed;
				}
				continue;
			}

			/* We have a match */
			a = c;
			debug("handle_IAs: found existing %s assignment on %s",
			      (a->ia.flags & DHCPV6_IA_NA) ? "NA" : "PD",
			      iface->name);

			/* Reset state */
			if (a->bound)
				apply_lease(a, false);

			stop_reconf(a);
			break;
		}

		if (lease_cfg && a && a->lease_cfg != lease_cfg) {
			debug("handle_IAs: lease_cfg mismatch, freeing assignment on %s",
			      iface->name);
			dhcpv6_free_lease(a);
			a = NULL;
		}

proceed:
		/* Generic message handling */
		uint16_t status = DHCPV6_STATUS_OK;
		bool assigned = false;

		switch (hdr->msg_type) {
		case DHCPV6_MSG_SOLICIT:
		case DHCPV6_MSG_REQUEST:
		case DHCPV6_MSG_REBIND: {
			if (hdr->msg_type == DHCPV6_MSG_REBIND && a)
				break;

			if (a)
				assigned = true;
			else {
				if ((!iface->no_dynamic_dhcp || (lease_cfg && (req.flags & DHCPV6_IA_NA))) &&
				    (iface->dhcpv6_pd || iface->dhcpv6_na)) {
					/* Create new binding */
					a = dhcpv6_alloc_lease(duid_len);

					if (a) {
						a->duid_len = duid_len;
						memcpy(a->duid, duid, duid_len);
						a->iaid = ia->iaid;
						a->peer = *addr;
						a->iface = iface;
						a->valid_until = now;
						a->preferred_until = now;
						a->ia = req;

						if (first)
							memcpy(a->key, first->key, sizeof(a->key));
						else
							odhcpd_urandom(a->key, sizeof(a->key));

						if ((req.flags & DHCPV6_IA_PD) && iface->dhcpv6_pd) {
							while (!(assigned = assign_pd(iface, a)) &&
								 ++a->ia.length <= 64);
						} else if ((req.flags & DHCPV6_IA_NA) && iface->dhcpv6_na) {
							assigned = assign_na(iface, a);
						}

						debug("handle_IAs: new %s binding on %s: %s",
						      (req.flags & DHCPV6_IA_NA) ? "NA" : "PD",
						      iface->name,
						      assigned ? "assigned" : "failed");

						if (lease_cfg && assigned) {
							if (lease_cfg->hostname) {
								a->hostname = strdup(lease_cfg->hostname);
								a->hostname_valid = true;
							}

							if (lease_cfg->leasetime)
								a->leasetime = lease_cfg->leasetime;

							list_add(&a->lease_cfg_list, &lease_cfg->dhcpv6_leases);
							a->lease_cfg = lease_cfg;
						}
					}
				}
			}

			/* Status evaluation */
			if (!assigned || iface->addr6_len == 0) {
				/* Set error status */
				status = (req.flags & DHCPV6_IA_PD) ? DHCPV6_STATUS_NOPREFIXAVAIL : DHCPV6_STATUS_NOADDRSAVAIL;
			} else if (hdr->msg_type == DHCPV6_MSG_REQUEST && !dhcpv6_ia_on_link(ia, a, iface)) {
				/* Send NOTONLINK status for the IA */
				status = DHCPV6_STATUS_NOTONLINK;
				assigned = false;
			}

			/* Reconfigure Accept */
			if (accept_reconf && assigned && !first &&
				hdr->msg_type != DHCPV6_MSG_REBIND) {

				size_t handshake_len = 4;
				buf[0] = 0;
				buf[1] = DHCPV6_OPT_RECONF_ACCEPT;
				buf[2] = 0;
				buf[3] = 0;

				if (hdr->msg_type == DHCPV6_MSG_REQUEST) {
					struct dhcpv6_auth_reconfigure auth = {
						htons(DHCPV6_OPT_AUTH),
						htons(sizeof(auth) - DHCPV6_OPT_HDR_SIZE),
						3, 1, 0,
						{htonl(time(NULL)), htonl(++serial)},
						1,
						{0}
					};

					memcpy(auth.key, a->key, sizeof(a->key));
					memcpy(buf + handshake_len, &auth, sizeof(auth));
					handshake_len += sizeof(auth);
				}

				buf += handshake_len;
				buflen -= handshake_len;
				response_len += handshake_len;

				first = a;
			}

			ia_response_len = build_ia(
				buf, buflen, status, ia, a, iface,
				hdr->msg_type != DHCPV6_MSG_REBIND);

			/* Was only a solicitation: mark binding for removal in 60 seconds */
			if (assigned) {
				switch (hdr->msg_type) {
				case DHCPV6_MSG_SOLICIT:
					if (!rapid_commit) {
						a->bound = false;
						a->valid_until = now + 60;
						break;
					}

					_o_fallthrough;
				case DHCPV6_MSG_REQUEST:
				case DHCPV6_MSG_REBIND:
					if (hostname_len > 0 && (!a->lease_cfg || !a->lease_cfg->hostname)) {

						char *tmp = realloc(a->hostname, hostname_len + 1);
						if (tmp) {
							a->hostname = tmp;
							memcpy(a->hostname, hostname, hostname_len);
							a->hostname[hostname_len] = 0;
							a->hostname_valid = odhcpd_hostname_valid(a->hostname);
						}
					}

					a->accept_fr_nonce = accept_reconf;
					a->bound = true;
					apply_lease(a, true);
					break;

				default:
					break;
				}
			} else {
				/* Clean up failed assignment */
				debug("handle_IAs: freeing unassigned %s lease on %s",
				      (a->ia.flags & DHCPV6_IA_NA) ? "NA" : "PD",
				      iface->name);
				dhcpv6_free_lease(a);
				a = NULL;
			}

			break;
		}

		case DHCPV6_MSG_RENEW:
		case DHCPV6_MSG_RELEASE:
		case DHCPV6_MSG_DECLINE: {
			/* RENEW / RELEASE / DECLINE require an existing binding */
			if (!a) {
				status = DHCPV6_STATUS_NOBINDING;
				ia_response_len = build_ia(buf, buflen, status, ia, a, iface, false);
				break;
			}

			switch (hdr->msg_type) {
			case DHCPV6_MSG_RENEW:
				ia_response_len = build_ia(buf, buflen, status, ia, a, iface, false);

				a->bound = true;
				apply_lease(a, true);
				break;

			case DHCPV6_MSG_RELEASE:
				/* Immediately expire the lease */
				a->valid_until = now - 1;
				break;

			case DHCPV6_MSG_DECLINE:
				/* DECLINE only applies to non-temporary addresses */
				if (!(a->ia.flags & DHCPV6_IA_NA))
					break;

				a->bound = false;

				if (a->lease_cfg &&
				    a->lease_cfg->hostid == a->ia.assigned_host_id) {
					/* Static lease: release immediately */
					a->valid_until = now - 1;
				} else {
					/* Dynamic lease: block address for 1 hour */
					memset(a->duid, 0, a->duid_len);
					a->valid_until = now + 3600;
				}
				break;
			}

			break;
		}

		case DHCPV6_MSG_CONFIRM:
			if (ia_addr_present && !dhcpv6_ia_on_link(ia, a, iface)) {
				notonlink = true;
				break;
			}

			if (!ia_addr_present || !a || !a->bound) {
				response_len = 0;
				goto out;
			}
			break;

		default:
			break;
		}

		if (hdr->msg_type == DHCPV6_MSG_REBIND && a) {
			ia_response_len = build_ia(buf, buflen, status, ia, a, iface, false);
			a->bound = true;
			apply_lease(a, true);
		}

		buf += ia_response_len;
		buflen -= ia_response_len;
		response_len += ia_response_len;
		dhcpv6_log(hdr->msg_type, iface, now, duidbuf, (req.flags & DHCPV6_IA_PD), a, status);
	} /* end dhcpv6_for_each_option */

	switch (hdr->msg_type) {
	case DHCPV6_MSG_RELEASE:
	case DHCPV6_MSG_DECLINE:
	case DHCPV6_MSG_CONFIRM:
		if (response_len + 6 < buflen) {
			buf[0] = 0;
			buf[1] = DHCPV6_OPT_STATUS;
			buf[2] = 0;
			buf[3] = 2;
			buf[4] = 0;
			buf[5] = (notonlink) ? DHCPV6_STATUS_NOTONLINK : DHCPV6_STATUS_OK;
			response_len += 6;
		}
		break;

	default:
		break;
	}

	statefiles_write();

out:
	return response_len;
}
