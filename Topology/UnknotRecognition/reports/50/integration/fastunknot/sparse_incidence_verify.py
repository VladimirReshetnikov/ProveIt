"""Independent verification of sparse interval-incidence and parity certificates.

Does not import sparse_incidence, _sparse_coverage, or interval_orbits.
Only the independently implemented native orbit-trace verifier is reused.
The nonnegative measure promise comes from the supplied equivalence relation;
it is not guessed from a finite list of untrusted function values.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
import re
from .interval_orbit_verify import verify_orbit_certificate


class _Invalid(ValueError):
    pass


def _int(x):
    if type(x) is int:
        return x
    if isinstance(x, str) and re.fullmatch(r'[+-]?0[xX][0-9a-fA-F]+', x):
        return int(x, 16)
    raise _Invalid('not an integer')


def _union(values):
    out = []
    for left, right in sorted(values):
        if left == right:
            continue
        if out and left <= out[-1][1]:
            if right > out[-1][1]:
                out[-1] = (out[-1][0], right)
        else:
            out.append((left, right))
    return tuple(out)


def _ports(size, ports, poll):
    if not isinstance(ports, (list, tuple)):
        raise _Invalid('ports not a sequence')
    out = []
    for port in ports:
        poll()
        if not isinstance(port, (list, tuple)):
            raise _Invalid('port not a sequence')
        intervals = []
        for pair in port:
            poll()
            if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                raise _Invalid('bad marked interval')
            a, b = map(_int, pair)
            if not 0 <= a <= b <= size:
                raise _Invalid('mark outside universe')
            intervals.append((a, b))
        out.append(_union(intervals))
    return tuple(out)


def _mask(raw, full):
    x = _int(raw)
    if not 0 <= x <= full:
        raise _Invalid('mask outside port set')
    return x


class _Counts:
    def __init__(self, size, pairs, ports, bundle, poll):
        if not isinstance(bundle, dict):
            raise _Invalid('missing count bundle')
        proof = bundle.get('base')
        if not verify_orbit_certificate(size, pairs, proof, check=poll):
            raise _Invalid('invalid baseline count')
        self.total = _int(proof['orbit_count'])
        self.ports, self.poll = ports, poll
        records = bundle.get('unions')
        if not isinstance(records, list):
            raise _Invalid('missing union proofs')
        self.values = {}
        self.used = set()
        for item in records:
            poll()
            if not isinstance(item, dict):
                raise _Invalid('invalid union record')
            intervals = item.get('intervals')
            canonical = _ports(size, [intervals], poll)[0]
            if not canonical:
                raise _Invalid('empty union must use baseline')
            decoded = tuple(tuple(map(_int, pair)) for pair in intervals)
            if decoded != canonical or canonical in self.values:
                raise _Invalid('union is noncanonical or duplicated')
            # Independently construct the contraction-to-one-class relations.
            anchor = canonical[0][0]
            rows = list(pairs)
            for left, right in canonical:
                poll()
                if right - left >= 2:
                    rows.append([left, right - 2, left + 1, right - 1, 1])
                if left != anchor:
                    rows.append([anchor, anchor, left, left, 1])
            cp = item.get('proof')
            if not verify_orbit_certificate(size, rows, cp, check=poll):
                raise _Invalid('invalid coned count')
            value = _int(cp['orbit_count']) - 1
            if not 0 <= value <= self.total:
                raise _Invalid('impossible subset sum')
            self.values[canonical] = value

    def query(self, mask):
        pieces = []
        for bit, port in enumerate(self.ports):
            self.poll()
            if not ((mask >> bit) & 1):
                pieces.extend(port)
        union = _union(pieces)
        if not union:
            return self.total
        if union not in self.values:
            raise _Invalid('missing union proof')
        self.used.add(union)
        return self.values[union]

    def finish(self):
        if self.used != set(self.values):
            raise _Invalid('unused union proof')


def _base(size, pairs, ports, cert, poll):
    size = _int(size)
    if size < 0 or not isinstance(pairs, (list, tuple)):
        raise _Invalid('invalid interval input')
    ports = _ports(size, ports, poll)
    if (not isinstance(cert, dict) or _int(cert.get('version')) != 1
            or cert.get('kind') != 'sparse-interval-incidence'):
        raise _Invalid('unknown sparse certificate')
    if _int(cert.get('size')) != size or _ports(size, cert.get('ports'), poll) != ports:
        raise _Invalid('input binding differs')
    counts = _Counts(size, pairs, ports, cert.get('counts'), poll)
    if _int(cert.get('orbit_count')) != counts.total:
        raise _Invalid('total differs from baseline')
    entries = cert.get('entries')
    if not isinstance(entries, list):
        raise _Invalid('missing atoms')
    full = (1 << len(ports)) - 1
    known = []
    seen = set()

    def previous(mask):
        value = 0
        for old, weight in known:
            poll()
            if old & mask == old:
                value += weight
        return value

    for entry in entries:
        poll()
        if not isinstance(entry, dict):
            raise _Invalid('invalid atom')
        support = _mask(entry.get('mask'), full)
        weight = _int(entry.get('weight'))
        if support in seen or weight <= 0:
            raise _Invalid('duplicate or nonpositive atom')
        zeros = entry.get('zeros')
        if not isinstance(zeros, list) or len(zeros) != support.bit_count():
            raise _Invalid('one zero witness is needed for every retained port')
        witnessed = 0
        for item in zeros:
            poll()
            if not isinstance(item, (list, tuple)) or len(item) != 2:
                raise _Invalid('invalid zero witness')
            bit, z = _int(item[0]), _mask(item[1], full)
            if not 0 <= bit < len(ports):
                raise _Invalid('invalid witness port')
            b = 1 << bit
            if not support & b or witnessed & b or z & b:
                raise _Invalid('zero witness does not exclude its port')
            if (support ^ b) & z != (support ^ b):
                raise _Invalid('zero witness fails to contain the remaining support')
            if counts.query(z) != previous(z):
                raise _Invalid('nonzero residual in a zero witness')
            witnessed |= b
        if witnessed != support:
            raise _Invalid('missing exclusion witness')
        if counts.query(support) - previous(support) != weight:
            raise _Invalid('wrong atom weight')
        seen.add(support)
        known.append([support, weight])
    if sum(w for _, w in known) != counts.total:
        raise _Invalid('unaccounted residual mass')
    counts.finish()
    return known, ports


def verify_sparse_port_incidence_certificate(size, pairings, ports, certificate, *, check=None):
    """Check complete sparse data without the producer or a subset-cube scan.

    Malformed mathematical data returns False. Cooperative callback exceptions
    propagate. Hostile serialized size should be limited by the caller.
    """
    poll = check or (lambda: None)
    try:
        poll()
        _base(size, pairings, ports, certificate, poll)
        return True
    except _Invalid:
        return False


def verify_sparse_signed_incidence_certificate(size, signed_pairings, ports,
                                                certificate, *, check=None):
    """Independently construct the parity double and verify its known support."""
    poll = check or (lambda: None)
    try:
        poll()
        size = _int(size)
        if size < 0 or not isinstance(signed_pairings, (list, tuple)):
            raise _Invalid('invalid signed input')
        base_rows, cover_rows = [], []
        for signed in signed_pairings:
            poll()
            if not hasattr(signed, 'pairing') or not hasattr(signed, 'parity'):
                raise _Invalid('signed pairing missing')
            parity = _int(signed.parity)
            if parity not in (0, 1):
                raise _Invalid('invalid parity')
            p = signed.pairing
            if not all(hasattr(p, x) for x in ('a', 'b', 'c', 'd', 'reverse')):
                raise _Invalid('invalid pairing object')
            if type(p.reverse) is not bool:
                raise _Invalid('invalid reversal flag')
            a, b, c, d = (_int(getattr(p, key)) for key in ('a', 'b', 'c', 'd'))
            sign = -1 if p.reverse else 1
            base_rows.append([a, b, c, d, sign])
            for sheet in range(2):
                other = sheet ^ parity
                cover_rows.append([a + sheet * size, b + sheet * size,
                                   c + other * size, d + other * size, sign])
        cert = certificate
        if (not isinstance(cert, dict) or _int(cert.get('version')) != 1
                or cert.get('kind') != 'sparse-signed-incidence'):
            raise _Invalid('unknown signed certificate')
        known, ports = _base(size, base_rows, ports, cert.get('base'), poll)
        lifted_ports = tuple(_union(list(p) + [(a + size, b + size) for a, b in p])
                             for p in ports)
        counts = _Counts(2 * size, cover_rows, lifted_ports, cert.get('cover'), poll)
        reported, split = cert.get('cover_histogram'), cert.get('signed_histogram')
        if (not isinstance(reported, list) or not isinstance(split, list)
                or len(reported) != len(known) or len(split) != len(known)):
            raise _Invalid('invalid signed histogram shape')
        lifted = []
        for (mask, count), row, srow in zip(known, reported, split):
            poll()
            if (not isinstance(row, (list, tuple)) or len(row) != 2
                    or not isinstance(srow, (list, tuple)) or len(srow) != 3):
                raise _Invalid('invalid signed row')
            claimed_mask, weight = map(_int, row)
            ss = list(map(_int, srow))
            if claimed_mask != mask or not count <= weight <= 2 * count:
                raise _Invalid('bad lifted multiplicity')
            expected = counts.query(mask)
            for old_mask, old_weight in lifted:
                poll()
                if old_mask & mask == old_mask:
                    expected -= old_weight
            if expected != weight or ss != [mask, weight - count, 2 * count - weight]:
                raise _Invalid('incorrect parity split')
            lifted.append([mask, weight])
        if sum(w for _, w in lifted) != counts.total:
            raise _Invalid('lifted total differs')
        counts.finish()
        return True
    except _Invalid:
        return False
