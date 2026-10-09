"""Sparse, proof-carrying port incidence over the existing AHT orbit kernel.

These APIs produce assertions about supplied interval relations, NOT knot
verdicts. They do not modify ordinary recognition dispatch. Optional limits
are shared across all counts; interrupted results contain no histogram/proof.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from ._sparse_coverage import WorkLimit, integer, recover_nonnegative, validate_options
from .interval_orbits import IntervalPairing, SignedPairing, count_orbits, signed_cover


def _union(intervals):
    out = []
    for lo, hi in sorted(intervals):
        if lo == hi:
            continue
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(hi, out[-1][1]))
        else:
            out.append((lo, hi))
    return tuple(out)


def _prepare(size, pairings, ports, max_ports, poll):
    size = integer(size)
    if size < 0 or not isinstance(ports, (list, tuple)):
        raise ValueError('invalid universe or port list')
    if max_ports is not None and (type(max_ports) is not int or max_ports < 0):
        raise ValueError('max_ports must be nonnegative or None')
    if max_ports is not None and len(ports) > max_ports:
        raise ValueError('port allowance exceeded')
    pairs = list(pairings)
    for p in pairs:
        poll()
        if not isinstance(p, IntervalPairing) or p.d >= size:
            raise ValueError('invalid interval pairing')
    result = []
    for port in ports:
        poll()
        if not isinstance(port, (list, tuple)):
            raise ValueError('each port must be an explicit interval union')
        values = []
        for item in port:
            poll()
            if not isinstance(item, (list, tuple)) or len(item) != 2:
                raise ValueError('an interval needs two endpoints')
            lo, hi = map(integer, item)
            if not 0 <= lo <= hi <= size:
                raise ValueError('mark outside universe')
            values.append((lo, hi))
        result.append(_union(values))
    return size, pairs, tuple(result)


class _Budget:
    def __init__(self, max_cycles, max_queries, check, record):
        for value in (max_cycles, max_queries):
            if value is not None and (type(value) is not int or value < 0):
                raise ValueError('limits must be nonnegative integers or None')
        if type(record) is not bool:
            raise ValueError('record_certificate must be bool')
        self.max_cycles, self.max_queries = max_cycles, max_queries
        self.poll = check if check is not None else (lambda: None)
        self.record = record
        self.stats = dict(orbit_queries=0, orbit_cycles=0, union_cache_hits=0,
                          empty_union_queries=0)

    def count(self, size, pairings):
        self.poll()
        if self.max_queries is not None and self.stats['orbit_queries'] >= self.max_queries:
            raise WorkLimit('orbit-query allowance exhausted')
        remaining = (None if self.max_cycles is None else
                     self.max_cycles - self.stats['orbit_cycles'])
        result = count_orbits(size, pairings, max_cycles=remaining,
                              check=self.poll, record_certificate=self.record)
        self.stats['orbit_queries'] += 1
        self.stats['orbit_cycles'] += result.cycles
        if not result.complete:
            raise WorkLimit('orbit-cycle allowance exhausted')
        return result


class _ConedOracle:
    def __init__(self, size, pairs, ports, budget):
        self.size, self.pairs, self.ports, self.budget = size, pairs, ports, budget
        self.full = (1 << len(ports)) - 1
        self.base = budget.count(size, pairs)
        self.cache = {}
        self.mask_unions = {}

    def selected_complement(self, mask):
        if mask not in self.mask_unions:
            values = []
            for i, port in enumerate(self.ports):
                self.budget.poll()
                if not (mask >> i) & 1:
                    values.extend(port)
            self.mask_unions[mask] = _union(values)
        return self.mask_unions[mask]

    def query(self, mask):
        self.budget.poll()
        union = self.selected_complement(mask)
        if not union:
            self.budget.stats['empty_union_queries'] += 1
            return self.base.orbits
        if union in self.cache:
            self.budget.stats['union_cache_hits'] += 1
        else:
            hub = union[0][0]
            extra = []
            for lo, hi in union:
                self.budget.poll()
                if hi - lo > 1:
                    extra.append(IntervalPairing(lo, hi - 2, lo + 1, hi - 1))
                if lo != hub:
                    extra.append(IntervalPairing(hub, hub, lo, lo))
            self.cache[union] = self.budget.count(self.size, self.pairs + extra)
        value = self.cache[union].orbits - 1
        if not 0 <= value <= self.base.orbits:
            raise ArithmeticError('invalid coned subset sum')
        return value

    def bundle(self, masks):
        """Keep only the proofs used by the compressed minimality witnesses."""
        used = set()
        for mask in masks:
            self.budget.poll()
            union = self.selected_complement(mask)
            if union:
                # Normally already queried, but this also covers future callers.
                if union not in self.cache:
                    self.query(mask)
                used.add(union)
        return dict(base=self.base.certificate,
                    unions=[dict(intervals=union, proof=self.cache[union].certificate)
                            for union in sorted(used)])


def _recover(size, pairs, ports, budget, strategy, max_signatures):
    oracle = _ConedOracle(size, pairs, ports, budget)
    answer = recover_nonnegative(len(ports), oracle.base.orbits, oracle.query,
                                 strategy=strategy, max_signatures=max_signatures,
                                 check=budget.poll)
    cert = None
    if budget.record:
        cert = dict(version=1, kind='sparse-interval-incidence', size=size,
                    ports=ports, orbit_count=oracle.base.orbits,
                    entries=answer['entries'], counts=oracle.bundle(answer['needed']))
    return oracle, answer, cert


def analyze_sparse_port_incidence(size, pairings, ports, *, strategy='linear',
                                  max_ports=None, max_signatures=None,
                                  max_cycles=None, max_queries=None,
                                  record_certificate=False, check=None):
    """Return a sparse list [signature_bitmask, positive_component_count].

    No array of length 2**r is allocated. ``linear`` is the conservative default;
    ``split`` often reduces queries for low-cardinality signatures. Unmarked
    components have mask zero. Certificates bind the exact input interval
    system and can be checked without invoking any count producer.
    """
    validate_options(strategy, max_signatures)
    budget = _Budget(max_cycles, max_queries, check, record_certificate)
    size, pairs, ports = _prepare(size, pairings, ports, max_ports, budget.poll)
    try:
        oracle, answer, cert = _recover(size, pairs, ports, budget, strategy, max_signatures)
        result = dict(status='COMPLETE', orbit_count=oracle.base.orbits,
                      histogram=[[e['mask'], e['weight']] for e in answer['entries']],
                      stats={**budget.stats, **answer['stats']})
        if record_certificate:
            result['certificate'] = cert
        budget.poll()
        return result
    except WorkLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=dict(budget.stats))


def analyze_sparse_signed_incidence(size, signed_pairings, ports, *,
                                    strategy='linear', max_ports=None,
                                    max_signatures=None, max_cycles=None,
                                    max_queries=None, record_certificate=False,
                                    check=None):
    """Split each incidence class by parity consistency using one support search.

    Output rows are [mask, consistent_components, inconsistent_components].
    'Consistent' means every closed relation walk has parity zero. It means
    orientable only when the supplied parity is the surface orientation character.
    The lifted support equals the base support. Each lifted weight needs at most
    one coned count, rather than a second support search.
    """
    validate_options(strategy, max_signatures)
    budget = _Budget(max_cycles, max_queries, check, record_certificate)
    signed = list(signed_pairings)
    if any(not isinstance(p, SignedPairing) for p in signed):
        raise ValueError('signed_pairings must contain SignedPairing objects')
    size, pairs, ports = _prepare(size, [s.pairing for s in signed], ports,
                                  max_ports, budget.poll)
    try:
        base, answer, base_cert = _recover(size, pairs, ports, budget, strategy, max_signatures)
        before = budget.stats['orbit_queries']
        lifted = signed_cover(size, signed)
        lifted_ports = tuple(_union(list(port) + [(a + size, b + size) for a, b in port])
                             for port in ports)
        cover = _ConedOracle(2 * size, lifted, lifted_ports, budget)
        cover_rows, rows = [], []
        for entry in answer['entries']:
            budget.poll()
            mask, count = entry['mask'], entry['weight']
            weight = cover.query(mask)
            for old_mask, old_weight in cover_rows:
                budget.poll()
                if old_mask & mask == old_mask:
                    weight -= old_weight
            if not count <= weight <= 2 * count:
                raise ArithmeticError('invalid parity-cover multiplicity')
            cover_rows.append([mask, weight])
            rows.append([mask, weight - count, 2 * count - weight])
        if sum(w for _, w in cover_rows) != cover.base.orbits:
            raise ArithmeticError('lifted total mass mismatch')
        result = dict(status='COMPLETE', orbit_count=base.base.orbits,
                      histogram=[[e['mask'], e['weight']] for e in answer['entries']],
                      signed_histogram=rows,
                      stats={**budget.stats, **answer['stats'],
                             'cover_orbit_queries': budget.stats['orbit_queries'] - before})
        if record_certificate:
            masks = {e['mask'] for e in answer['entries']}
            result['certificate'] = dict(version=1, kind='sparse-signed-incidence',
                base=base_cert, cover=cover.bundle(masks), cover_histogram=cover_rows,
                signed_histogram=rows)
        budget.poll()
        return result
    except WorkLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=dict(budget.stats))
