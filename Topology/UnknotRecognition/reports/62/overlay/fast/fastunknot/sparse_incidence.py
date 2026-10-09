"""Sparse marked-orbit incidence through the maintained unweighted AHT kernel.

This is an aggregate interval-relation primitive, NOT an unknot recognizer.
No 2**r array is created. Incomplete runs publish neither histogram nor proof.
All distinct coned queries and the baseline share both work allowances.
"""
from .interval_orbits import IntervalPairing, count_orbits
from .sparse_incidence_common import (allowance, prepare, selected_union,
                                     cone_rows, pairing_rows)
from .sparse_zeta import recover_nonnegative_zeta, RecoveryLimit


def analyze_sparse_port_incidence(size, pairings, ports, *, max_ports=None,
                                   max_terms=None, max_cycles=None,
                                   max_orbit_queries=None,
                                   record_certificate=False, check=None):
    """Return positive [mask,count] pairs for exact component signatures.

    Pairings accept native IntervalPairing objects or inclusive [a,b,c,d,sign]
    rows; ports are unions of half-open intervals. Bit i denotes port i.
    COMPLETE includes the unmarked term (mask 0) exactly when it is positive.
    Optional sparse-incidence-v1 certificates reuse existing orbit traces.
    Limits are explicit work controls, not assertions about geometric inputs.
    """
    poll = check if check is not None else lambda: None
    poll()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    for name, limit in [('max_cycles', max_cycles), ('max_terms', max_terms),
                        ('max_orbit_queries', max_orbit_queries)]:
        allowance(limit, name)
    size, ports = prepare(size, ports, max_ports, poll)
    rows = pairing_rows(size, pairings, poll)
    pairs = [IntervalPairing(a, b, c, d, sign == -1) for a, b, c, d, sign in rows]
    full = (1 << len(ports)) - 1
    stats = dict(orbit_queries=0, orbit_cycles=0, union_cache_hits=0,
                 empty_unions=0, logical_zeta_queries=0)
    cache, proofs = {}, []

    def count(extra):
        poll()
        if (max_orbit_queries is not None
                and stats['orbit_queries'] >= max_orbit_queries):
            raise RecoveryLimit('orbit-query allowance exhausted')
        remaining = None if max_cycles is None else max_cycles - stats['orbit_cycles']
        reply = count_orbits(size, pairs + extra, max_cycles=remaining,
                              record_certificate=record_certificate, check=poll)
        stats['orbit_queries'] += 1
        stats['orbit_cycles'] += reply.cycles
        if not reply.complete:
            raise RecoveryLimit('total orbit-cycle allowance exhausted')
        return reply

    try:
        base = count([])

        def zeta(allowed):
            stats['logical_zeta_queries'] += 1
            marked = selected_union(ports, full ^ allowed, poll)
            if not marked:
                stats['empty_unions'] += 1
                return base.orbits, None
            if marked in cache:
                stats['union_cache_hits'] += 1
                return cache[marked]
            extra = [IntervalPairing(a, b, c, d, sign == -1)
                     for a, b, c, d, sign in cone_rows(marked)]
            reply = count(extra)
            value = reply.orbits - 1
            if not 0 <= value <= base.orbits:
                raise ArithmeticError('coned orbit count violates the zeta identity')
            ref = len(proofs) if record_certificate else None
            if record_certificate:
                proofs.append(dict(union=marked, trace=reply.certificate))
            cache[marked] = value, ref
            return value, ref

        terms, steps, recovery = recover_nonnegative_zeta(
            len(ports), base.orbits, zeta, max_terms=max_terms,
            record_witness=record_certificate, check=poll)
    except RecoveryLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)

    stats.update(recovery)
    histogram = [list(term) for term in sorted(terms)]
    result = dict(status='COMPLETE', orbit_count=base.orbits,
                  histogram=histogram, stats=stats)
    if record_certificate:
        # Intermediate positive search queries are unnecessary in the proof.
        used = set()
        for step in steps:
            poll()
            if step['support_ref'] is not None:
                used.add(step['support_ref'])
            used.update(row[2] for row in step['zeros'] if row[2] is not None)
        ordered = sorted(used)
        remap = {old: new for new, old in enumerate(ordered)}
        for step in steps:
            poll()
            if step['support_ref'] is not None:
                step['support_ref'] = remap[step['support_ref']]
            for row in step['zeros']:
                if row[2] is not None:
                    row[2] = remap[row[2]]
        retained = [proofs[index] for index in ordered]
        result['certificate'] = dict(
            format='sparse-incidence-v1', size=size, ports=ports,
            orbit_count=base.orbits, histogram=histogram,
            base=base.certificate, proofs=retained, steps=steps)
        stats['retained_union_proofs'] = len(retained)
    poll()
    return result
