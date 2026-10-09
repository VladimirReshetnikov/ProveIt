"""Opt-in adapter for ProveIt's maintained, independently replayable AHT kernel.

Run with Topology/UnknotRecognition/fast on PYTHONPATH. This module does not
change recognize dispatch. The historical source/API hashes are in provenance.
"""
from __future__ import annotations
from .core import (ResourceLimit, recover, certificate_payload,
                   certificate_queries, verify_payload, natural)
from .intervals import (IntervalOracle, prepare_ports, selected_union, cone_rows)


def analyze_port_incidence_sparse(size, pairings, ports, *, max_entries=None,
                                   max_calls=None, max_cycles=None,
                                   record_certificate=False, check=None):
    from fastunknot.interval_orbits import IntervalPairing, count_orbits
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    for cap in (max_calls, max_cycles, max_entries):
        if cap is not None:
            natural(cap, 'allowance')
    poll = check or (lambda: None)
    canonical = prepare_ports(size, ports)
    pairs = list(pairings)
    stats = {'orbit_queries': 0, 'orbit_cycles': 0, 'certificate_queries': 0}

    def count(extra, record=False):
        poll()
        if max_calls is not None and stats['orbit_queries'] >= max_calls:
            raise ResourceLimit('shared orbit-query allowance exhausted')
        remaining = None if max_cycles is None else max_cycles-stats['orbit_cycles']
        added = [IntervalPairing(a,b,c,d,sign == -1) for a,b,c,d,sign in extra]
        reply = count_orbits(size, pairs+added, max_cycles=remaining,
                              check=poll, record_certificate=record)
        stats['orbit_queries'] += 1
        stats['orbit_cycles'] += reply.cycles
        stats['certificate_queries'] += int(record)
        if not reply.complete:
            raise ResourceLimit('shared AHT-cycle allowance exhausted')
        return reply

    try:
        oracle = IntervalOracle(size, canonical,
                                lambda extra: count(extra).orbits, check=poll)
        found = recover(len(canonical), oracle.total, oracle,
                        max_entries=max_entries, check=poll)
        stats.update(support_size=len(found.entries),
                     zeta_requests=found.oracle_requests,
                     union_cache_hits=oracle.cache_hits)
        result = {'status':'COMPLETE', 'orbit_count':found.total,
                  'histogram_encoding':'sparse-mask-multiplicity-pairs',
                  'histogram':[list(item) for item in found.entries], 'stats':stats}
        if record_certificate:
            # A second pass retains only the proofs required for verification.
            base = count([], True)
            if base.orbits != found.total:
                raise ArithmeticError('baseline changed during certificate pass')
            proofs, indices, physical = [], [], {}
            full = (1 << found.r)-1
            for u in certificate_queries(found):
                poll()
                union = selected_union(canonical, full ^ u)
                if not union:
                    indices.append([u, None]); continue
                if union not in physical:
                    reply = count(cone_rows(union), True)
                    physical[union] = len(proofs)
                    proofs.append(reply.certificate)
                indices.append([u, physical[union]])
            result['certificate'] = {
                'version':1, 'size':size, 'ports':canonical,
                'payload':certificate_payload(found), 'base':base.certificate,
                'proofs':proofs, 'query_indices':indices}
        poll()
        return result
    except ResourceLimit as exc:
        return {'status':'INCONCLUSIVE', 'reason':str(exc), 'stats':stats}


def verify_sparse_port_incidence_certificate(size, pairings, ports, cert, *,
                                              check=None):
    """No orbit producer/recovery calls; validate all proof/source bindings."""
    from fastunknot.interval_orbit_verify import verify_orbit_certificate
    poll = check or (lambda: None)
    try:
        poll(); canonical = prepare_ports(size, ports)
        if not isinstance(cert, dict) or set(cert) != {
                'version','size','ports','payload','base','proofs','query_indices'}:
            return False
        if (type(cert['version']) is not int or cert['version'] != 1
                or natural(cert['size']) != size
                or prepare_ports(size, cert['ports']) != canonical):
            return False
        if not verify_orbit_certificate(size, pairings, cert['base'], check=poll):
            return False
        total = natural(cert['base']['orbit_count'])
        if not isinstance(cert['proofs'], list) or not isinstance(cert['query_indices'], list):
            return False
        table = {}
        r, full = len(canonical), (1 << len(canonical))-1
        for item in cert['query_indices']:
            poll()
            if not isinstance(item, (list,tuple)) or len(item) != 2:
                return False
            u, index = item
            natural(u, 'query mask')
            if u > full or u in table:
                return False
            if index is not None:
                natural(index, 'proof index')
                if index >= len(cert['proofs']):
                    return False
            table[u] = index
        used_queries, used_proofs, union_proofs, values = set(), {}, {}, {}

        def authenticated(u):
            poll()
            if u not in table:
                raise ValueError('missing verification query')
            used_queries.add(u)
            union = selected_union(canonical, full ^ u)
            index = table[u]
            if not union:
                if index is not None:
                    raise ValueError('empty union has no auxiliary proof')
                return total
            if index is None:
                raise ValueError('nonempty union needs a count proof')
            if index in used_proofs and used_proofs[index] != union:
                raise ValueError('proof rebound to a different physical union')
            if union in union_proofs and union_proofs[union] != index:
                raise ValueError('duplicate physical-union proof')
            if union not in values:
                proof = cert['proofs'][index]
                if not verify_orbit_certificate(size, list(pairings)+cone_rows(union),
                                                proof, check=poll):
                    raise ValueError('invalid orbit proof')
                value = natural(proof['orbit_count']) - 1
                if not 0 <= value <= total:
                    raise ValueError('coning identity failed')
                values[union] = value
                used_proofs[index] = union
                union_proofs[union] = index
            return values[union]

        valid = verify_payload(r, total, cert['payload'], authenticated, check=poll)
        return (valid and used_queries == set(table)
                and set(used_proofs) == set(range(len(cert['proofs']))))
    except (ValueError, KeyError, TypeError, IndexError):
        return False
