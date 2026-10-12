"""Opt-in integration seam for ProveIt at c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5.

No monkey patch and no global default change. Native imports occur only in
propose_geometry(). The surrounding source-parallelity proof must already be
authenticated. A successful return still needs the ordinary downstream core,
bundle-port, boundary-pattern, and whole-cut checks.
"""
from __future__ import annotations
from copy import deepcopy
from dualforest import make_instance, solve, verify_positive


def from_native_records(counts, three_handle_ids, records):
    ids = list(three_handle_ids)
    if len(set(ids)) != len(ids) or any(type(x) is not int or x < 0 for x in ids):
        raise ValueError('invalid three-handle IDs')
    ids.sort()
    vertex = {h: i+1 for i, h in enumerate(ids)}
    vertex[None] = 0
    m = len(records)
    if set(counts) != set(range(m)) or any(type(r) is not int for r in counts):
        raise ValueError('native two-handle IDs must be the contiguous row range')
    edges = [None] * m
    for rec in records:
        if type(rec) is not dict or set(rec) != {'two_handle', 'ends'}:
            raise ValueError('malformed native endpoint record')
        r, pair = rec['two_handle'], rec['ends']
        if type(r) is not int or not 0 <= r < m or edges[r] is not None or len(pair) != 2:
            raise ValueError('invalid two-handle endpoint record')
        if any(x is not None and (type(x) is not int or x not in vertex) for x in pair):
            raise ValueError('unknown three-handle endpoint')
        edges[r] = tuple(vertex[x] for x in pair)
    return make_instance(len(ids)+1, edges, [counts[r] for r in range(m)]), ids


def native_proposal(inst, certificate, records, three_handle_ids):
    """Translate a verified matrix proposal, without pretending to source-replay it."""
    if inst.root != 0:
        raise ValueError('native proposal requires boundary root normalized to zero')
    if not verify_positive(inst, certificate):
        raise ValueError('local positive certificate failed')
    ids = sorted(three_handle_ids)
    if len(ids) + 1 != inst.vertices:
        raise ValueError('inconsistent vertex map')
    return dict(schema='core-three-handle-reduction-v1',
                dual_endpoints=deepcopy(records),
                cancellations=[dict(two_handle=r, three_handle=ids[v-1])
                               for r, v in certificate['dual_cancellations']],
                surviving_two_handles=[r for r in range(inst.m)
                                       if r not in set(certificate['tree'])])


def propose_geometry(geometry, *, max_branches=10000, check=lambda: None):
    """Produce and native-source-replay a proposed replacement dual forest.

    Return status 'local-yes' only with source-replayed reduced geometry.
    'local-no' is NOT a non-handlebody or knottedness verdict. Exceptions from
    the caller's resource callback propagate; they are never treated as 'no'.

    This native end-to-end adapter has not been executed in the delivered
    environment. The record-level translation has its own executed tests.
    """
    from fastunknot.core_handlebody import _forest, _occurrences
    from fastunknot.core_three_handle_reduction import reduce_core_three_handles
    from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles

    check()
    baseline = reduce_core_three_handles(geometry, check=check)
    if baseline is None:
        return dict(status='unknown', reason='native dual endpoint construction stalled')
    _, baseline_proof = baseline
    if replay_core_three_handles(geometry, baseline_proof, check=check) is None:
        return dict(status='unknown', reason='native endpoint authentication failed')
    primal_tree, _ = _forest(geometry['core'], check)
    counts = _occurrences(geometry['core'], primal_tree, check)
    ids = [h['id'] for h in geometry['core']['handles3']]
    inst, ids = from_native_records(counts, ids, baseline_proof['dual_endpoints'])
    answer = solve(inst, max_branches=max_branches, check=check)
    if answer['status'] != 'yes':
        return dict(status='local-no' if answer['status'] == 'no' else 'unknown',
                    result=answer, primal_forest=primal_tree)
    proposal = native_proposal(inst, answer['certificate'], baseline_proof['dual_endpoints'], ids)
    check()
    reduced = replay_core_three_handles(geometry, proposal, check=check)
    if reduced is None:
        return dict(status='unknown', reason='native replay rejected proposed forest')
    check()
    return dict(status='local-yes', reduced_geometry=reduced,
                native_dual_proof=proposal, local_result=answer,
                primal_forest=primal_tree,
                obligation='Run all normal downstream core, port, and whole-cut verifiers.')
