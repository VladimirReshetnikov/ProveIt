"""Additive research adapter for the inspected native core dictionary shape.

Caller must independently authenticate source charts. This adapter neither
executes geometric cancellation nor returns a knot/handlebody certificate.
"""
from __future__ import annotations
from collections.abc import Mapping
from cycleblocks import optimize_counts, deferred_forest, Limits


def propose_core_plan(core: Mapping, weights=None, *, limits=Limits(), check=lambda: None):
    """Read every raw one-handle occurrence, optimize, and defer the forest.

    Unlike native saturated occurrence extraction, this keeps 3 distinct from 2
    so graph-cycle parity is meaningful. Source handles not occurring in any
    row remain in the complete graph and in the final forest search.
    """
    if not isinstance(core, Mapping): raise ValueError('core must be a mapping')
    zero, one, two = core['handles0'], core['handles1'], core['handles2']
    if any(type(x) is not list for x in [zero, one, two]):
        raise ValueError('core inventories must be lists')
    edges = {}
    for handle in one:
        check()
        label = handle['id']
        if type(label) is not int or label < 0 or label in edges:
            raise ValueError('bad or repeated one-handle label')
        edges[label] = handle['ends']
    counts = {}
    for handle in two:
        check()
        label = handle['id']
        if type(label) is not int or label < 0 or label in counts:
            raise ValueError('bad or repeated two-handle label')
        row = {}
        if type(handle['cycle']) is not list: raise ValueError('cycle must be a list')
        for flag in handle['cycle']:
            check()
            if type(flag['dimension']) is not int or flag['dimension'] not in (0, 1):
                raise ValueError('unsupported attaching-cycle flag dimension')
            if flag['dimension'] == 1:
                c = flag['handle']
                if type(c) is not int or c not in edges:
                    raise ValueError('flag references an absent source one-handle')
                row[c] = row.get(c, 0) + 1
        counts[label] = row
    plan = optimize_counts(counts, weights, limits=limits, check=check)
    if plan['status'] != 'OPTIMAL_MATRIX_PLAN':
        return dict(status='INCONCLUSIVE', matrix_result=plan,
                    source_geometry_authenticated=False)
    forest = deferred_forest(len(zero), edges, counts, plan, weights=weights)
    return dict(status='MATRIX_PLAN_NOT_GEOMETRY', matrix_result=plan,
                deferred_forest=forest, counts=counts,
                source_geometry_authenticated=False,
                geometric_cancellation_executed=False)
