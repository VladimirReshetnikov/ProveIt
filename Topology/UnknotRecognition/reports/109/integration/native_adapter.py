"""Additive adapter for already authenticated native occurrence dictionaries.

This module does NOT authenticate handle charts, consume a knot diagram, or
return a topological verdict. A residual row is retained, never discarded.
"""
from ordered_kernel import optimize_counts, verify_plan, transport_counts


def optimize_retained_occurrences(counts, weights=None, **options):
    plan=optimize_counts(counts,weights,**options)
    if plan['status']!='OPTIMAL_MATRIX_PLAN':
        return {'status':'INCONCLUSIVE','matrix_result':plan}
    if not verify_plan(counts,plan,weights):
        raise ArithmeticError('independent matrix replay failed')
    residual=transport_counts(counts,plan,weights=weights,saturated=True)
    return {'status':'PARTIAL_MATRIX_KERNEL', 'matrix_result':plan,
            'retained_two_handle_ids':plan['deferred_rows'],
            'saturated_retained_occurrences':residual,
            'obligation':'retain source-bound ordered attaching charts and all unpivoted one-handles'}
