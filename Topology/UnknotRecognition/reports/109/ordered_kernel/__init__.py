"""Opt-in exact matrix kernels. No function returns a knot verdict."""
from .dp import ordered_plan, Limits
from .two_incidence import two_incidence_plan, verify_two_incidence_optimality
from .certificates import verify_plan, transport_counts, peeling_plan, package_plan, verify_weighted_stopping_optimality
from .decomposition import Decomposition, elimination_decomposition
from .model import Matrix, noop


def optimize_counts(counts, weights=None, decomposition=None, *, method='auto',
                    limits=None, check=noop):
    matrix = Matrix.parse(counts, weights)
    if method not in ('auto', 'ordered', 'two-incidence'):
        raise ValueError('unknown optimization method')
    if method == 'auto':
        prefix, remaining = peeling_plan(matrix, [], check=check)
        if not remaining:
            return package_plan(matrix, [], method='full-private-peeling', stats={}, check=check)
        if len(remaining) < len(matrix.rows) and decomposition is None:
            # A full-matrix private prefix is safe for every nonnegative-weight
            # optimum. Provided decompositions retain their original indexing;
            # automatic decomposition construction may instead use the core.
            sub={r:matrix.entries[r] for r in remaining}
            subweights={r:matrix.weights[r] for r in remaining}
            small=optimize_counts(sub,subweights,method='auto',limits=limits,check=check)
            if small['status']!='OPTIMAL_MATRIX_PLAN':
                small['prepeeled_rows']=len(prefix)
                return small
            stats=dict(small['stats'],prepeeled_rows=len(prefix),source_rows=len(matrix.rows),
                       core_rows=len(remaining))
            result=package_plan(matrix,small['deferred_rows'],method=small['method'],stats=stats,check=check)
            for key in ('lower_bound_certificate','decomposition','decomposition_scope_rows'):
                if key in small: result[key]=small[key]
            return result
    pivot_cols = {c for row in matrix.entries.values() for c,a in row.items() if a == 1}
    support = {}
    for row in matrix.entries.values():
        for c in row:
            if c in pivot_cols:
                support[c] = support.get(c, 0) + 1
    if method == 'two-incidence' or (method == 'auto' and max(support.values(), default=0) <= 2):
        return two_incidence_plan(counts, weights, check=check)
    return ordered_plan(counts, weights, decomposition, limits=limits, check=check)
