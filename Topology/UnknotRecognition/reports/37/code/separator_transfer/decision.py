"""Cut-only preflight for a certified closed complex; NOT a generic knot oracle."""
from .core import F2, minimum_vertex_cut, factor_at_cut
from .cube import morse_graphs
from .budgets import sharp_rank_budget


def terminal_rank_one_test(complex_, matching):
    """Return RANK_NOT_ONE or exact rank, and whether coefficients were evaluated.

    An arbitrary chain complex is not interpreted as a knot. Converting rank
    results into UNKNOT/KNOTTED requires a verified reduced knot-complex origin.
    Construction of the complex and matching is outside this function's cost.
    """
    counts, graphs = morse_graphs(complex_, matching)
    cuts = {key: minimum_vertex_cut(g) for key, g in graphs.items()}
    budget = sharp_rank_budget(counts, {key: c.capacity for key,c in cuts.items()})
    lower = budget['homology_lower']
    if lower > 1:
        return dict(status='RANK_NOT_ONE', lower=lower, exact_rank=None,
                    evaluated_maps=0, critical=budget['dimension'])
    ranks = [factor_at_cut(graphs[key], cut.cut, F2()).binary_rank()
             for key,cut in cuts.items()]
    rank = budget['dimension'] - 2*sum(ranks)
    return dict(status='RANK_ONE' if rank == 1 else 'RANK_NOT_ONE',
                lower=lower, exact_rank=rank, evaluated_maps=len(ranks),
                critical=budget['dimension'])
