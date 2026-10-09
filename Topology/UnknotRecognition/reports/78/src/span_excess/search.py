"""Exact finite band search. Results have no implicit knot-recognition meaning."""
from __future__ import annotations
from .model import HeightModel, Budget, noop, integer
from .strata import enumerate_strata, constraints_for, stratum_count
from .network import minimize_difference
from .checker import replay_cell


def optimize_band(model: HeightModel, k: int, *, extra=(), max_work=None,
                  check=noop, save_cells=True, on_cell=None):
    model.validate()
    if integer(k) < 0:
        raise ValueError("negative excess")
    budget = Budget(max_work, check)
    for u, v, b in extra:
        if not (0 <= integer(u) < model.n and 0 <= integer(v) < model.n):
            raise ValueError("extra constraint endpoint out of range")
        integer(b)
    records, profile = [], {}
    count = feasible = augmentations = 0
    best = None
    for cell in enumerate_strata(model, k, budget.tick):
        budget.tick()
        constraints = constraints_for(model, cell)+tuple(extra)
        result = minimize_difference(model.n, model.edges, constraints,
                                     check=budget.tick)
        proof = result['certificate']
        row = {'stratum': cell.to_list(), 'excess': cell.excess, 'proof': proof}
        if proof['status'] == 'OPTIMAL':
            feasible += 1
            p = proof['potential']
            if model.span(p) != model.optimum+cell.excess:
                raise ArithmeticError("stratum did not have its advertised exact span")
            row['score2'] = model.score2(p)
            # Prefer lower excess among equal Euler scores. This is not a
            # general connectedness guarantee; see the article's counterpoint.
            if best is None or (row['score2'], -row['excess']) > (best['score2'], -best['excess']):
                best = row
            q = str(cell.excess)
            if q not in profile or row['score2'] > profile[q]['score2']:
                profile[q] = row
        if not replay_cell(model, row, extra):
            raise ArithmeticError("independent cell replay failed")
        count += 1
        augmentations += result['stats']['augmentations']
        if save_cells:
            records.append(row)
        if on_cell is not None:
            on_cell(row)
    if count != stratum_count(len(model.vertices), k):
        raise ArithmeticError("enumeration cardinality mismatch")
    return {'schema': 'span-excess-band-v1', 'status': 'COMPLETE', 'radius': k,
            'extra_constraints': list(map(list, extra)), 'best': best,
            'profile': profile, 'cells': records if save_cells else None,
            'stats': {'strata': count, 'feasible_strata': feasible,
                      'augmentations': augmentations, 'work': budget.work}}
