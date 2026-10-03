"""Audit the owner's constant-neighborhood exact collection algorithm."""
import sys, random, json
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import prism_certificate as pc
rng = random.Random(8912)
cases = []
for shape in ((1, 1, 1), (1, 2, 1), (3, 1, 1), (2, 2, 1), (2, 1, 3), (2, 2, 2), (3, 3, 3), (4, 3, 2)):
    for lower in ((0, 0, 0), (-3, 2, -1)):
        P = pc.Prism(lower, shape)
        for i, (p, q) in enumerate(P.edges()):
            if not P.edge_from_index(i) == (p, q):
                raise AssertionError('audit check failed at source line 11')
        for i, (x, p) in enumerate(P.halo()):
            if not P.halo_from_index(i) == (x, p):
                raise AssertionError('audit check failed at source line 13')
            axis = next((a for a in range(3) if x[a] != p[a]))
            sign = x[axis] - p[axis]
            if not P.halo_index(axis, sign, p) == i:
                raise AssertionError('audit check failed at source line 15')
        tab = tuple((rng.randrange(6) for _ in range(12)))
        src = pc.PeriodicInput((2, 3, 2), tab, tuple(((p, rng.randrange(3)) for p in P.points())))
        C = pc.Compiler(P, src)
        poly = C.polynomial()
        stream = list(C.collected_records())
        collected = dict(stream)
        if not len(stream) == len(collected):
            raise AssertionError(('duplicate', shape, lower))
        if not collected == poly:
            raise AssertionError(('coefficient mismatch', shape, lower))
        L = C.ledger(True)
        CL = C.closed_ledger()
        ST = C.collected_statistics()
        for k in ('records', 'summands', 'witnesses', 'evaluation_adds', 'evaluation_mults', 'expansion_coefficient_mults', 'plain_square_residuals', 'weighted_square_residuals', 'product_summands'):
            if not L[k] == CL[k]:
                raise AssertionError((k, L[k], CL[k]))
        for k in ('collected_monomials', 'degree', 'coefficient_height'):
            if not L[k] == ST[k]:
                raise AssertionError('audit check failed at source line 23')
        cases.append({'shape': shape, 'lower': lower, 'records': L['records'], 'collected': len(collected)})
print(json.dumps({'cases': cases}, indent=2))
