"""Cross-check newly authored compiler against separate sparse expansion."""
import sys, json, random
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import prism_certificate as pc
from audit_polynomial import build, evaluate
from audit_independent import prism, stabilize
cases = []
for shape, eta, bg in [((1, 1, 1), (0,), 0), ((1, 1, 1), (1,), 0), ((1, 1, 1), (6,), 0), ((1, 1, 1), (6,), 5), ((2, 1, 1), (5, 5), 0), ((2, 1, 1), (6, 5), 0), ((2, 2, 1), (6, 5, 4, 0), 0), ((2, 2, 2), (6, 5, 4, 3, 2, 1, 0, 0), 0)]:
    P = pc.Prism((0, 0, 0), shape)
    src = pc.PeriodicInput((1, 1, 1), (bg,), tuple(((p, eta[i] - bg) for i, p in enumerate(P.points()) if eta[i] != bg)))
    C = pc.Compiler(P, src)
    ind = build(shape, eta, bg)
    names = {f'{i}:{f}': C.v(p, f) for i, p in enumerate(P.points()) for f in pc.FIELDS}
    for p, q in P.edges():
        i, j = (P.index(p), P.index(q))
        names.update({f'{i},{j}:{our}': C.ev(p, q, their) for our, their in zip(('lm', 'ln', 'l0', 'lp', 'lplus', 'sig'), pc.EDGE_FIELDS)})
    for j, (x, p) in enumerate(P.halo()):
        names[f'H{x}'] = 8 * P.V + 6 * P.E + j
    mapped = {tuple(sorted((names[x] for x in m))): a for m, a in ind['polynomial'].items()}
    theirs = C.polynomial()
    if not mapped == theirs:
        raise AssertionError((shape, eta, bg))
    L = C.ledger(True)
    CL = C.closed_ledger()
    if not L['records'] == ind['raw_monomials'] == CL['records']:
        raise AssertionError('audit check failed at source line 25')
    if not L['collected_monomials'] == ind['collected_monomials']:
        raise AssertionError('audit check failed at source line 26')
    if not L['coefficient_height'] <= L['coefficient_height_bound']:
        raise AssertionError('audit check failed at source line 27')
    if not (L['witnesses'] == ind['variables'] and L['summands'] == ind['summands']):
        raise AssertionError('audit check failed at source line 28')
    for key in ('plain_square_residuals', 'weighted_square_residuals', 'product_summands'):
        if not L[key] == CL[key]:
            raise AssertionError('audit check failed at source line 29')
    rng = random.Random(8321)
    for _ in range(10):
        w = [rng.randrange(5) for _ in range(P.witnesses)]
        if not C.evaluate(w) == evaluate(theirs, {i: x for i, x in enumerate(w)}):
            raise AssertionError('audit check failed at source line 33')
    cases.append({'shape': shape, 'eta': eta, 'background': bg, 'records': L['records'], 'collected': L['collected_monomials']})
for shape in ((1, 1, 1), (1, 2, 1), (1, 1, 3), (3, 1, 1), (3, 4, 2)):
    for lower in ((0, 0, 0), (-8, -2, 4), (9, 3, -5)):
        P = pc.Prism(lower, shape)
        if not list(map(P.index, P.points())) == list(range(P.V)):
            raise AssertionError('audit check failed at source line 39')
        if not [P.index(P.point(i)) for i in range(P.V)] == list(range(P.V)):
            raise AssertionError('audit check failed at source line 40')
        if not [P.edge_index(p, q) for p, q in P.edges()] == list(range(P.E)):
            raise AssertionError('audit check failed at source line 41')
        if not [P.edge_index(q, p) for p, q in P.edges()] == list(range(P.E)):
            raise AssertionError('audit check failed at source line 42')
        if not len({x for x, p in P.halo()}) == P.H:
            raise AssertionError('audit check failed at source line 43')
        if not all((not P.contains(x) and P.contains(p) and (sum((abs(a - b) for a, b in zip(x, p))) == 1) for x, p in P.halo())):
            raise AssertionError('audit check failed at source line 44')
        C = pc.Compiler(P, pc.PeriodicInput((1, 1, 1), (0,), ((lower, 6),)))
        if not C.evaluate(C.certificate()) == 0:
            raise AssertionError('audit check failed at source line 46')
checks = 0
for shape, heights in (((1, 1, 1), range(19)), ((2, 1, 1), range(14)), ((3, 1, 1), range(9)), ((2, 2, 1), (0, 1, 4, 5, 6, 7))):
    P = pc.Prism((0, 0, 0), shape)
    vs, ns, halo = prism(shape)
    from itertools import product
    for eta in product(heights, repeat=P.V):
        C = pc.Compiler(P, pc.PeriodicInput((1, 1, 1), (0,), tuple(((p, h) for p, h in zip(vs, eta) if h))))
        u, z = stabilize(eta, ns)
        if max(u) > 1:
            try:
                C.certificate()
            except ValueError:
                pass
            else:
                raise AssertionError(('incorrect acceptance', shape, eta, u))
        else:
            w = C.certificate()
            if not C.evaluate(w) == 0:
                raise AssertionError('audit check failed at source line 62')
            if not tuple((w[C.v(p, 'k')] + w[C.v(p, 'c')] for p in vs)) == u:
                raise AssertionError('audit check failed at source line 63')
            if not tuple((w[C.v(p, 'z')] for p in vs)) == z:
                raise AssertionError('audit check failed at source line 64')
        checks += 1
print(json.dumps({'exact_polynomial_cases': cases, 'translated_geometry_cases': 15, 'random_off_zero_evaluations': 80, 'constructor_cases': checks}, indent=2))
