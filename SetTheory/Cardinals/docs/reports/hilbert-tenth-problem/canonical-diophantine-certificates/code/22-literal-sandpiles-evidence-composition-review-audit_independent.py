"""Independent audit: direct finite sink stabilization vs binary rank conditions.
No imports or execution from upstream or the certificate implementation.
"""
from itertools import product
from collections import deque
from fractions import Fraction
import json
DIRS = ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1))

def prism(shape):
    vs = tuple(product(*(range(s) for s in shape)))
    ix = {v: i for i, v in enumerate(vs)}
    ns = [tuple((ix[x] for d in DIRS if (x := tuple((a + b for a, b in zip(v, d)))) in ix)) for v in vs]
    halo = {tuple((a + b for a, b in zip(v, d))) for v in vs for d in DIRS} - {*vs}
    return (vs, ns, halo)

def stabilize(eta, ns):
    z = list(eta)
    u = [0] * len(z)
    q = deque((i for i, h in enumerate(z) if h >= 6))
    while q:
        i = q.popleft()
        if z[i] < 6:
            continue
        z[i] -= 6
        u[i] += 1
        if z[i] >= 6:
            q.append(i)
        for j in ns[i]:
            z[j] += 1
            if z[j] == 6:
                q.append(j)
    return (tuple(u), tuple(z))

def rank_candidates(z, u, ns):
    domains = [range(1, len(u) + 3) if t else (0,) for t in u]
    out = []
    for r in product(*domains):
        if all((not u[i] or (z[i] >= sum((r[j] >= r[i] for j in ns[i])) and (r[i] < 2 or z[i] < sum((r[j] + 1 >= r[i] for j in ns[i])))) for i in range(len(u)))):
            out.append(r)
    return out

def fiveway(delta, selectors, sigma):
    lm, ln, l0, lp, lplus = selectors
    return (sum(selectors) - 1) ** 2 + lm * (delta + 2 + sigma) ** 2 + ln * (delta + 1) ** 2 + l0 * delta ** 2 + lp * (delta - 1) ** 2 + lplus * (delta - 2 - sigma) ** 2 + (ln + l0 + lp) * sigma

def run():
    counts = {}
    for shape in ((1, 1, 1), (2, 1, 1), (1, 2, 1), (1, 1, 2), (3, 1, 1), (2, 2, 1), (2, 1, 2), (2, 2, 2), (3, 2, 4)):
        vs, ns, halo = prism(shape)
        a, b, c = shape
        V = len(vs)
        E = sum(map(len, ns)) // 2
        H = len(halo)
        if not (V == a * b * c and E == 3 * a * b * c - a * b - a * c - b * c and (H == 2 * (a * b + a * c + b * c))):
            raise AssertionError('audit check failed at source line 44')
        if not all((sum((sum((abs(vv - xx) for vv, xx in zip(v, x))) == 1 for v in vs)) == 1 for x in halo)):
            raise AssertionError('audit check failed at source line 45')
        if not 8 * V + 6 * E + H == 26 * a * b * c - 4 * (a * b + a * c + b * c):
            raise AssertionError('audit check failed at source line 46')
        if not 8 * V + 7 * E + H == 29 * a * b * c - 5 * (a * b + a * c + b * c):
            raise AssertionError('audit check failed at source line 47')
    counts['geometry_shapes'] = 9
    cases = 0
    candidate_pairs = 0
    rank_zeros = 0
    for shape, heights in (((1, 1, 1), range(19)), ((2, 1, 1), range(14)), ((3, 1, 1), range(9)), ((2, 2, 1), (0, 1, 4, 5, 6, 7))):
        vs, ns, halo = prism(shape)
        for eta in product(heights, repeat=len(vs)):
            true_u, true_z = stabilize(eta, ns)
            accepted = []
            for u in product((0, 1), repeat=len(vs)):
                z = tuple((eta[i] - 6 * u[i] + sum((u[j] for j in ns[i])) for i in range(len(vs))))
                if not all((0 <= h <= 5 for h in z)):
                    continue
                candidate_pairs += 1
                rs = rank_candidates(z, u, ns)
                if not len(rs) <= 1:
                    raise AssertionError((shape, eta, u, z, rs))
                if rs:
                    accepted.append((u, z, rs[0]))
                    rank_zeros += 1
            expected = int(all((t <= 1 for t in true_u)))
            if not len(accepted) == expected:
                raise AssertionError((shape, eta, true_u, accepted))
            if accepted:
                if not accepted[0][:2] == (true_u, true_z):
                    raise AssertionError('audit check failed at source line 63')
            cases += 1
    counts.update(initial_states=cases, stable_binary_candidates=candidate_pairs, canonical_rank_zeros=rank_zeros)
    ns = prism((2, 1, 1))[1]
    if not not rank_candidates((0, 0), (1, 1), ns):
        raise AssertionError('audit check failed at source line 67')
    if not stabilize((6, 5), ns) == ((1, 1), (1, 0)):
        raise AssertionError('audit check failed at source line 68')
    if not rank_candidates((1, 0), (1, 1), ns) == [(1, 2)]:
        raise AssertionError('audit check failed at source line 69')
    gadget_cases = 0
    for delta in range(-10, 11):
        zeros = []
        for sels in product((0, 1), repeat=5):
            for gap in range(12):
                if fiveway(delta, sels, gap) == 0:
                    zeros.append((sels, gap))
        if not len(zeros) == 1:
            raise AssertionError((delta, zeros))
        sels, gap = zeros[0]
        if not sels[2] + sels[3] + sels[4] == int(delta >= 0):
            raise AssertionError('audit check failed at source line 78')
        if not sels[1] + sels[2] + sels[3] + sels[4] == int(delta >= -1):
            raise AssertionError('audit check failed at source line 79')
        if not sels[0] + sels[1] + sels[2] == int(delta <= 0):
            raise AssertionError('audit check failed at source line 80')
        if not sels[0] + sels[1] + sels[2] + sels[3] == int(delta <= 1):
            raise AssertionError('audit check failed at source line 81')
        gadget_cases += 1
    counts['integer_differences'] = gadget_cases
    z = 0
    ell = 5
    f = Fraction(5, 6)
    k = Fraction(1, 6)
    c = beta = g = h = 0
    u = k + c
    eta = 1
    A = B = 0
    terms = [(z + 6 * u - eta) ** 2, (z + ell - 5) ** 2, (f + k + c - 1) ** 2, (f + k) * beta, (k + c) * (z - A - g) ** 2, f * g, c * (B - z - 1 - h) ** 2, (f + k) * h]
    if not all((t == 0 for t in terms)):
        raise AssertionError('audit check failed at source line 87')
    halo_gap = 5 - u
    if not (0 + u + halo_gap - 5 == 0 and halo_gap == Fraction(29, 6)):
        raise AssertionError('audit check failed at source line 89')
    print(json.dumps(counts, indent=2))
    return counts
if __name__ == '__main__':
    run()
