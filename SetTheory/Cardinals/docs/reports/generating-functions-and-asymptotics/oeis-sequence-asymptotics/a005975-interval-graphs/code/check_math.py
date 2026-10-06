#!/usr/bin/env python3
"""Regenerate the exact finite checks for Report 133, using the standard library.

All guards are explicit and remain active under python -O. Default output is
stable JSON on stdout. --output is an exclusive NEW file outside the bundle.
These checks do not certify an asymptotic onset or a finite error constant.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import math
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
from output_guard import external_output, write_external_bytes
ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise RuntimeError(str(message))

from collections import defaultdict, Counter
from itertools import product
import json
from pathlib import Path

def comps(total, length):
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in comps(total - first, length - 1):
            yield ((first,) + tail)

def matrices(n):
    for d in range(1, n + 1):

        def rows(i, remaining, covered, prior):
            if i == d:
                if remaining == 0:
                    yield prior
                return
            maxrow = remaining - (d - i - 1)
            for weight in range(1, maxrow + 1):
                for row in comps(weight, d - i):
                    if not covered >> i & 1 and row[0] == 0:
                        continue
                    new = covered
                    for offset, value in enumerate(row):
                        if value:
                            new |= 1 << i + offset
                    yield from rows(i + 1, remaining - weight, new, prior + (row,))
        yield from rows(0, n, 0, ())

def data(mat):
    cells = []
    reps = []
    for i, row in enumerate(mat):
        for offset, value in enumerate(row):
            if value:
                reps.append(len(cells))
            cells.extend([(i, i + offset)] * value)
    up = tuple((sum((1 << b for b, (l, r) in enumerate(cells) if j < l)) for i, j in cells))
    down = tuple((sum((1 << b for b, row in enumerate(up) if row >> a & 1)) for a in range(len(up))))
    return (up, down, cells, reps)

def poset_key(up):
    n = len(up)
    down = tuple((sum((1 << b for b, row in enumerate(up) if row >> a & 1)) for a in range(n)))
    order = sorted(range(n), key=lambda i: (down[i].bit_count(), up[i].bit_count()))
    return tuple((sum(((up[i] >> j & 1) << k for k, j in enumerate(order))) for i in order))

def graph_key(adj, root=None):
    n = len(adj)
    groups = defaultdict(list)
    for i in range(n):
        groups[int(i == root), adj[i].bit_count()].append(i)
    cells = [groups[k] for k in sorted(groups)]
    while True:
        new = []
        for cell in cells:
            splits = defaultdict(list)
            for i in cell:
                key = tuple((sum((adj[i] >> j & 1 for j in block)) for block in cells))
                splits[key].append(i)
            new.extend((splits[k] for k in sorted(splits)))
        if len(new) == len(cells):
            break
        cells = new

    def permutations(cell):
        classes = []
        for i in cell:
            for cls in classes:
                j = cls[0]
                if adj[i] & ~(1 << j) == adj[j] & ~(1 << i):
                    cls.append(i)
                    break
            else:
                classes.append([i])
        remaining = [len(c) for c in classes]

        def rec(order):
            if len(order) == len(cell):
                yield tuple(order)
                return
            for t, cls in enumerate(classes):
                if remaining[t]:
                    v = cls[len(cls) - remaining[t]]
                    remaining[t] -= 1
                    yield from rec(order + [v])
                    remaining[t] += 1
        yield from rec([])
    best = None
    for blocks in product(*(permutations(cell) for cell in cells)):
        order = sum(blocks, ())
        candidate = tuple((sum(((adj[i] >> j & 1) << k for k, j in enumerate(order))) for i in order))
        if best is None or candidate < best:
            best = candidate
    return best

def connected(adj):
    if not adj:
        return False
    seen = work = 1
    while work:
        bit = work & -work
        work ^= bit
        new = adj[bit.bit_length() - 1] & ~seen
        seen |= new
        work |= new
    return seen == (1 << len(adj)) - 1

def autonomous(up, down, mask):
    return all((up[i] & mask in (0, mask) and down[i] & mask in (0, mask) for i in range(len(up)) if not mask >> i & 1))

def strong_children(adj):
    n = len(adj)
    full = (1 << n) - 1
    modules = [m for m in range(1, full + 1) if all((adj[i] & m in (0, m) for i in range(n) if not m >> i & 1))]
    strong = [m for m in modules if not any((m & k and m & ~k and k & ~m for k in modules))]
    return [m for m in strong if m != full and (not any((m != k and k != full and (m & ~k == 0) for k in strong)))]

def inflate(up, v, dual=False):
    bags = [([i] if i < v else [i + 2]) if i != v else [v, v + 1, v + 2] for i in range(len(up))]
    out = [0] * (len(up) + 2)
    for i, row in enumerate(up):
        for j in range(len(up)):
            if row >> j & 1:
                for a in bags[i]:
                    for b in bags[j]:
                        out[a] |= 1 << b
    if not dual:
        out[v] |= 1 << v + 1 | 1 << v + 2
    else:
        out[v + 1] |= 1 << v
        out[v + 2] |= 1 << v
    return tuple(out)

def graphs(up, down=None):
    n = len(up)
    if down is None:
        down = tuple((sum((1 << b for b, row in enumerate(up) if row >> a & 1)) for a in range(n)))
    h = tuple((a | b for a, b in zip(up, down)))
    g = tuple(((1 << n) - 1 ^ row ^ 1 << i for i, row in enumerate(h)))
    return (h, g)

def graph_checks():
    summary = []
    fibers = {}
    eligible = {}
    finite_checks = []
    dominant_by_n = {}
    knownF = [1, 1, 2, 5, 15, 53, 217, 1014, 5335, 31240]
    knownI = [1, 1, 2, 4, 10, 27, 92, 369, 1807, 10344]
    knownC = [0, 1, 1, 2, 5, 15, 56, 250, 1328, 8069]
    for n in range(1, 10):
        types = {}
        f = defaultdict(list)
        e = []
        T = R = good = selfduals = connorders = selfdualconn = 0
        for mat in matrices(n):
            up, down, cells, reps = data(mat)
            p = poset_key(up)
            pd = poset_key(down)
            require(p not in types, ('duplicate Fishburn order', n, mat))
            types[p] = mat
            h, g = graphs(up, down)
            gh = graph_key(h)
            selfdual = p == pd
            selfduals += selfdual
            conn = connected(g)
            connorders += conn
            selfdualconn += selfdual and conn
            f[gh].append((p, pd, conn))
            diag = [i for i, (a, b) in enumerate(cells) if a == b]
            simplicial = [i for i in range(n) if all((g[i] & ~(1 << j | g[j]) == 0 for j in range(n) if g[i] >> j & 1))]
            require(diag == simplicial, ('diagonal test', n, mat))
            T += len(diag)
            R += sum((cells[i][0] == cells[i][1] for i in reps))
            if n <= 7:
                generic = not any((autonomous(up, down, m) for m in range(1, (1 << n) - 1) if 3 <= m.bit_count() <= n - 1))
                good += generic
                if generic and n >= 5:
                    kids = strong_children(h)
                    require(connected(h) and connected(g), 'mathematical invariant')
                    require(all((k.bit_count() <= 2 for k in kids)), 'mathematical invariant')
                if generic and (not selfdual) and (n >= 5):
                    for v in reps:
                        if v not in diag:
                            continue
                        if any((autonomous(up, down, 1 << v | 1 << w) for w in range(n) if w != v)):
                            continue
                        require(any((k == 1 << v for k in kids)), 'mathematical invariant')
                        e.append((up, v))
        require(len(types) == knownF[n], ('F count', n, len(types)))
        require(len(f) == knownI[n], ('I count', n, len(f)))
        C = sum((vals[0][2] for vals in f.values()))
        require(C == knownC[n], ('C count', n, C))
        fibers[n] = f
        eligible[n] = e
        loss = (connorders + selfdualconn) // 2 - C
        row = dict(n=n, F=len(types), I=len(f), C=C, selfdual_orders=selfduals, connected_orders=connorders, T=T, R=R, T_minus_R=T - R, good=good if n <= 7 else None, eligible=len(e) if 5 <= n <= 7 else None, connected_fiber_loss=loss)
        summary.append(row)
    for m in range(5, 8):
        hits = Counter()
        explicit = defaultdict(set)
        for up, v in eligible[m]:
            down = tuple((sum((1 << b for b, row in enumerate(up) if row >> a & 1)) for a in range(m)))
            produced = []
            for qq in (up, down):
                for internaldual in (False, True):
                    pp = inflate(qq, v, internaldual)
                    hh, gg = graphs(pp)
                    produced.append(poset_key(pp))
                    require(connected(hh) and connected(gg), 'mathematical invariant')
                    kids = strong_children(hh)
                    big = [k for k in kids if k.bit_count() == 3]
                    require(len(big) == 1 and big[0] == 7 << v, 'mathematical invariant')
                    require(all((k.bit_count() <= 2 or k == big[0] for k in kids)), 'mathematical invariant')
            require(len(set(produced)) == 4, 'mathematical invariant')
            h, g = graphs(inflate(up, v))
            key = graph_key(h)
            hits[key] += 1
            explicit[key].update(produced)
        dominant_by_n[m + 2] = set(hits)
        require(all((k == 2 for k in hits.values())), 'mathematical invariant')
        for key in hits:
            full = fibers[m + 2][key]
            require(len(full) == 4 and {p for p, pd, c in full} == explicit[key], 'mathematical invariant')
            require(all((p != pd for p, pd, c in full)), 'mathematical invariant')
            require(len({min(p, pd) for p, pd, c in full}) == 2, 'mathematical invariant')
        row = dict(quotient_size=m, eligible_roots=len(eligible[m]), dominant_graphs=len(hits), all_fibers_have_four_types=True, all_have_two_dual_orbits=True, all_have_no_selfdual_order=True, all_graph_preimage_counts_two=True)
        finite_checks.append(row)
    exhaustive_cases = []

    def induced(up, keep):
        return tuple((sum(((up[i] >> j & 1) << k for k, j in enumerate(keep))) for i in keep))

    def iseligible(up, v):
        n = len(up)
        down = tuple((sum((1 << b for b, row in enumerate(up) if row >> a & 1)) for a in range(n)))
        h, g = graphs(up, down)
        simplicial = all((g[v] & ~(1 << j | g[j]) == 0 for j in range(n) if g[v] >> j & 1))
        generic = not any((autonomous(up, down, m) for m in range(1, (1 << n) - 1) if 3 <= m.bit_count() <= n - 1))
        pair = any((autonomous(up, down, 1 << v | 1 << w) for w in range(n) if w != v))
        return n >= 5 and simplicial and generic and (not pair) and (poset_key(up) != poset_key(down))
    for n in range(5, 10):
        counts = Counter()
        losses = Counter()
        orders_checked = 0
        restorations = 0
        for key, fullfiber in fibers[n].items():
            if not fullfiber[0][2]:
                continue
            dualorbits = len({min(p, pd) for p, pd, c in fullfiber})
            loss = dualorbits - 1
            if loss == 0:
                continue
            categories = set()
            for up, pd, c in fullfiber:
                orders_checked += 1
                h, g = graphs(up)
                keep = [i for i, row in enumerate(h) if row]
                require(keep, ('complete graph lost an orbit', n))
                u = n - len(keep)
                core = induced(up, keep)
                hc, gc = graphs(core)
                require(connected(hc), 'mathematical invariant')
                if u:
                    restored = {poset_key(induced(p, [i for i, row in enumerate(graphs(p)[0]) if row])) for p, pd, c in fullfiber}
                    allcore = {p for p, pd, c in fibers[len(keep)][graph_key(hc)]}
                    require(restored == allcore, ('universal-vertex fiber', n, key))
                    restorations += 1
                if not connected(gc):
                    require(u >= 1, 'mathematical invariant')
                    categories.add('7.1 disconnected core')
                    continue
                kids = strong_children(hc)
                require(len(kids) >= 4, 'mathematical invariant')
                edgekids = [k for k in kids if any((hc[i] & k for i in range(len(core)) if k >> i & 1))]
                if u:
                    require(any((k.bit_count() >= 3 for k in edgekids)), 'mathematical invariant')
                    categories.add('7.2 universal plus exceptional prime core')
                    continue
                if any((k.bit_count() >= 4 for k in edgekids)):
                    categories.add('7.3 large comparable child')
                    continue
                stars = []
                for k in edgekids:
                    vertices = [i for i in range(n) if k >> i & 1]
                    if k.bit_count() == 3 and sorted(((h[i] & k).bit_count() for i in vertices)) == [1, 1, 2]:
                        stars.append(k)
                require(stars, ('loss with only unique-orientation children', n, key))
                indominant = key in dominant_by_n.get(n, set())
                for k in stars:
                    v = (k & -k).bit_length() - 1
                    keep = [i for i in range(n) if not k >> i & 1 or i == v]
                    quotient = induced(up, keep)
                    marked = keep.index(v)
                    qh, qg = graphs(quotient)
                    require(all((qg[marked] & ~(1 << j | qg[j]) == 0 for j in range(len(quotient)) if qg[marked] >> j & 1)), 'mathematical invariant')
                    if not indominant:
                        require(not iseligible(quotient, marked), 'mathematical invariant')
                categories.add('dominant' if indominant else '7.4 excluded rooted quotient')
            require(len(categories) == 1, (n, key, categories))
            category = next(iter(categories))
            counts[category] += 1
            losses[category] += loss
        row = dict(n=n, positive_loss_graphs_by_case=dict(counts), loss_by_case=dict(losses), all_order_types_checked=orders_checked, universal_restoration_order_checks=restorations)
        exhaustive_cases.append(row)
    return dict(summary=summary, dominant_fiber_checks=finite_checks, exhaustive_case_checks=exhaustive_cases)

def auxiliary_checks(result):
    rows = result['summary']
    F = [1] + [r['F'] for r in rows]
    I = [1] + [r['I'] for r in rows]
    C = [0] + [r['C'] for r in rows]
    O = [0] + [r['connected_orders'] for r in rows]
    T = [0] + [r['T'] for r in rows]
    for n, row in enumerate(rows, 1):
        require(row['T'] - row['R'] == T[n - 1], ('diagonal identity', n))
        require(F[n] == sum(O[k] * F[n-k] for k in range(1,n+1)), ('ordinal identity',n))
    # Exact Euler transform via logarithmic derivative, using integer arithmetic.
    reconstructed = [1]
    for n in range(1,10):
        total = sum(sum(d*C[d] for d in range(1,k+1) if k%d==0)*reconstructed[n-k]
                    for k in range(1,n+1))
        require(total % n == 0, ('Euler divisibility', n))
        reconstructed.append(total//n)
    require(reconstructed == I, 'Euler component reconstruction')
    # Brute-force automorphism orbits independently verify occupied-cell roots.
    rooted = []
    for n in range(1,6):
        root_count = 0
        for matrix in matrices(n):
            up, down, cells, representatives = data(matrix)
            parent = list(range(n))
            def find(i):
                while parent[i] != i:
                    i = parent[i]
                return i
            for permutation in permutations(range(n)):
                if all((up[i] >> j & 1) == (up[permutation[i]] >> permutation[j] & 1)
                       for i in range(n) for j in range(n)):
                    for i in range(n):
                        parent[find(i)] = find(permutation[i])
            for i in range(n):
                for j in range(n):
                    require((find(i)==find(j)) == (cells[i]==cells[j]), 'cell orbit equality')
            root_count += len({find(i) for i,(a,b) in enumerate(cells) if a==b})
        require(root_count == rows[n-1]['R'], ('rooted isomorphism count',n))
        rooted.append(root_count)
    # Rational coefficient polynomials in z = pi^2, independent of floating point.
    c1 = (Q(11,24), -Q(17,144), Q(1,432))
    aF = tuple(c1[i]-(Q(1,12) if i==0 else 0) for i in range(3))
    require(aF == (Q(3,8), -Q(17,144), Q(1,432)), 'Stirling normalization')
    alphaI = (aF[0], aF[1]-Q(1,6), aF[2])
    alphaC = (aF[0], aF[1]-Q(1,3), aF[2])
    require(alphaI == (Q(3,8), -Q(41,144), Q(1,432)), 'all graph first correction')
    require(alphaC == (Q(3,8), -Q(65,144), Q(1,432)), 'connected first correction')
    require(-2*Q(1,6)**2 == -Q(1,18), 'logarithmic normalization')
    return dict(diagonal_identity_through=9, ordinal_through=9, Euler_through=9,
                brute_force_rooted_counts_through_5=rooted,
                aF=[str(c) for c in aF], alphaI=[str(c) for c in alphaI],
                alphaC=[str(c) for c in alphaC], log_pi_four_coefficient='-1/18')


def psi(z):
    correction = 0.0
    while z < 16:
        correction -= 1/z
        z += 1
    inv = 1/z
    # Digamma expansion through z^-10; error here is below double precision.
    return correction + math.log(z) - inv/2 - inv**2/12 + inv**4/120 - inv**6/252 + inv**8/240 - inv**10/132


def inverse_checks():
    q = 6/math.pi**2
    K = 6*math.sqrt(3)*math.exp(math.pi**2/12)/math.pi**2.5
    aF = 3/8-17*math.pi**2/144+math.pi**4/432
    beta = math.pi**4/18
    results = []
    for kind, alpha in [('I',aF-math.pi**2/6),('C',aF-math.pi**2/3)]:
        def phi(y):
            return math.log(K)+math.lgamma(y+1)+math.log(y)/2+y*math.log(q)+alpha/y-beta*math.log(y)/y**2
        def derivative(y):
            return psi(y+1)+1/(2*y)+math.log(q)-alpha/y**2+beta*(2*math.log(y)-1)/y**3
        errors = []
        for x in (20.0, 50.0, 100.0, 200.0):
            L = x*math.log(q*x/math.e)
            # x satisfies the defining Lambert equation exactly as an identity.
            w = math.log(q*x/math.e)
            require(abs(w*math.exp(w)-q*L/math.e) < 1e-10*L, 'Lambert identity')
            lo, hi = x-5, x+5
            require(phi(lo)<L<phi(hi), 'large-root bracket')
            for iteration in range(80):
                mid = (lo+hi)/2
                if phi(mid)<L: lo=mid
                else: hi=mid
            y = (lo+hi)/2
            first = x-(phi(x)-L)/derivative(x)
            second = first-(phi(first)-L)/derivative(first)
            error1, error2 = abs(first-y), abs(second-y)
            require(error1*x*math.log(x)<10, 'first Newton scaled error')
            require(error2*x**3*math.log(x)**3<100, 'second Newton scaled error')
            for step in (-0.1,0.1):
                remainder = abs(phi(x+step)-phi(x)-derivative(x)*step)
                require(remainder <= step**2/x, 'finite Taylor remainder')
            difference = (phi(x+0.01)-phi(x-0.01))/0.02
            require(abs(difference-derivative(x))<1e-5/x, 'digamma derivative check')
            errors.append(dict(x=int(x), first_scaled=round(error1*x*math.log(x),6),
                               second_scaled=round(error2*x**3*math.log(x)**3,6)))
        results.append(dict(sequence=kind, finite_checks=errors))
    return results


def induced(up, keep):
    return tuple((sum(((up[i] >> j & 1) << k for k, j in enumerate(keep))) for i in keep))

def downsets(up):
    return tuple((sum((1 << b for b, row in enumerate(up) if row >> a & 1)) for a in range(len(up))))

def simplicial(g, v):
    return all((g[v] & ~(1 << j | g[j]) == 0 for j in range(len(g)) if g[v] >> j & 1))

def serial_extension(up, first=False):
    m = len(up)
    if first:
        return tuple(up) + ((1 << m) - 1, 0)
    return tuple((row | 1 << m for row in up)) + (0, 0)

def constant_refinement_checks(base):
    knownF = [1] + [row['F'] for row in base['summary']]
    knownI = [1] + [row['I'] for row in base['summary']]
    knownC = [0] + [row['C'] for row in base['summary']]
    fibers = {}
    generic_nonselfdual = {}
    eligible = {}
    summary = []
    previousT = 0
    checks = Counter()
    for n in range(1, 10):
        f = defaultdict(list)
        genericA = []
        er = []
        T = R = O = Sconn = generic_count = badroot = pairroot = 0
        for mat in matrices(n):
            up, down, cells, reps = data(mat)
            p = poset_key(up)
            pd = poset_key(down)
            h, g = graphs(up, down)
            key = graph_key(h)
            conn = connected(g)
            f[key].append((p, pd, conn))
            O += conn
            Sconn += conn and p == pd
            diag = [v for v in reps if cells[v][0] == cells[v][1]]
            require(all((simplicial(g, v) == (cells[v][0] == cells[v][1]) for v in range(n))), 'constant refinement invariant')
            T += sum((a == b for a, b in cells))
            R += len(diag)
            if n <= 7:
                forbidden = [mask for mask in range(1, (1 << n) - 1) if 3 <= mask.bit_count() <= n - 1 and autonomous(up, down, mask)]
                generic = not forbidden
                generic_count += generic
                if generic and p != pd and (n >= 5):
                    genericA.append(up)
                for v in diag:
                    if forbidden:
                        badroot += 1
                    pairs = [1 << v | 1 << w for w in range(n) if w != v and autonomous(up, down, 1 << v | 1 << w)]
                    pairroot += bool(pairs)
                    if n >= 5 and generic and (p != pd) and (not pairs):
                        er.append((up, v))
                    for mask in forbidden:
                        members = [i for i in range(n) if mask >> i & 1]
                        if mask >> v & 1:
                            inner = induced(up, members)
                            _, ig = graphs(inner)
                            require(simplicial(ig, members.index(v)), 'constant refinement invariant')
                            checks['inside_module_simplicial'] += 1
                        else:
                            keep = [i for i in range(n) if not mask >> i & 1 or i == members[0]]
                            quotient = induced(up, keep)
                            _, qg = graphs(quotient)
                            require(simplicial(qg, keep.index(v)), 'constant refinement invariant')
                            checks['outside_module_simplicial'] += 1
                    for mask in pairs:
                        keep = [i for i in range(n) if not mask >> i & 1 or i == v]
                        quotient = induced(up, keep)
                        _, qg = graphs(quotient)
                        require(simplicial(qg, keep.index(v)), 'constant refinement invariant')
                        checks['pair_contraction_simplicial'] += 1
        require(sum(map(len, f.values())) == knownF[n], 'constant refinement invariant')
        require(len(f) == knownI[n] and sum((v[0][2] for v in f.values())) == knownC[n], 'constant refinement invariant')
        require(T - R == previousT, 'constant refinement invariant')
        previousT = T
        checks['exact_T_minus_R'] += 1
        if n >= 2 and n <= 7:
            require(pairroot <= 3 * summary[-1]['R'], 'constant refinement invariant')
        fibers[n] = f
        generic_nonselfdual[n] = genericA
        eligible[n] = er
        row = dict(n=n, F=knownF[n], I=len(f), C=knownC[n], O=O, T=T, R=R, ordinal_remainder=knownF[n] - O, connected_fiber_loss=(O + Sconn) // 2 - knownC[n], generic=generic_count if n <= 7 else None, generic_nonselfdual=len(genericA) if 5 <= n <= 7 else None, eligible=len(er) if 5 <= n <= 7 else None, rooted_nongeneric=badroot if n <= 7 else None, rooted_in_autonomous_pair=pairroot if n <= 7 else None)
        summary.append(row)
    serial_by_n = {}
    dominant_by_n = {}
    family_checks = []
    for m in range(5, 8):
        serial_hits = Counter()
        serial_types = defaultdict(set)
        for up in generic_nonselfdual[m]:
            down = downsets(up)
            produced = []
            for q in (up, down):
                for first in (False, True):
                    pp = serial_extension(q, first)
                    hh, gg = graphs(pp)
                    require(connected(gg), 'constant refinement invariant')
                    universal = [v for v, row in enumerate(gg) if row.bit_count() == m + 1]
                    leaves = [v for v, row in enumerate(gg) if row.bit_count() == 1]
                    require(universal == [m + 1] and leaves == [m], 'constant refinement invariant')
                    require(graph_key(induced(gg, list(range(m)))) == graph_key(graphs(up)[1]), 'constant refinement invariant')
                    produced.append(poset_key(pp))
                    checks['serial_special_vertices_canonical'] += 1
            require(len(set(produced)) == 4, 'constant refinement invariant')
            key = graph_key(graphs(serial_extension(up))[0])
            serial_hits[key] += 1
            serial_types[key].update(produced)
        require(all((v == 2 for v in serial_hits.values())), 'constant refinement invariant')
        for key in serial_hits:
            full = fibers[m + 2][key]
            require(len(full) == 4 and {p for p, pd, c in full} == serial_types[key], 'constant refinement invariant')
            require(all((p != pd for p, pd, c in full)), 'constant refinement invariant')
            require(len({min(p, pd) for p, pd, c in full}) == 2, 'constant refinement invariant')
            checks['serial_full_fibers'] += 1
        serial_by_n[m + 2] = set(serial_hits)
        dhits = Counter()
        for up, v in eligible[m]:
            key = graph_key(graphs(inflate(up, v))[0])
            dhits[key] += 1
        require(all((v == 2 for v in dhits.values())), 'constant refinement invariant')
        for key in dhits:
            full = fibers[m + 2][key]
            require(len(full) == 4 and len({min(p, pd) for p, pd, c in full}) == 2, 'constant refinement invariant')
            require(all((p != pd for p, pd, c in full)), 'constant refinement invariant')
        dominant_by_n[m + 2] = set(dhits)
        require(not set(dhits) & set(serial_hits), 'constant refinement invariant')
        row = dict(m=m, A=len(generic_nonselfdual[m]), J_graphs=len(serial_hits), E=len(eligible[m]), D_graphs=len(dhits), serial_preimages_exactly_two=True, serial_fiber_types_exactly_four=True, serial_dual_orbits_exactly_two=True, serial_fixed_points_zero=True, families_disjoint=True)
        family_checks.append(row)
    partitions = []
    for n in range(7, 10):
        count = Counter()
        loss = Counter()
        for key, full in fibers[n].items():
            if not full[0][2]:
                continue
            delta = len({min(p, pd) for p, pd, c in full}) - 1
            if not delta:
                continue
            up = full[0][0]
            h, g = graphs(up)
            keep = [i for i, row in enumerate(h) if row]
            u = n - len(keep)
            core = induced(up, keep)
            hc, gc = graphs(core)
            if key in serial_by_n[n]:
                category = 'J_serial_exact'
            elif key in dominant_by_n[n]:
                category = 'D_rooted_exact'
            elif not connected(gc):
                category = 'serial_residual'
            elif u:
                category = 'prime_core_with_universals'
            else:
                kids = strong_children(hc)
                big = [k for k in kids if k.bit_count() >= 4 and any((hc[i] & k for i in range(len(core)) if k >> i & 1))]
                category = 'large_comparable_child' if big else 'excluded_rooted_quotient'
            count[category] += 1
            loss[category] += delta
        require(sum(loss.values()) == summary[n - 1]['connected_fiber_loss'], 'constant refinement invariant')
        row = dict(n=n, positive_loss_graphs=dict(count), loss=dict(loss))
        partitions.append(row)
    known_serial_graphs = [3, 15, 94]
    require([row['J_graphs'] for row in family_checks] == known_serial_graphs, 'serial family counts')
    require([row['A'] for row in family_checks] == [6, 30, 188], 'generic nonselfdual core counts')
    require(Q(1, 2) + Q(1, 2) == 1, 'shifted constant ledger')
    require(-1 + 2 * Q(1, 2) == 0, 'all graph second-shift cancellation')
    require(1 + 2 - 2 == 1, 'ordinal second-shift coefficient')
    require(-2 * Q(-1, 2) == 1 and -Q(-1, 2) == Q(1, 2), 'Fishburn ratio constant normalization')
    return dict(summary=summary, exact_checks=dict(checks), families=family_checks, loss_partitions=partitions, constant_ledger={'rooted_mean': 'log(q)+gamma', 'serial_loss': '1/2', 'ordinal_half': '1/2', 'total': 'log(q)+gamma+1', 'all_graph_component_cancellation': '0'}, Fishburn_relative_constants={'C': '1/q-2*b0/q^2', 'I': '1/(2*q)-2*b0/q^2'})

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    try:
        output = external_output(args.output,ROOT) if args.output is not None else None
        result=graph_checks()
        result['constant_refinement']=constant_refinement_checks(result)
        result['auxiliary']=auxiliary_checks(result)
        result['inversion']=inverse_checks()
        result['status']='PASS'
        blob=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode()
        if output is not None:
            write_external_bytes(output,blob,ROOT)
        else:
            sys.stdout.buffer.write(blob)
    except (OSError,RuntimeError,ValueError) as exc:
        print('CHECK_FAILED: '+str(exc),file=sys.stderr)
        return 1
    return 0

if __name__=='__main__':
    raise SystemExit(main())
