"""Independent exact static combinatorics and formal algebra. No source reads.

P is reconstructed by Newton differences of finite integer values.
L is obtained by the alternating logarithm series, not its recurrence.
D is solved using the exponentiated equation, not the source log recurrence.
All loops enumerate finite graphs/tables or perform rational arithmetic.
No upstream program, interpreter, simulator, schedule or theorem prover runs.
"""
from fractions import Fraction as F
from math import comb, factorial, isqrt
from pathlib import Path
import json

ORDER = 8
MAX_N = 64
OUT = Path(__file__).resolve().parent / 'evidence' / 'mathematics.json'

# Laurent coefficient ring Q[s,s^-1,lambda,lambda^-1].
def mon(c=1, s=0, lam=0):
    return {(s, lam): F(c)} if c else {}

def plus(*terms):
    out = {}
    for p in terms:
        for e, c in p.items():
            out[e] = out.get(e, F(0)) + c
    return {e: c for e, c in out.items() if c}

def times(p, q):
    out = {}
    for (a, b), c in p.items():
        for (d, e), f in q.items():
            key = (a+d, b+e)
            out[key] = out.get(key, F(0)) + c*f
    return {e: c for e, c in out.items() if c}

def scaled(p, c=1, s=0, lam=0):
    return times(p, mon(c, s, lam))

def zero_series(m):
    return [{} for _ in range(m+1)]

def series_add(*args):
    return [plus(*(p[i] for p in args)) for i in range(len(args[0]))]

def series_mul(p, q):
    m = len(p)-1
    out = zero_series(m)
    for i in range(m+1):
        out[i] = plus(*(times(p[j], q[i-j]) for j in range(i+1)))
    return out

def series_scale(p, factor):
    return [times(c, factor) for c in p]

def series_pow(p, n):
    out = zero_series(len(p)-1)
    out[0] = mon()
    for _ in range(n):
        out = series_mul(out, p)
    return out

def series_exp(p):
    assert not p[0]
    m = len(p)-1
    out = zero_series(m)
    out[0] = mon()
    # (exp p)' = p' exp p is independently exact for formal series.
    for k in range(1, m+1):
        out[k] = scaled(plus(*(scaled(times(p[j], out[k-j]), j)
                                for j in range(1, k+1))), F(1, k))
    return out

def substitute(poly, series):
    m = len(series)-1
    out = zero_series(m)
    for (power, lam), c in poly.items():
        assert power >= 0
        out = series_add(out, series_scale(series_pow(series, power), mon(c, lam=lam)))
    return out

def sector(n, k):
    return sum(comb(n, r)*comb(n, k-r)*2**(r*(k-r))
               for r in range(max(0, k-n), min(n, k)+1))

def make_P(k):
    # Newton interpolation from k+1 exact values; degree <=k is proved in text.
    differences = [sector(n, k) for n in range(k+1)]
    basis, out = mon(), {}
    for j in range(k+1):
        out = plus(out, scaled(basis, differences[0]))
        differences = [b-a for a, b in zip(differences, differences[1:])]
        basis = scaled(times(basis, plus(mon(s=1), mon(-j))), F(1, j+1))
    return out

def evaluate(poly, n):
    assert all(lam == 0 for s, lam in poly)
    return sum(c*F(n)**s for (s, lam), c in poly.items())

def a(n):
    return sum(comb(n, j)*(1+2**j)**n for j in range(n+1))

def exponentiated_residual(delta, ps):
    m = len(delta)-1
    x = [dict(p) for p in delta]
    x[0] = mon(s=1)
    delta_square = series_mul(delta, delta)
    out = zero_series(m)
    for k in range(m+1):
        factor = plus(mon(2, s=1, lam=1), mon(-k, lam=1))
        exponent = series_add(series_scale(delta, factor),
                              series_scale(delta_square, mon(lam=1)))
        term = series_mul(substitute(ps[k], x), series_exp(exponent))
        for j in range(m-k+1):
            out[j+k] = plus(out[j+k], term[j])
    out[0] = plus(out[0], mon(-1))
    return out

def logarithmic_residual(delta, logs):
    m = len(delta)-1
    x = [dict(p) for p in delta]
    x[0] = mon(s=1)
    out = series_add(series_scale(delta, mon(2, s=1)), series_mul(delta, delta))
    for k in range(1, m+1):
        term = series_mul(substitute(logs[k], x),
                          series_exp(series_scale(delta, mon(-k, lam=1))))
        for j in range(m-k+1):
            out[j+k] = plus(out[j+k], scaled(term[j], lam=-1))
    return out

def graph_evidence():
    data = []
    for n in range(5):
        histogram = [0]*(2*n+1)
        for graph in range(1 << (n*n)):
            used_left, used_right = 0, 0
            for i in range(n):
                row = (graph >> (n*i)) & ((1 << n)-1)
                if row:
                    used_left |= 1 << i
                used_right |= row
            isolated = 2*n-used_left.bit_count()-used_right.bit_count()
            histogram[isolated] += 1
        weighted = sum(count*(1 << i) for i, count in enumerate(histogram))
        assert weighted == a(n)
        for k in range(2*n+1):
            moment = sum(count*comb(i, k) for i, count in enumerate(histogram) if i >= k)
            assert F(moment, 1 << (n*n)) == F(sector(n, k), 1 << (n*k))
        data.append(dict(n=n, graphs=1 << (n*n), isolation_histogram=histogram,
                         weighted_count=weighted, all_factorial_moments_exact=True))
    return data

def closure_evidence():
    data = []
    for K in range(1, 5):
        flats = []
        for i in range(K):
            for j in range(K):
                mask = sum(1 << (u*K+v) for u in range(K) for v in range(K)
                           if (i == K-1 or u == i) and (j == K-1 or v == j))
                flats.append(mask)
        closed, obstructed, grid_checks = 0, 0, 0
        boundary_counts = {}
        for table in range(1 << (K*K)):
            union = 0
            for cell, flat in enumerate(flats):
                if table & (1 << cell):
                    union |= flat
            if union != table:
                assert union & ~table
                obstructed += 1
                continue
            closed += 1
            if not (table & (1 << (K*K-1))):
                r = sum(bool(table & (1 << (i*K+K-1))) for i in range(K-1))
                c = sum(bool(table & (1 << ((K-1)*K+j))) for j in range(K-1))
                boundary_counts[(r, c)] = boundary_counts.get((r, c), 0)+1
            for A in range(1, K+3):
                for B in range(1, K+3):
                    product = 1
                    for i in range(K):
                        for j in range(K):
                            if table & (1 << (i*K+j)):
                                factor = (A-i-1)**2 if i < K-1 else 0
                                factor += (B-j-1)**2 if j < K-1 else 0
                                product *= factor
                    expected = bool(table & (1 << ((min(A, K)-1)*K+min(B, K)-1)))
                    assert (product == 0) == expected
                    grid_checks += 1
        assert closed == a(K-1)+1
        n = K-1
        assert boundary_counts == {(r, c): comb(n, r)*comb(n, c)*2**((n-r)*(n-c))
                                   for r in range(n+1) for c in range(n+1)}
        data.append(dict(K=K, all_tables=1 << (K*K), closed=closed,
                         explicit_closure_obstructions=obstructed,
                         zero_polynomial_grid_checks=grid_checks,
                         boundary_cardinality_counts_exact=True))
    return data

def colored_evidence():
    # Enumerate ordinary graphs; each bipartite component has two color choices.
    data = []
    for n in range(7):
        pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
        total, connected = 0, 0
        for mask in range(1 << len(pairs)):
            adj = [[] for _ in range(n)]
            for j, (u, v) in enumerate(pairs):
                if mask & (1 << j):
                    adj[u].append(v)
                    adj[v].append(u)
            colors, components, good = {}, 0, True
            for u in range(n):
                if u in colors:
                    continue
                components += 1
                colors[u] = 0
                stack = [u]
                while stack:
                    v = stack.pop()
                    for w in adj[v]:
                        if w in colors:
                            if colors[w] == colors[v]:
                                good = False
                        else:
                            colors[w] = 1-colors[v]
                            stack.append(w)
            if good:
                total += 1 << components
                if components == 1:
                    connected += 2
        data.append(dict(n=n, ordinary_graphs=1 << len(pairs),
                         named_colored_total=total, named_colored_connected=connected))
    return data

def dyadic(power):
    return F(2**power) if power >= 0 else F(1, 2**(-power))

def exact_inverse(y, sequence):
    if y < sequence[0]:
        return None
    # isqrt(floor(log2 y)) equals floor(sqrt(log2 y)) for rational positive y.
    floor_log = y.numerator.bit_length()-y.denominator.bit_length()
    while dyadic(floor_log) > y:
        floor_log -= 1
    while dyadic(floor_log+1) <= y:
        floor_log += 1
    m = isqrt(floor_log)
    return m-1 if y < sequence[m] else m

def encode(poly):
    return [dict(s=s, lambda_power=lam, coefficient=str(c))
            for (s, lam), c in sorted(poly.items(), reverse=True)]

def main():
    ps = [make_P(k) for k in range(ORDER+1)]
    u = [{}] + ps[1:]
    logs = zero_series(ORDER)
    for j in range(1, ORDER+1):
        logs = series_add(logs, series_scale(series_pow(u, j), mon(F((-1)**(j+1), j))))
    for k in range(1, ORDER+1):
        rhs = plus(ps[k], *(scaled(times(logs[j], ps[k-j]), -F(j, k)) for j in range(1, k)))
        assert logs[k] == rhs
    ds = [{}]
    for m in range(1, ORDER+1):
        delta = ds + [{}]
        residual = exponentiated_residual(delta, ps)
        ds.append(scaled(residual[m], -F(1, 2), s=-1, lam=-1))
        assert all(not p for p in exponentiated_residual(ds, ps))
        assert all(not p for p in logarithmic_residual(ds, logs))
    assert ds[1] == mon(-1, lam=-1)
    assert ds[2] == plus(mon(-F(1,2), s=1, lam=-1), mon(-F(1,2), lam=-1), mon(F(1,2), s=-1, lam=-2))
    assert ds[3] == plus(mon(-F(1,2), s=2, lam=-1), mon(-F(1,3), lam=-1), mon(1, lam=-2), mon(1, s=-1, lam=-2))
    expected_P = [[1], [0,2], [0,-1,3], [0,F(2,3),-5,F(13,3)], [0,-F(1,2),F(41,4),-F(33,2),F(27,4)]]
    expected_L = [[], [0,2], [0,-1,1], [0,F(2,3),-3,1], [0,-F(1,2),F(101,12),-F(15,2),F(19,12)]]
    for k, row in enumerate(expected_P):
        assert ps[k] == plus(*(mon(c, s=j) for j, c in enumerate(row)))
    for k, row in enumerate(expected_L):
        assert logs[k] == plus(*(mon(c, s=j) for j, c in enumerate(row)))
    b = [sum(comb(k,r)*2**(r*(k-r)) for r in range(k+1)) for k in range(ORDER+1)]
    c = [0]
    for k in range(1, ORDER+1):
        c.append(b[k]-sum(comb(k-1,j-1)*c[j]*b[k-j] for j in range(1,k)))
        assert c[k] > 0
        assert max(s for s, lam in ps[k]) == k
        assert max(s for s, lam in logs[k]) == k
        assert max(s for s, lam in ds[k]) == k-1
        assert ps[k].get((k,0)) == F(b[k],factorial(k))
        assert logs[k].get((k,0)) == F(c[k],factorial(k))
        assert {(s,l):q for (s,l),q in ds[k].items() if s==k-1} == mon(-F(c[k],2*factorial(k)),s=k-1,lam=-1)
    values, majorant_checks, threshold_checks = [], 0, 0
    for n in range(MAX_N+1):
        value = a(n)
        assert value == sum(comb(n,r)*comb(n,c)*2**((n-r)*(n-c)) for r in range(n+1) for c in range(n+1))
        sectors = [F(sector(n,k),2**(n*k)) for k in range(2*n+1)]
        assert sum(sectors) == F(value,2**(n*n))
        assert 2**(n*n) <= value <= 2**(n*n+2*n) < 2**((n+1)**2)
        if n:
            assert 2**(n*n) < value+1 < 2**((n+1)**2)
        for k in range(ORDER+1):
            assert evaluate(ps[k],n) == sector(n,k)
        for k, term in enumerate(sectors):
            assert term**4 <= comb(2*n,k)**4 * dyadic(-4*n*k+k*k)
            majorant_checks += 1
        values.append(value)
    probes = {F(0),F(1),F(3,2),F(2),F(5,2)}
    for n in range(1, MAX_N):
        for value in (values[n],values[n]+1,2**(n*n)):
            probes.update((F(value)-F(1,2),F(value),F(value)+F(1,2)))
    for sequence in (values,[x+1 for x in values]):
        for y in sorted(probes):
            answer = max((i for i,x in enumerate(sequence) if x <= y),default=None)
            assert exact_inverse(y,sequence) == answer
            threshold_checks += 1
    graphs, closure, colored = graph_evidence(), closure_evidence(), colored_evidence()
    assert all(row['named_colored_total']==b[row['n']] and row['named_colored_connected']==c[row['n']] for row in colored)
    ratios = []
    for n in (16,32,64):
        for m in range(ORDER):
            tail = F(values[n],2**(n*n))-sum(F(sector(n,k),2**(n*k)) for k in range(m+1))
            first = F(sector(n,m+1),2**(n*(m+1)))
            assert tail >= first > 0
            ratios.append(dict(n=n,M=m,tail_over_first_omitted=str(tail/first)))
    result = dict(order=ORDER,sequence_indices=MAX_N+1,polynomial_values=(MAX_N+1)*(ORDER+1),
                  exact_fourth_power_majorant_checks=majorant_checks,
                  exact_rational_threshold_checks=threshold_checks,
                  exponentiated_inverse_residual_zero=True,log_inverse_residual_zero=True,
                  P=[encode(p) for p in ps],L=[encode(p) for p in logs],D=[encode(p) for p in ds],
                  b=b,c=c,closure=closure,graphs=graphs,colored_graphs=colored,
                  sharp_forward_tail_ratios=ratios,initial_values=[str(v) for v in values])
    with OUT.open('x') as f:
        json.dump(result,f,indent=2,sort_keys=True)
        f.write('\n')
    summary={key:result[key] for key in ('order','sequence_indices','polynomial_values','exact_fourth_power_majorant_checks','exact_rational_threshold_checks','exponentiated_inverse_residual_zero','log_inverse_residual_zero','b','c')}
    summary.update(closure_tables=sum(r['all_tables'] for r in closure),
                   zero_polynomial_grid_checks=sum(r['zero_polynomial_grid_checks'] for r in closure),
                   bipartite_graphs=sum(r['graphs'] for r in graphs),
                   ordinary_graphs=sum(r['ordinary_graphs'] for r in colored))
    print(json.dumps(summary,indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
