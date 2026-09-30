#!/usr/bin/env python3
"""Exact finite checks and high-precision illustrations for the accompanying article.

The algebra uses fractions.Fraction, including divided-power log polynomials.
The numerical checks use mpmath and are not directed-rounding certificates.
No network access, repository checkout, or optional CAS is needed.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path
import json
import platform
import random
import mpmath as mp

Poly = tuple[F, ...]
Series = dict[F, Poly]
ZERO: Poly = ()
ONE: Poly = (F(1),)


def trim(p) -> Poly:
    p = list(map(F, p))
    while p and not p[-1]:
        p.pop()
    return tuple(p)


def add(p: Poly, q: Poly) -> Poly:
    return trim((p[k] if k < len(p) else 0) + (q[k] if k < len(q) else 0)
                for k in range(max(len(p), len(q))))


def scale(p: Poly, c) -> Poly:
    return trim(F(c) * a for a in p)


def derivative(p: Poly) -> Poly:
    return p[1:] if len(p) > 1 else ZERO


def multiply(p: Poly, q: Poly) -> Poly:
    if not p or not q:
        return ZERO
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] += comb(i+j, i) * a * b
    return trim(out)


def T(b: F, p: Poly) -> Poly:
    if not p:
        return ZERO
    if not b:
        return (F(0),) + p
    out, q, k = ZERO, p, 0
    while q:
        out = add(out, scale(q, F((-1)**k) / b**(k+1)))
        q, k = derivative(q), k+1
    return out


def pnorm(p: Poly) -> F:
    return sum(map(abs, p), F(0))


def sadd(a: Series, b: Series, factor=F(1)) -> Series:
    out = dict(a)
    for s, p in b.items():
        q = add(out.get(s, ZERO), scale(p, factor))
        if q:
            out[s] = q
        else:
            out.pop(s, None)
    return out


def smul(a: Series, b: Series) -> Series:
    out: Series = {}
    for s, p in a.items():
        for t, q in b.items():
            out = sadd(out, {s+t: multiply(p, q)})
    return out


def sd(a: Series) -> Series:
    return {s: q for s, p in a.items() if (q := add(scale(p, s), derivative(p)))}


def matzero(r: int):
    return [[{} for _ in range(r)] for _ in range(r)]


def eye(r: int):
    out = matzero(r)
    for i in range(r):
        out[i][i] = {F(0): ONE}
    return out


def madd(a, b, factor=F(1)):
    return [[sadd(x, y, factor) for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mmul(a, b):
    r = len(a)
    out = matzero(r)
    for i in range(r):
        for j in range(r):
            for k in range(r):
                out[i][j] = sadd(out[i][j], smul(a[i][k], b[k][j]))
    return out


def paths(i, j, edges):
    if i == j:
        yield (i,)
    else:
        for k in range(i+1, j+1):
            if (i, k) in edges:
                for suffix in paths(k, j, edges):
                    yield (i,) + suffix


def path_kernel(path, exponents, lam):
    q, suffix_sum = ONE, F(0)
    for k in reversed(range(len(exponents))):
        suffix_sum += exponents[k]
        beta = suffix_sum - (lam[path[k]] - lam[path[-1]])
        q = T(beta, q)
    return q


def h_paths(lam, edges):
    r, out = len(lam), eye(len(lam))
    for i in range(r):
        for j in range(i+1, r):
            for path in paths(i, j, edges):
                es = list(zip(path, path[1:]))
                for tup in product(*(list(edges[e].items()) for e in es)):
                    exps = [a for a, _ in tup]
                    coeff = F(1)
                    for _, a in tup:
                        coeff *= a
                    q = scale(path_kernel(path, exps, lam), coeff)
                    out[i][j] = sadd(out[i][j], {sum(exps, F(0)): q})
    return out


def as_matrix(r, edges):
    a = matzero(r)
    for (i, j), data in edges.items():
        a[i][j] = {s: (c,) for s, c in data.items() if c}
    return a


def h_recursive(lam, edges):
    r, h = len(lam), eye(len(lam))
    a = as_matrix(r, edges)
    for span in range(1, r):
        for i in range(r-span):
            j = i+span
            rhs = dict(a[i][j])
            for k in range(i+1, j):
                rhs = sadd(rhs, smul(a[i][k], h[k][j]))
            h[i][j] = {s: T(s-(lam[i]-lam[j]), p) for s, p in rhs.items()}
    return h


def normal_form(lam, edges):
    r, p, rr = len(lam), eye(len(lam)), matzero(len(lam))
    a = as_matrix(r, edges)
    for span in range(1, r):
        for i in range(r-span):
            j = i+span
            rhs = dict(a[i][j])
            for k in range(i+1, j):
                rhs = sadd(rhs, smul(a[i][k], p[k][j]))
                rhs = sadd(rhs, smul(p[i][k], rr[k][j]), -1)
            rho = lam[i]-lam[j]
            for s, q in rhs.items():
                assert len(q) == 1
                if s == rho:
                    rr[i][j][s] = q
                else:
                    p[i][j][s] = scale(q, 1/(s-rho))
    return p, rr


def scalar_mmul(a, b):
    r = len(a)
    return [[sum((a[i][k]*b[k][j] for k in range(r)), F(0))
             for j in range(r)] for i in range(r)]


def normal_log_factor(lam, rr):
    r = len(lam)
    b = [[sum((p[0] for p in rr[i][j].values()), F(0))
          for j in range(r)] for i in range(r)]
    power = [[F(i == j) for j in range(r)] for i in range(r)]
    out = matzero(r)
    for k in range(r):
        for i in range(r):
            for j in range(r):
                if power[i][j]:
                    poly = (F(0),)*k + (power[i][j],)
                    out[i][j] = sadd(out[i][j], {lam[i]-lam[j]: poly})
        power = scalar_mmul(power, b)
    assert not any(x for row in power for x in row)
    return out


def unipotent_inverse(h):
    r = len(h)
    n, ans, power = madd(h, eye(r), -1), eye(r), eye(r)
    for k in range(1, r):
        power = mmul(power, n)
        ans = madd(ans, power, (-1)**k)
    assert mmul(ans, h) == eye(r)
    return ans


def exact_checks():
    rng = random.Random(20260929)
    counts = {"scalar_inverse_checks": 0, "kernel_degree_checks": 0,
              "finite_systems": 0, "differential_entry_checks": 0,
              "gauge_entry_checks": 0, "connection_entry_checks": 0,
              "weighted_path_checks": 0, "chain_formula_checks": 0}
    for b in map(F, [-2, F(-1,3), 0, F(1,4), 3]):
        for deg in range(7):
            for _ in range(3):
                p = trim(F(rng.randint(-5,5), rng.randint(1,4)) for _ in range(deg+1))
                q = T(b, p)
                assert add(scale(q, b), derivative(q)) == p
                if not b and q:
                    assert q[0] == 0
                counts['scalar_inverse_checks'] += 1
    for m in range(1, 8):
        for _ in range(30):
            betas = [rng.choice([F(0), F(-2), F(1,3), F(-1,5), F(4)]) for _ in range(m)]
            q = ONE
            for b in reversed(betas):
                q = T(b, q)
            z = betas.count(F(0))
            leading = F(1)
            for b in betas:
                if b:
                    leading /= b
            assert len(q)-1 == z and q[-1] == leading
            counts['kernel_degree_checks'] += 1
    systems = []
    exponent_pool = [F(1,2), F(1), F(3,2), F(2), F(3)]
    for r in range(2, 7):
        for case in range(6):
            lam = tuple(F(rng.randint(-2, 5)) for _ in range(r))
            edges = {}
            for i in range(r):
                for j in range(i+1, r):
                    if j == i+1 or rng.random() < .45:
                        edges[i,j] = {s: F(rng.choice([-3,-2,-1,1,2,3]), rng.randint(1,3))
                                      for s in rng.sample(exponent_pool, 2)}
            a, h = as_matrix(r, edges), h_paths(lam, edges)
            assert h == h_recursive(lam, edges)
            ah = mmul(a, h)
            for i in range(r):
                for j in range(r):
                    residual = sadd(sd(h[i][j]), {s:scale(q,lam[i]-lam[j]) for s,q in h[i][j].items()}, -1)
                    assert not sadd(residual, ah[i][j], -1)
                    counts['differential_entry_checks'] += 1
            p, rr = normal_form(lam, edges)
            ap, pr = mmul(a, p), mmul(p, rr)
            for i in range(r):
                for j in range(r):
                    residual = sadd(sd(p[i][j]), {s:scale(q,lam[i]-lam[j]) for s,q in p[i][j].items()}, -1)
                    residual = sadd(sadd(residual, ap[i][j], -1), pr[i][j])
                    assert not residual
                    counts['gauge_entry_checks'] += 1
            hstd = mmul(p, normal_log_factor(lam, rr))
            connection = mmul(unipotent_inverse(hstd), h)
            for i in range(r):
                for j in range(r):
                    for s, q in connection[i][j].items():
                        assert s == lam[i]-lam[j] and len(q) == 1
                    counts['connection_entry_checks'] += 1
            for i in range(r):
                for j in range(i+1,r):
                    for path in paths(i,j,edges):
                        es = list(zip(path,path[1:]))
                        bound, out = F(0), {}
                        input_norm_product = F(1)
                        for edge in es:
                            input_norm_product *= sum((abs(c)*(1+s) for s,c in edges[edge].items()), F(0))
                        for tup in product(*(list(edges[e].items()) for e in es)):
                            exps = [s for s,_ in tup]
                            q = path_kernel(path,exps,lam)
                            weightprod, coeff = F(1), F(1)
                            for s,c in tup:
                                weightprod *= 1+s
                                coeff *= c
                            bound = max(bound, pnorm(q)/weightprod)
                            out = sadd(out, {sum(exps,F(0)):scale(q,coeff)})
                        assert sum((pnorm(q) for q in out.values()),F(0)) <= bound*input_norm_product
                        counts['weighted_path_checks'] += 1
            counts['finite_systems'] += 1
            systems.append({"dimension":r,"case":case,"spectrum":list(map(str,lam)),"edges":len(edges)})
    for q in range(7):
        for n in [2,3,7,19]:
            p = (F(0),)*q + (F(1),)
            expected = tuple(-F(n)**(q-j+1) for j in range(q+1))
            assert T(-F(1,n),p) == expected
            counts['chain_formula_checks'] += 1
    for r in range(2,8):
        lam = tuple(F(r-i-1) for i in range(r))
        edges = {(0,1):{F(1)-F(1,n):F(1,n*n) for n in [2,3,5]}}
        for i in range(1,r-1):
            edges[i,i+1] = {F(1):F(1)}
        p,rr = normal_form(lam,edges)
        for j in range(1,r):
            expected = {F(j)-F(1,n):(-F(n)**j/F(n*n),) for n in [2,3,5]}
            assert p[0][j] == expected
            counts['chain_formula_checks'] += 1
    return counts, systems


def positive_sum(term, ratio_bound, dps=55):
    total = mp.mpf(0)
    for k in range(500):
        a = term(k)
        total += a
        r = ratio_bound(k)
        if r < 1:
            error = abs(a)*r/(1-r)
            if error < mp.mpf(10)**(-dps) * max(1, abs(total)):
                return total, error, k+1
    raise ArithmeticError('Positive series did not meet the requested tail bound.')


def numerical_checks():
    mp.mp.dps = 75
    cases, table = [], []
    for q,pstr,cstr,tint in product([0,1,3,5], ['1.5','2','2.5','6.5'], ['0.5','1','2'], [20,80]):
        p,c,t = mp.mpf(pstr),mp.mpf(cstr),mp.mpf(tint)
        N = int(c*t)
        e, e_tail, ek = positive_sum(
            lambda k: t**(p-1+k)*mp.zeta(p+k,N)/(mp.factorial(q)*mp.factorial(k)*(q+k+1)),
            lambda k: t/(N*(k+1)))
        integral, i_tail, ik = positive_sum(
            lambda k: c**(1-p-k)/(mp.factorial(q)*mp.factorial(k)*(q+k+1)*(p+k-1)),
            lambda k: 1/(c*(k+1)))
        psi = mp.quad(lambda u: mp.exp(u/c)*u**q, [0,1])/mp.factorial(q)
        psi1 = mp.quad(lambda u: mp.exp(u/c)*u**(q+1), [0,1])/mp.factorial(q)
        g = c**(-p)*psi
        minus_gp = p*c**(-p-1)*psi + c**(-p-2)*psi1
        approx = integral + g/(2*t)
        bound = minus_gp/(8*t*t)
        tol = mp.mpf('1e-48')
        assert integral-tol <= e <= integral+g/t+tol
        assert -tol <= e-approx <= bound+tol
        row = {"q":q,"p":pstr,"c":cstr,"t":tint,"N":N,
               "scaled_tail":mp.nstr(e,25),"integral":mp.nstr(integral,25),
               "trapezoid_approximation":mp.nstr(approx,25),
               "observed_error":mp.nstr(e-approx,15),"proved_error_bound":mp.nstr(bound,15),
               "series_terms":[ek,ik],"analytic_series_tail_bounds":[mp.nstr(e_tail,8),mp.nstr(i_tail,8)]}
        cases.append(row)
        if pstr=='2.5' and cstr=='1':
            table.append(row)
    return cases, table


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    # ed. (2026-09-29): the default output is build/recheck; writing the recorded results/ needs --overwrite-recorded.
    parser.add_argument('--outdir',type=Path,default=Path(__file__).resolve().parents[1]/'build'/'recheck')
    parser.add_argument('--overwrite-recorded',action='store_true',
                        help='allow writing the recorded results/ (verification.json and the table the article inputs)')
    args = parser.parse_args()
    recorded = Path(__file__).resolve().parents[1]/'results'
    if args.outdir.resolve() == recorded.resolve() and not args.overwrite_recorded:
        parser.error('refusing to overwrite the recorded results/; '
                     'pass --overwrite-recorded or choose another --outdir')
    args.outdir.mkdir(parents=True,exist_ok=True)
    counts,systems = exact_checks()
    cases,table = numerical_checks()
    result = {"status":"all checks passed","seed":20260929,"python":platform.python_version(),
              "mpmath":mp.__version__,"working_decimal_digits":75,
              "exact_counts":counts,"exact_systems":systems,"numerical_cases":len(cases),
              "numerical_checks_are_interval_certificates":False,"crossover_cases":cases}
    # ed. (2026-09-29): newline='\n' so both outputs are LF on Windows too
    (args.outdir/'verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    lines = [r'\begin{tabular}{rrlll}',r'\toprule',
             r'$q$ & $t$ & Scaled tail $E$ & $I+g/(2t)$ & Error bound \\',r'\midrule']
    for row in table:
        fmt = lambda key: mp.nstr(mp.mpf(row[key]),9)
        lines.append(f"{row['q']} & {row['t']} & {fmt('scaled_tail')} & {fmt('trapezoid_approximation')} & {fmt('proved_error_bound')} \\\\")
    lines += [r'\bottomrule',r'\end{tabular}']
    (args.outdir/'crossover_table.tex').write_text('\n'.join(lines)+'\n',encoding='utf-8',newline='\n')
    summary = {'status':result['status'],**counts,'numerical_cases':len(cases),'python':result['python'],'mpmath':result['mpmath']}
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
