"""Regenerate numerical tables, exact Perron certificates, and sequence data.

Requires numpy, scipy; symbolic generating functions additionally require sympy.
The independent verifier is standard-library-only (verify.py).
"""
from __future__ import annotations
import argparse
import csv
import json
from math import ceil, exp, floor, log, sqrt
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigs
from model import c, counts, edges

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


def matrix_at(m: int, comp: str, x: float):
    ss, es = edges(m, comp)
    rows, cols, vals = zip(*[(a, b, mult*x**k) for a, b, k, mult in es])
    return coo_matrix((vals, (rows, cols)), shape=(len(ss), len(ss))).tocsr()


def perron(m: int, comp: str, x: float, vector: bool = False):
    matrix = matrix_at(m, comp, x)
    if matrix.shape[0] <= 24:
        vals, vecs = np.linalg.eig(matrix.toarray())
        i = int(np.argmax(vals.real))
        val, vec = vals[i].real, vecs[:, i].real
    else:
        vals, vecs = eigs(matrix, k=1, which="LR", tol=1e-12,
                          v0=np.ones(matrix.shape[0]), maxiter=30000)
        val, vec = vals[0].real, vecs[:, 0].real
    if vector:
        if np.sum(vec) < 0:
            vec = -vec
        vec = vec / np.max(vec)
        if np.min(vec) <= 0:
            raise ArithmeticError("Perron vector was not numerically positive")
        return float(val), vec
    return float(val)


def root(m: int, comp: str) -> float:
    return brentq(lambda x: perron(m, comp, x)-1, 0.25, 1.01,
                  xtol=2e-14, rtol=1e-14)


def exact_sign(m: int, comp: str, num: int, den: int, vector: list[int], lower: bool) -> bool:
    ss, es = edges(m, comp)
    powers = [num**k * den**(m-k) for k in range(m+1)]
    vals = [0] * len(ss)
    for a,b,k,mult in es:
        vals[a] += mult * powers[k] * vector[b]
    rhs = [den**m * v for v in vector]
    return all(a < b if lower else a > b for a,b in zip(vals,rhs))


def certificate(m: int, comp: str, r: float) -> dict:
    # The enclosing rationals are intentionally much wider than machine epsilon.
    den = 10**10
    lo, hi = floor(r*den)-3, ceil(r*den)+3
    _, v = perron(m, comp, r, vector=True)
    vector = [max(1, int(round(float(x)*10**18))) for x in v]
    for _ in range(8):
        if exact_sign(m, comp, lo, den, vector, True) and \
           exact_sign(m, comp, hi, den, vector, False):
            return {"m":m, "component":comp,
                    "lower_radius":{"numerator":lo,"denominator":den,"vector":vector},
                    "upper_radius":{"numerator":hi,"denominator":den,"vector":vector}}
        lo -= 10
        hi += 10
    raise ArithmeticError(f"Could not certify m={m} component={comp}")


def normalized_catalans(n: int) -> np.ndarray:
    a = np.ones(n+1, dtype=float)
    if n:
        j = np.arange(n, dtype=float)
        a[1:] = np.cumprod((2*j+1)/(2*j+4))
    return a


def scalar_bound(m: int, d: int | None = None) -> float:
    """Growth bound from R_m (d=None) or K_{m,d}; floating point only."""
    if d is None:
        k = np.arange(1, m+1, dtype=float)
        b = 0.25 * normalized_catalans(m-1)
        b[0] += 0.25
    else:
        end = m-d
        if end < 2:
            return 1.0
        k = np.arange(1, end+1, dtype=float)
        b = np.zeros(end)
        b[0] = .25
        sz = k[1:]
        base = normalized_catalans(end-2)/16
        ratio = np.ones(end-1)
        coeff = np.zeros(end-1)
        for j in range(1, d+1):
            mask = sz >= j+1
            if j >= 2:
                # first_count(k,j) / first_count(k,1)
                ratio *= np.divide(sz-j, 2*sz-j-2,
                                   out=np.zeros_like(sz), where=(2*sz-j-2)!=0)
            coeff[mask] += j*ratio[mask]
        b[1:] = base*coeff
    def f(t: float) -> float:
        return float(np.dot(b, np.exp(t*k/m))-1)
    hi = max(2.0, log(m)+2*log(max(log(m),1.0))+6)
    while f(hi) < 0:
        hi *= 1.5
    t = brentq(f, 0, hi, xtol=5e-13)
    return 4*exp(-t/m)


def symbolic_gf(m: int) -> dict:
    import sympy as sp
    from sympy.polys.matrices import DomainMatrix
    from sympy.polys.domains import QQ
    x = sp.Symbol("x")
    ss, es = edges(m)
    M = sp.eye(len(ss))
    for a,b,k,mult in es:
        M[a,b] -= mult*x**k
    # Exact polynomial-domain fraction-free inversion. This is not data fitting.
    dm = DomainMatrix.from_Matrix(M).convert_to(QQ.poly_ring(x))
    num, den = dm.inv_den()
    numer = num.to_Matrix()
    denom = den.as_expr()
    ii = ss.index((None,None))
    d0 = sp.Poly(denom, x).nth(0)
    common_den = sp.Poly(denom/d0, x)
    all_num = [sp.Poly(x*sum(numer[i,j] for j in range(len(ss)))/d0, x)
               for i in range(len(ss))]
    def encode(poly):
        assert all(v.q == 1 for v in poly.all_coeffs())
        return [int(poly.nth(j)) for j in range(poly.degree()+1)]
    certificate_data = {"m":m, "common_denominator":encode(common_den),
                        "state_numerators":[encode(poly) for poly in all_num]}
    (DATA/f"symbolic_certificate_m{m}.json").write_text(json.dumps(certificate_data,indent=2)+"\n")
    val = sp.cancel(1+x*sum(numer[ii,j] for j in range(len(ss)))/denom)
    pp, qq = map(sp.Poly, sp.fraction(val))
    pp,qq = sp.Poly(pp,x),sp.Poly(qq,x)
    norm = qq.nth(0)
    pp,qq = sp.Poly(pp.as_expr()/norm,x),sp.Poly(qq.as_expr()/norm,x)
    assert all(v.q==1 for v in list(pp.all_coeffs())+list(qq.all_coeffs()))
    return {"m":m, "numerator_ascending":[int(pp.nth(j)) for j in range(pp.degree()+1)],
            "denominator_ascending":[int(qq.nth(j)) for j in range(qq.degree()+1)],
            "numerator":str(pp.as_expr()), "denominator_factored":str(sp.factor(qq.as_expr()))}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-m", type=int, default=20)
    ap.add_argument("--symbolic-max", type=int, default=4)
    ap.add_argument("--large-scalars", action="store_true")
    args = ap.parse_args()
    DATA.mkdir(exist_ok=True)
    certs, table = [], []
    for m in range(2,args.max_m+1):
        ru,rv = root(m,"U"),root(m,"V")
        certs += [certificate(m,"U",ru),certificate(m,"V",rv)]
        au,av=1/ru,1/rv
        a=max(au,av)
        table.append({"m":m,"lambda_U":au,"lambda_V":av,"alpha":a,
                      "dominant":"U" if au>av else "V",
                      "majorant_upper":scalar_bound(m),
                      "block_d1_lower":scalar_bound(m,1),
                      "centered_remainder":m*(4-a)-2*log(m)-4*log(log(m))})
        print(m,au,av,flush=True)
    (DATA/"perron_certificates.json").write_text(json.dumps(certs,indent=2)+"\n")
    with (DATA/"growth_constants.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=table[0].keys());w.writeheader();w.writerows(table)
    with (DATA/"sequences.csv").open("w",newline="") as f:
        w=csv.writer(f);w.writerow(["n"]+[f"a_m{m}" for m in range(1,13)])
        all_counts=[counts(m,200) for m in range(1,13)]
        for n in range(201):
            w.writerow([n]+[aa[n] for aa in all_counts])
    gg=[]
    for m in range(1,args.symbolic_max+1):
        print("symbolic",m,flush=True)
        gg.append(symbolic_gf(m))
    (DATA/"generating_functions.json").write_text(json.dumps(gg,indent=2)+"\n")
    if args.large_scalars:
        table=[]
        for m in [10,20,50,100,200,500,1000,3000,10000,30000,100000,300000,1000000]:
            vals={"m":m,"majorant_upper":scalar_bound(m)}
            for d in (1,2,4,8):
                vals[f"block_d{d}_lower"]=scalar_bound(m,d)
            upper_a=vals["majorant_upper"]
            lower_a=max(vals[f"block_d{d}_lower"] for d in (1,2,4,8))
            shift=2*log(m)+4*log(log(m))
            vals["remainder_lower_bound"]=m*(4-upper_a)-shift
            vals["remainder_upper_bound"]=m*(4-lower_a)-shift
            table.append(vals)
            print("scalar",m,lower_a,upper_a,flush=True)
        with (DATA/"large_m_scalar_bounds.csv").open("w",newline="") as f:
            w=csv.DictWriter(f,fieldnames=table[0].keys());w.writeheader();w.writerows(table)


if __name__=="__main__":
    main()
