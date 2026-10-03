#!/usr/bin/env python3
"""Reproduce finite checks for At the Critical Line.

Exact symbolic tests and high-precision numerical diagnostics only.  This
program is not an interval certificate or a formal proof of an infinite
continued-fraction construction.  It uses no network or external data.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
from pathlib import Path
from typing import Sequence

import mpmath as mp
import sympy as sp

EXACT: list[str] = []
NUMERIC: list[dict[str, str]] = []


def exact(name: str, condition: object) -> None:
    if not bool(condition):
        raise AssertionError(name)
    EXACT.append(name)


def numeric(name: str, value: mp.mpf, bound: mp.mpf) -> None:
    if not mp.isfinite(value) or not value <= bound:
        raise AssertionError(f"{name}: {value} > {bound}")
    NUMERIC.append({"name": name, "value": mp.nstr(value, 16),
                    "bound": mp.nstr(bound, 16)})


def convergents(partials: Sequence[int]) -> list[tuple[int, int]]:
    pm2, pm1, qm2, qm1 = 0, 1, 1, 0
    out = []
    for a in partials:
        p, q = a * pm1 + pm2, a * qm1 + qm2
        out.append((p, q))
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q
    return out


def richardson_weights(order: int) -> list[sp.Rational]:
    return [sp.Rational((-1)**(order + 1 - ell) * ell**order,
                        math.factorial(ell - 1) * math.factorial(order + 1 - ell))
            for ell in range(1, order + 2)]


def symbolic_checks() -> None:
    for m in range(1, 9):
        weights = richardson_weights(m)
        for j in range(m + 1):
            moment = sum(w / sp.Integer(ell)**j
                         for ell, w in enumerate(weights, 1))
            exact(f"Richardson m={m}, moment={j}", moment == int(j == 0))
    prefix = [1, 4, 3, 2, 8, 6, 1, 12, 2, 7, 4, 10]
    conv = convergents(prefix)
    for k, (p, q) in enumerate(conv):
        pp, qp = conv[k-1] if k else (1, 0)
        exact(f"determinant k={k}", p * qp - pp * q == (-1)**(k-1))
        a_next = k + 3
        theta = sp.Rational(2, 7)
        tau = a_next + theta
        alpha = (p * tau + pp) / (q * tau + qp)
        delta = sp.factor(q * alpha - p)
        exact(f"signed complete-quotient identity k={k}",
              delta == (-1)**k / (q * tau + qp))
        exact(f"inverse-error identity k={k}",
              1 / abs(delta) == a_next*q + qp + theta*q)
    even_conv = convergents([1] + [2 + 2*(k % 5) for k in range(30)])
    for k, (p, q) in enumerate(even_conv):
        exact(f"all-even positive critical sign k={k}",
              (-1)**(p+q+k) == 1)
    alternating_conv = convergents([1, 2, 3] + [4]*28)
    for k, (p, q) in enumerate(alternating_conv):
        if k >= 1:
            exact(f"alternating critical sign k={k}",
                  (-1)**(p+q+k) == (-1)**(k+1))
    eps = sp.Symbol('eps', positive=True)
    for d in range(2, 8):
        centers = [-1] + list(range(1, d))
        nodes = [1 + c*eps for c in centers]
        den = sp.prod(nodes[0]-node for node in nodes[1:])
        for m in [d-2, d-1, d]:
            expression = eps**m/den
            expected = eps**(m-d+1)/sp.prod(centers[0]-c for c in centers[1:])
            exact(f"hinge scaling d={d}, m={m}", sp.simplify(expression-expected) == 0)
    # Polynomial reproduction for a divided difference, including degree r-1.
    for r in range(2, 8):
        nodes = [sp.Rational(j*j+1, j+2) for j in range(r)]
        for k in range(r):
            dd = sum(nodes[i]**k / sp.prod(nodes[i]-nodes[j]
                     for j in range(r) if j != i) for i in range(r))
            exact(f"divided-difference r={r}, monomial={k}", dd == int(k == r-1))
    t, z, T = sp.symbols('t z T', nonzero=True)
    for m in range(1, 7):
        jet = sum(sp.binomial(m,j)*T**(-j)*sp.diff(sp.exp(-z*t),z,j)
                  for j in range(m+1))
        exact(f"weighted derivative identity m={m}",
              sp.simplify(jet-(1-t/T)**m*sp.exp(-z*t)) == 0)


def residue_nodes(periods: Sequence[mp.mpf], degree: int,
                  cutoff: mp.mpf) -> list[tuple[mp.mpf, mp.mpf]]:
    """Simple poles only; test values approximate specified irrational ratios."""
    if degree < len(periods) or any(w <= 0 for w in periods):
        raise ValueError("Require positive periods and degree >= number of lattices")
    out = []
    for j, w in enumerate(periods):
        for n in range(1, int(mp.ceil(w*cutoff))):
            node = n/w
            if node >= cutoff:
                continue
            denominator = mp.pi*w
            for k, wk in enumerate(periods):
                if k != j:
                    phase = wk*node
                    if phase == mp.nint(phase):
                        raise ValueError(
                            "Coincident pole or gap unresolved at current precision; "
                            "use confluent residues or increase precision")
                    denominator *= mp.sin(mp.pi*phase)
            if denominator == 0:
                raise ValueError("Coincident pole: simple-residue formula is invalid")
            coeff = (-1)**n * node**degree / denominator
            out.append((node, coeff))
    return sorted(out, key=lambda pair: pair[0])


def jet(nodes: Sequence[tuple[mp.mpf,mp.mpf]], z: mp.mpf,
        order: int) -> mp.mpf:
    return mp.fsum(c*(-a)**order*mp.exp(-a*z) for a,c in nodes)


def riesz(nodes: Sequence[tuple[mp.mpf,mp.mpf]], z: mp.mpf,
          cutoff: mp.mpf, order: int) -> mp.mpf:
    return mp.fsum(c*mp.exp(-a*z)*(1-a/cutoff)**order
                   for a,c in nodes if a < cutoff)


def accelerated(nodes: Sequence[tuple[mp.mpf,mp.mpf]], z: mp.mpf,
                cutoff: mp.mpf, order: int) -> mp.mpf:
    return mp.fsum(mp.mpf(int(w.p))/int(w.q)*riesz(nodes,z,ell*cutoff,order)
                   for ell,w in enumerate(richardson_weights(order),1))


def tex_number(value: mp.mpf, digits: int=5) -> str:
    text = mp.nstr(value, digits, min_fixed=-2, max_fixed=3)
    if 'e' in text:
        mant, exp = text.split('e')
        return rf"{mant}\times 10^{{{int(exp)}}}"
    return text


def write_csv(path: Path, fields: list[str], rows: list[dict[str, str]]) -> None:
    with path.open('w', encoding='utf-8', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)


def numerical_checks(outdir: Path, precision: int) -> None:
    mp.mp.dps = precision
    rows, tex_rows = [], []
    for d, periods, degree, order in [
            (2,[mp.mpf(1),mp.sqrt(2)],2,1),
            (3,[mp.mpf(1),mp.sqrt(2),mp.sqrt(3)],3,2)]:
        z = mp.mpf('0.8')
        nodes = residue_nodes(periods,degree,mp.mpf(260))
        short = [(a,c) for a,c in nodes if a < 220]
        derivatives = [jet(nodes,z,j) for j in range(order+1)]
        numeric(f"reference cutoff comparison d={d}",
                abs(derivatives[0]-jet(short,z,0)),mp.mpf('1e-63'))
        for cutoff_int in [8,12,16,24,32]:
            cutoff=mp.mpf(cutoff_int)
            raw=riesz(nodes,z,cutoff,order)
            polynomial=mp.fsum(mp.binomial(order,j)*derivatives[j]/cutoff**j
                              for j in range(order+1))
            remainder=abs(raw-polynomial)
            acc=accelerated(nodes,z,cutoff,order)
            error=abs(acc-derivatives[0])
            scale=cutoff**(degree-order)*mp.exp(-z*cutoff)
            # Deliberately loose consistency diagnostics, not certified constants.
            numeric(f"Riesz jet remainder d={d}, T={cutoff_int}",remainder/scale,mp.mpf('10000'))
            numeric(f"accelerated remainder d={d}, T={cutoff_int}",error/scale,mp.mpf('10000'))
            rows.append({"d":str(d),"D":str(degree),"m":str(order),"T":str(cutoff_int),
                         "raw_error":mp.nstr(abs(raw-derivatives[0]),18),
                         "jet_remainder":mp.nstr(remainder,18),
                         "accelerated_error":mp.nstr(error,18),
                         "scaled_accelerated_error":mp.nstr(error/scale,18)})
            tex_rows.append(f"{d} & {order} & {cutoff_int} & ${tex_number(abs(raw-derivatives[0]))}$ & "
                            f"${tex_number(remainder)}$ & ${tex_number(error)}$ \\\\")
    write_csv(outdir/'riesz.csv',list(rows[0]),rows)
    (outdir/'riesz_table.tex').write_text(
        r'\begin{tabular}{rrrlll}'+'\n'+r'\toprule'+'\n'+
        r'$d$&$m$&$T$&$|\Riesz_T^{(m)}-\Ssum|$&$|\Riesz_T^{(m)}-Q_T|$&$|\Accel_T^{(m)}-\Ssum|$\\'+'\n'+
        r'\midrule'+'\n'+'\n'.join(tex_rows)+'\n'+r'\bottomrule'+'\n'+r'\end{tabular}'+'\n',
        encoding='utf-8',newline='\n')  # ed. (2026-09-29): LF on Windows too

    collision_rows, collision_tex=[],[]
    z=mp.mpf('1.7')
    for k in [4,8,16,32]:
        vals={}
        for sign in [-1,1]:
            alpha=mp.mpf(3)/2+sign*mp.sqrt(2)*mp.power(10,-k)
            nodes=residue_nodes([mp.mpf(1),alpha],2,mp.mpf(2))
            vals[sign]=[riesz(nodes,z,mp.mpf(2),m) for m in range(3)]
            collision_rows.append({"k":str(k),"side":str(sign),
                                   **{f"R_{m}":mp.nstr(vals[sign][m],24) for m in range(3)}})
        collision_tex.append(f"{k} & ${tex_number(vals[1][0])}$ & ${tex_number(vals[-1][1],7)}$ & "
                             f"${tex_number(vals[1][1],7)}$ & ${tex_number(abs(vals[1][2]-vals[-1][2]))}$ \\\\")
        numeric(f"second-order continuity diagnostic k={k}",
                abs(vals[1][2]-vals[-1][2]),mp.mpf(100)*mp.power(10,-k))
    write_csv(outdir/'cutoff_collision.csv',list(collision_rows[0]),collision_rows)
    (outdir/'collision_table.tex').write_text(
        r'\begin{tabular}{r@{\qquad}llll}'+'\n'+r'\toprule'+'\n'+
        r'$k$&$P_{2,+}$&$\Riesz_{2,-}^{(1)}$&$\Riesz_{2,+}^{(1)}$&$|\Riesz_{2,+}^{(2)}-\Riesz_{2,-}^{(2)}|$\\'+'\n'+
        r'\midrule'+'\n'+'\n'.join(collision_tex)+'\n'+r'\bottomrule'+'\n'+r'\end{tabular}'+'\n',
        encoding='utf-8',newline='\n')  # ed. (2026-09-29): LF on Windows too

    # Exact collision scaling constant for the actual d-lattice sine kernels.
    eps=mp.sqrt(2)*mp.mpf('1e-14')
    for d in range(2,7):
        centers=[-1]+list(range(1,d))
        periods=[1/(1+eps*c) for c in centers]
        nodes=residue_nodes(periods,d,mp.mpf(1))
        if len(nodes)!=1:
            raise AssertionError("collision test should retain exactly one node")
        constant=-mp.exp(-1)/(mp.pi**d*mp.fprod(c+1 for c in centers[1:]))
        for m in [d-2,d-1,d]:
            scaled=riesz(nodes,mp.mpf(1),mp.mpf(1),m)/eps**(m-d+1)
            numeric(f"sharp sine-kernel collision d={d}, m={m}",
                    abs(scaled/constant-1),mp.mpf('1e-10'))

    # Finite Legendre classification (illustration, not a proof).
    alpha=mp.sqrt(2)
    convset=set(convergents([1]+[2]*20))
    for n in range(1,501):
        p=int(mp.nint(n*alpha))
        if abs(n*alpha-p)<mp.mpf(1)/(2*n):
            g=math.gcd(p,n)
            numeric(f"finite Legendre test n={n}",
                    mp.mpf(0 if (p//g,n//g) in convset else 1),mp.mpf(0))


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    # ed. (2026-09-29): the default output is build/results (as build.sh and the Makefile pass);
    # writing the recorded results/ needs --overwrite-recorded.
    parser.add_argument('--outdir',type=Path,default=Path(__file__).resolve().parent/'build'/'results')
    parser.add_argument('--precision',type=int,default=110)
    parser.add_argument('--overwrite-recorded',action='store_true',
                        help='allow writing the recorded results/ (including the two tables the article inputs)')
    args=parser.parse_args()
    if args.outdir.resolve()==(Path(__file__).resolve().parent/'results').resolve() and not args.overwrite_recorded:
        parser.error('refusing to overwrite the recorded results/; '
                     'pass --overwrite-recorded or choose another --outdir')
    if args.precision<80:
        parser.error('--precision must be at least 80')
    args.outdir.mkdir(parents=True,exist_ok=True)
    symbolic_checks()
    numerical_checks(args.outdir,args.precision)
    report={"python":platform.python_version(),"sympy":sp.__version__,"mpmath":mp.__version__,
            "decimal_precision":args.precision,"exact_count":len(EXACT),
            "numerical_count":len(NUMERIC),"all_passed":True,
            "exact_checks":EXACT,"numerical_checks":NUMERIC,
            "scope":"Finite identities and high-precision diagnostics; no intervals, no Lean proof."}
    # ed. (2026-09-29): newline='\n' so the JSON and the summary are LF on Windows too
    (args.outdir/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    text=(f"Exact assertions: {len(EXACT)} passed\nNumerical assertions: {len(NUMERIC)} passed\n"
          f"Decimal precision: {args.precision}\nPython {platform.python_version()}, "
          f"SymPy {sp.__version__}, mpmath {mp.__version__}\n"
          "No directed-rounding interval arithmetic or formal proof assistant was used.\n")
    (args.outdir/'run_summary.txt').write_text(text,encoding='utf-8',newline='\n')
    print(text)

if __name__=='__main__':
    main()
