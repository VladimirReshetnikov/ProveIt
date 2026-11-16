#!/usr/bin/env python3
"""A small certificate generator for the canonical-product tail.

For |z|<=R and N>=2R, the logarithmic tail q_k(z) satisfies
  sum_{k>N}|q_k(z)| <= 2 R^3/(3N).
The script computes partial products with mpmath, but the *reported tail bound*
is a rational consequence of this theorem.  Thus the bound is suitable as an
input certificate once the finite mpmath approximation is replaced by an exact
dyadic ball evaluator in a formal implementation.
"""
from __future__ import annotations
import argparse, json
from fractions import Fraction
from pathlib import Path
import mpmath as mp


def tail_bound(R: Fraction, N: int) -> Fraction:
    assert N >= 1 and Fraction(N,1) >= 2*R
    return Fraction(2,3)*R**3/Fraction(N,1)


def q(k: int, z):
    return k*mp.log(1+z/k)-z+z*z/(2*k)


def finite_logG1p(z, N):
    return (z/2*mp.log(2*mp.pi) - (z+(1+mp.euler)*z*z)/2
            + mp.fsum(q(k,z) for k in range(1,N+1)))


def run():
    mp.mp.dps=80
    cases=[]
    raw=[(Fraction(1,2), 40, mp.mpf('0.3')),
         (Fraction(1,1), 200, mp.mpf('0.6')+mp.mpf('0.2')*1j),
         (Fraction(2,1), 1200, mp.mpf('-0.4')+mp.mpf('1.1')*1j)]
    for R,N,z in raw:
        B=tail_bound(R,N)
        approx=finite_logG1p(z,N)
        truth=mp.log(mp.barnesg(1+z))
        err=abs(approx-truth)
        cases.append({
            'R':str(R),'N':N,'z':str(z),
            'rational_log_tail_bound': {'numerator':B.numerator,'denominator':B.denominator,'decimal':float(B)},
            'observed_log_error':mp.nstr(err,25),
            'observed_within_bound':bool(err <= mp.mpf(B.numerator)/B.denominator),
        })
    return {'theorem':'sum_{k>N}|q_k(z)| <= 2 R^3/(3N), for |z|<=R and N>=2R',
            'finite_evaluation':'mpmath diagnostic; replace by dyadic ball arithmetic for a proof certificate',
            'cases':cases,'all_observed_within_bound':all(c['observed_within_bound'] for c in cases)}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path); ns=ap.parse_args()
    out=run(); text=json.dumps(out,indent=2,sort_keys=True)+"\n"
    if ns.output:
        ns.output.parent.mkdir(parents=True,exist_ok=True); ns.output.write_text(text,encoding='utf-8')
    print(text,end='')
    raise SystemExit(0 if out['all_observed_within_bound'] else 1)
if __name__=='__main__': main()
