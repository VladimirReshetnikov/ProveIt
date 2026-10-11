"""Exact small-rank verification of the all-rank alternant coefficient."""
from __future__ import annotations

import itertools
import json
import math
from pathlib import Path

import sympy as sp

BASE=Path(__file__).resolve().parent.parent / "results"


def parity(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))


def delta(xs):
    return sp.prod(xs[j]-xs[i] for i in range(len(xs)) for j in range(i+1,len(xs)))


checks=[]
for m in [2,3,4]:
    N=m*(m-1)//2
    al=sp.symbols(f'a0:{m}')
    ls=sp.symbols(f'l0:{m}')
    observed=sum(parity(p)*sum(al[p[j]]*ls[j] for j in range(m))**N
                 for p in itertools.permutations(range(m)))
    coefficient=sp.Rational(math.factorial(N),math.prod(math.factorial(k) for k in range(m)))
    expected=coefficient*delta(al)*delta(ls)
    difference=sp.Poly(sp.expand(observed-expected),*al,*ls)
    correct=difference.is_zero
    assert correct
    checks.append({'m':m,'N':N,'permutations':math.factorial(m),
                   'alternant_coefficient':str(coefficient),'symbolic_polynomial_equal':correct,
                   'normalized_spectral_coefficient':str(sp.Rational(
                       (-1)**N*math.factorial(N-1),
                       math.prod(math.factorial(k) for k in range(m))))})
    print(f'm={m}: exact symbolic alternant {correct}',flush=True)

# Unnormalized examples verify the signs and the degree-six coefficient.
examples=[]
for shifts,weights in [([1,2,3],[2,1,0]),([1,2,3,4],[3,2,1,0])]:
    m=len(shifts); N=m*(m-1)//2
    factor=sp.Rational((-1)**N*math.factorial(N-1),
                       sum(weights)*math.prod(math.factorial(k) for k in range(m)))
    examples.append({'shifts':shifts,'weights':weights,'jet_order':N-1,
                     'degree_of_monic_P':N-1,
                     'signed_sum':str(factor*delta(weights)*delta(shifts))})

(BASE/'vandermonde_alternant_checks.json').write_text(json.dumps(
    {'checks':checks,'examples':examples,'status':'exact symbolic polynomial identities'},indent=2)+'\n')
