#!/usr/bin/env python3
"""Exact auxiliary checks for the total-coordinate-bitlength addendum.

Python standard library only. No source repository code is imported or run.
Default mode verifies a saved receipt without writing; --write regenerates it.
All finite-set counts below are explicitly finite-sample checks, not claims
to exhaust the complete native fiber. The universal result is a proof.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
RECEIPT = HERE / 'TOTAL-BITLENGTH-RECEIPT.json'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def pell_pair(A, n):
    delta = A*A-1
    x, y, u, v = 1, 0, A, 1
    while n:
        if n & 1:
            x, y = x*u+delta*y*v, x*v+y*u
        u, v = u*u+delta*v*v, 2*u*v
        n >>= 1
    return x, y


def varying_tuple(A, p, l, k=None, sign=None):
    delta = A*A-1
    c = pell_pair(A, p)[1]
    M = p*c//math.gcd(c, delta)
    m = M*l
    n = p if k is None else 4*m*k+sign*p
    f, main_y = pell_pair(A, m)
    R = delta*main_y
    aux_x, y = pell_pair(R, n)
    require(R % (c*c) == 0, 'i is not integral')
    require(aux_x % R == 0, 'U is not integral')
    i, U = R//(c*c), aux_x//R
    require((U+p) % c == 0, 'j is not integral')
    require((U+c) % f == 0, 'o is not integral')
    j, o = (U+p)//c, (U+c)//f
    vals = (f,i,j,o,y)
    require(all(isinstance(x,int) and x>0 for x in vals), 'positivity/type failure')
    require(R*R == delta*(f*f-1), 'main norm mismatch')
    require(R*R*(U*U-y*y) == 1-y*y, 'auxiliary norm mismatch')
    require(U == j*c-p == o*f-c, 'reconstruction mismatch')
    product = math.prod(vals)
    rhs = R*y*(U+p)*(U+c)
    require(product*c**3 == rhs, 'exact product identity failed')
    require(product*c**2 != rhs, 'denominator mutation was not detected')
    subtotal = sum(x.bit_length() for x in vals)
    require(1 << (subtotal-5) <= product < 1 << subtotal,
            'exact five-coordinate bit-rounding bound failed')
    return {'A':A,'p':p,'c':c,'M':M,'l':l,'m':m,'n':n,
            'branch':'baseline' if k is None else ('minus' if sign == -1 else 'plus'),
            'coordinate_bits':[x.bit_length() for x in vals],
            'varying_bit_sum':subtotal,'product_bits':product.bit_length()}, product


def sample_cutoff_checks(samples, fixed_bits):
    # All comparisons and counts are integer exact; no logarithm or float floor.
    rows = []
    for metadata, _ in samples:
        B0 = fixed_bits+metadata['varying_bit_sum']
        counts = []
        for B in (B0-1,B0,B0+1):
            count = sum(fixed_bits+meta['varying_bit_sum'] <= B for meta,_ in samples)
            lower = sum(P <= 1 << (B-fixed_bits-5) for _,P in samples)
            upper = sum(P <= 1 << (B-fixed_bits) for _,P in samples)
            require(lower <= count <= upper, 'finite-sample global cutoff sandwich failed')
            counts.append(count)
        require(counts[1] > counts[0], 'known total-bit jump was not counted')
        rows.append({'A':metadata['A'],'m':metadata['m'],'n':metadata['n'],
                     'cutoff':B0,'sample_counts_below_at_above':counts})
    return rows


def synthetic_rounding_checks():
    fixtures = [(1,1,1,1,1),(2,4,8,16,32),(3,7,15,31,63),
                (2,3,3,4,6),(3,2,2,7,7),(1,2,4,8,16)]
    results=[]
    for xs in fixtures:
        P = math.prod(xs)
        B = sum(x.bit_length() for x in xs)
        require(1 << (B-5) <= P < 1 << B, 'synthetic rounding bound failed')
        results.append({'coordinates':list(xs),'sum_bits':B,'product_bits':P.bit_length()})
    # Different tuples with equal total bits exercise multiplicity in a finite
    # synthetic set, independently of whether the Pell sample happens to tie.
    budgets = sorted(sum(x.bit_length() for x in xs) for xs in fixtures)
    require(len(set(budgets)) < len(budgets), 'synthetic sample has no ties')
    for rank,B in enumerate(budgets,1):
        require(sum(t < B for t in budgets) < rank <= sum(t <= B for t in budgets),
                'rank-with-ties inequality failed')
    return results


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    samples=[]
    for A in (3,4,5):
        for l,k,sign in [(1,None,None),(2,None,None),(3,None,None),
                         (1,1,-1),(1,1,1),(2,1,-1)]:
            samples.append(varying_tuple(A,3,l,k,sign))
    # Arbitrary positive fixed-coordinate fixture, not native forced values.
    fixed_fixture=list(range(1,18))
    fixed_bits=sum(x.bit_length() for x in fixed_fixture)
    result={'status':'PASS',
            'evidence_boundary':'These are small auxiliary Pell reconstructions and finite-sample bit-cutoff checks. They are not full padded native instances, whole-fiber exhaustive counts, or an asymptotic proof.',
            'exact_auxiliary_tuples':[meta for meta,_ in samples],
            'arbitrary_seventeen_fixed_fixture':fixed_fixture,
            'arbitrary_fixed_bits':fixed_bits,
            'exact_sample_bit_cutoffs':sample_cutoff_checks(samples,fixed_bits),
            'synthetic_rounding_and_ties':synthetic_rounding_checks(),
            'denominator_mutations_detected':len(samples)}
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.write:
        RECEIPT.write_text(encoded)
        print('PASS: wrote',RECEIPT.name)
    else:
        require(RECEIPT.read_text()==encoded,'receipt mismatch; no files modified')
        print('PASS: matched read-only receipt')
    print('Exact auxiliary tuples:',len(samples))
    print('Exact finite-sample cutoff checks:',3*len(samples))
    print('Product denominator mutations detected:',len(samples))
    print('Synthetic rounding/tie fixtures:',len(result['synthetic_rounding_and_ties']))


if __name__=='__main__':
    main()
