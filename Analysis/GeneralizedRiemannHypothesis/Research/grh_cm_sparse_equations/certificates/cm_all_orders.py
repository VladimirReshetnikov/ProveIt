#!/usr/bin/env python3
"""Certify clustered CM conjugates for every quartic and quintic order.

Run with no arguments to reconstruct the class polynomials by certified complex
interval arithmetic.  --from-json reuses coefficients previously generated.
"""
import argparse
import csv
import json
from fractions import Fraction
from math import comb
from pathlib import Path
from cm_gen import class_polynomial
from cm_order_census import census

# Each attempted ball has v_p(j/p**t - r) greater than the Schur threshold.
BALLS = (
    (2, 6, 3), (2, 6, 5), (2, 6, 7), (2, 3, 5),
    (3, 3, 1), (3, 3, 2), (7, 0, 6), (13, 0, 5), (17, 0, 8),
)

def valuation(n,p):
    """Finite valuation of a nonzero integer."""
    assert n
    answer=0
    while n % p == 0:
        n //= p
        answer += 1
    return answer

def digit_sum(n,p):
    total = 0
    while n:
        n,r = divmod(n,p)
        total += r
    return total

def threshold(k,p):
    # Legendre's factorial identity bounds v_p((i+n)!/i!)/n by this.
    return Fraction(max(digit_sum(i,p) for i in range(k)),p-1)

def translated_polynomial(poly,p,t,r):
    """P(p^t (Y+r)), coefficients ascending."""
    scaled=[c * p**(t*i) for i,c in enumerate(poly)]
    return [sum(scaled[j]*comb(j,i)*r**(j-i) for j in range(i,len(scaled)))
            for i in range(len(scaled))]

def strict_ball_count(poly,p,radius):
    """Number of roots with v_p(root)>radius, with multiplicity.

    It is the smallest index attaining the minimum of v_p(c_i)+i*radius,
    by the Newton polygon theorem (including a possible zero-root factor).
    """
    _, i = min((valuation(c,p)+j*radius,j) for j,c in enumerate(poly) if c)
    return i

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--from-json',type=Path)
    ap.add_argument('--save-json',type=Path)
    ap.add_argument('--csv',type=Path)
    args=ap.parse_args()
    orders=census()
    polynomials=json.loads(args.from_json.read_text()) if args.from_json else {}
    rows=[]
    for h in (4,5):
        for D in orders[h]:
            if args.from_json is None:
                polynomials[str(D)]=class_polynomial(D)
            f=polynomials[str(D)]
            assert f[-1]==1 and len(f)==h+1 and f[0]
            k=4 if D==131 else h
            for p,t,r in BALLS:
                theta=threshold(k,p)
                g=translated_polynomial(f,p,t,r)
                n=strict_ball_count(g,p,theta)
                if n>=k:
                    rows.append((D,h,k,p,t,r,theta,n))
                    break
            else:
                raise AssertionError(f"no {k}-root certificate at discriminant -{D}")
    assert len(rows)==113
    assert {int(d) for d in polynomials} == set(orders[4]+orders[5])
    f=polynomials['131']
    assert valuation(f[0],17)==3
    assert strict_ball_count(translated_polynomial(f,17,0,8),17,Fraction(1,2))==4
    if args.save_json:
        args.save_json.write_text(json.dumps(polynomials,indent=2)+'\n')
    if args.csv:
        with args.csv.open('w',newline='') as stream:
            writer=csv.writer(stream)
            writer.writerow(('D','class_number','target','p','t','r','threshold','root_count'))
            writer.writerows(rows)
    print('84/84 quartic orders have a four-root certificate')
    print('28/29 quintic orders have a five-root certificate')
    print('D=131 has four unit roots at 8 mod 17 (valuation > 1/2)')
    print('its fifth root has 17-adic valuation 3')

if __name__=='__main__':
    main()
