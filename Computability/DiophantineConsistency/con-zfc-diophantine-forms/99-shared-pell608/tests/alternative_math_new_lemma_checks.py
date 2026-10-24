#!/usr/bin/env python3
"""Exact finite checks of self-bounding factorial and shared Pell witnesses.

Independent of all equation builders. Universal proofs are supplied
separately; these checks are implementation evidence and negative controls.
"""
from __future__ import annotations

import json
from math import comb, factorial, gcd, prod
from pathlib import Path


def require(condition, label):
    if not condition:
        raise ValueError(label)


def ceil_ratio(n: int, m: int, *, linear_bad_radius: bool = False) -> int:
    q = m*n if linear_bad_radius else m*n*n
    p, c = (q+1)**n, comb(q+n,n)
    return (p+c-1)//c


def check_factorial():
    tested = 0
    for n in range(0, 8):
        f = factorial(n)
        for m in range(f+3):
            require((ceil_ratio(n,m) == m) == (m == f),
                    f"factorial fixed point n={n},m={m}")
            tested += 1
    for n in range(8,21):
        f = factorial(n)
        candidates = sorted({0,1,2,f//2} | set(range(f-5,f+6)))
        for m in candidates:
            require((ceil_ratio(n,m) == m) == (m == f),
                    f"factorial larger boundary n={n},m={m}")
            tested += 1
        q, c, p = f*n*n, comb(f*n*n+n,n), (f*n*n+1)**n
        r = p+c-c*f-1
        s = c-r-1
        require(r>=0 and s>=0 and p+c==c*f+r+1 and c==r+s+1,
                "natural completeness witnesses")
    require(ceil_ratio(4,23,linear_bad_radius=True) == 23,
            "bad linear-radius negative control must exhibit false fixed point")
    require(ceil_ratio(4,23) != 23,
            "quadratic radius must reject same false output")
    return {"tested_candidate_pairs": tested, "largest_n": 20,
            "full_output_ranges_n_le": 7,
            "negative_control": {"n":4,"incorrect_m":23,
                "correct_factorial":24,"linear_radius_false_fixed_point":True,
                "quadratic_radius_rejects":True}, "passed": True}


def pell(a: int, j: int) -> tuple[int,int]:
    require(a>=2 and j>=0, "Pell parameter range")
    if j==0:
        return 1,0
    x,y=pell(a,j//2)
    xx,yy=2*x*x-1,2*x*y
    if j%2:
        return a*xx+(a*a-1)*yy,xx+a*yy
    return xx,yy


def norm(a,x,y):
    return x*x+y*y-(a*y)**2-1


def shared_pell(a: int, indices: list[int]):
    mains=[pell(a,k) for k in indices]
    ys=[p[1] for p in mains]
    index=2*prod(k*y for k,y in zip(indices,ys))
    u,v=pell(a,index)
    modulus=4*prod(ys)
    require(u>a and v>0 and v%2==0, "common pair ranges")
    require(norm(a,u,v)==0 and gcd(u,modulus)==1, "common norm and CRT")
    qb=((1-a)*pow(u,-1,modulus))%modulus
    b=a+u*qb
    require(b>=a and b%modulus==1, "common B")
    for k,(x,y) in zip(indices,mains):
        s,r=pell(b,k)
        require(v%(y*y)==0 and v//(y*y)>=1, "all squared divisibilities")
        require((b-1)%(4*y)==0 and (b-1)//(4*y)>=1,
                "all positive B quotients")
        require(s>=x and (s-x)%u==0, "all S orientations")
        require(r>=k and (r-k)%(4*y)==0, "all R orientations")
        require(norm(a,x,y)==0 and norm(b,s,r)==0, "all main/third norms")
    return {"A":a,"indices":indices,"common_index_M":index,
            "U_bits":u.bit_length(),"V_bits":v.bit_length(),
            "B_bits":b.bit_length(),"common_modulus_bits":modulus.bit_length(),
            "passed":True}


def complete_shared_power():
    inputs=[(1,1),(2,1),(3,1)]
    w=sum(n+k for n,k in inputs)
    a,wz=pell(w+1,w)
    require(wz%w==0 and norm(w+1,a,wz)==0, "shared majorant")
    exponents=sorted({k for n,k in inputs})
    shared_pell(a,exponents)
    for n,k in inputs:
        x,y=pell(a,k)
        m,t=n**k,2*a*n-n*n-1
        numerator=x+y*n-y*a-m
        require(0<m<t and numerator>=0 and numerator%t==0,
                "all power quotient and gap rows")
    return {"inputs":inputs,"distinct_exponent_blocks":len(exponents),
            "W":w,"A":a,"Z":wz//w,"passed":True}


def shared_radix():
    families=[[(1,1),(2,1),(3,1)],[(4,2),(5,3),(2,4)],
              [(0,0),(0,1),(1,0)],[(8,4),(8,3),(12,5)]]
    count=0
    for calls in families:
        h_bound=sum(n for n,k in calls)
        q=2**h_bound+1
        for n,k in calls:
            expected=comb(n,k) if k<=n else 0
            numerator=(q+1)**n
            denominator=q**k
            quotient,remainder=divmod(numerator,denominator)
            high,coefficient=divmod(quotient,q)
            require(coefficient==expected,"shared-radix binomial digit")
            require(numerator==denominator*(q*high+coefficient)+remainder,
                    "shared-radix division identity")
            require(0<=remainder<denominator and 0<=coefficient<q,
                    "shared-radix remainder and digit bounds")
            count+=1
    return {"families":len(families),"exact_digit_checks":count,"passed":True}


if __name__=="__main__":
    receipt={"scope":"Finite exact checks; universal proofs separate",
             "builder_imported":False,
             "factorial":check_factorial(),
             "shared_pell":[shared_pell(2,[1,2]),shared_pell(3,[2,3])],
             "complete_shared_power":complete_shared_power(),
             "shared_radix":shared_radix(),
             "passed":True}
    out=Path(__file__).with_name("alternative_math_new_lemma_results.json")
    out.write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))
