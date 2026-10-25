#!/usr/bin/env python3
"""Finite regression checks for the cofinal Pell majorant lemma.

These checks support the ordinary proof; they do not prove universal
arithmetic statements by enumeration. No full consistency equation is solved.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import hashlib
import json
from math import factorial

ROOT=Path(__file__).resolve().parent

def pell_mod(a,n,m):
    if m<=0 or n<0:
        raise ValueError("positive modulus and nonnegative index required")
    x,y=1,0
    u,v=a%m,1
    disc=(a*a-1)%m
    while n:
        if n&1:
            x,y=(x*u+disc*y*v)%m,(x*v+y*u)%m
        u,v=(u*u+disc*v*v)%m,(2*u*v)%m
        n//=2
    return x,y

def pell_exact(a,n):
    x,y=1,0
    for _ in range(n):
        x,y=a*x+(a*a-1)*y,x+a*y
    return x,y

def vp(n,p):
    n=abs(n)
    if n==0:
        raise ValueError("valuation of zero not used")
    r=0
    while n%p==0:
        n//=p;r+=1
    return r

def require(c,m):
    if not c:raise ValueError(m)

def audit():
    # The conjectured congruence at every old horizon is deliberately false.
    bad_t=16;bad_d=6*(bad_t+1);bad_n=bad_d*10**bad_t
    _,bad_r=pell_mod(bad_d+1,bad_n,3*bad_d)
    require(bad_r//bad_d==0,"expected control quotient residue zero")
    counts={"small_exact_pairs":0,"cofinal_horizons":0,
            "taylor_modular_checks":0,"matrix_lift_checks":0}
    horizon_cases=[]
    for a in range(3,30,2):
        for n in range(1,41):
            x,y=pell_exact(a,n)
            require(x*x-(a*a-1)*y*y==1,"norm")
            require(vp(y,2)==vp(n,2),"dyadic valuation")
            counts["small_exact_pairs"]+=1
    for d in range(3,180,3):
        for n in range(1,80):
            _,y=pell_mod(d+1,n,3*d)
            derivative=n*(n*n-1)//3
            require((y-n-d*derivative)%(3*d)==0,"Taylor congruence")
            counts["taylor_modular_checks"]+=1
    for h in range(1,51):
        if h%3==0:continue
        t=16+h*h;d=6*(t+1);a=d+1;n=d*10**t
        _,ym=pell_mod(a,n,3*d)
        require(ym%d==0 and ym//d==1,"ordinate progression")
        # A bounded exponent still independently exercises the same lifting.
        j=min(t,12)
        _,y5=pell_mod(a,n,5**j)
        require(y5==0,"five-adic divisibility")
        j2=min(t+1,16)
        _,y2=pell_mod(a,n,2**j2)
        require(y2==0,"dyadic divisibility")
        require(n%(120*5**(t-1))==0,"matrix-period exponent")
        require(2*t>=sum(t//5**k for k in range(1,t.bit_length()+1)),
                "factorial five-part")
        counts["cofinal_horizons"]+=1
        horizon_cases.append({"h":h,"t":t,"d":d,"quotient_mod3":1,
                              "checked_5_power":j,"checked_2_power":j2})
    for a in range(2,60):
        for k in range(1,9):
            x,y=pell_mod(a,120*5**(k-1),5**k)
            require((x,y)==(1,0),"SL2 lifting")
            counts["matrix_lift_checks"]+=1
    result={"status":"pass","counts":counts,
            "rejected_shortcut":{"claim":"all horizons give quotient1mod3",
             "t":bad_t,"d":bad_d,"n_recipe":"d*10^t",
             "actual_quotient_mod3":bad_r//bad_d},
            "cofinal_horizons":horizon_cases,
            "scope":"finite regression; see PROOF.md for universal proof",
            "proof_sha256":hashlib.sha256((ROOT/"PROOF.md").read_bytes()).hexdigest()}
    return result

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    rendered=json.dumps(audit(),indent=2)+"\n"
    if args.output:args.output.write_text(rendered)
    print(rendered,end="")

