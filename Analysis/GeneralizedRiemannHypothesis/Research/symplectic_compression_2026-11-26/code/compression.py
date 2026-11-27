#!/usr/bin/env python3
"""Evaluate an exact symplectic compression probability from a JSON file.

Usage: python3 compression.py example_matrix.json
Input keys: q, n, H1, H0, matrix.  Here dim ambient=2*n and all arrays are
row-major. Supported fields: any prime q, or q=4 with elements encoded as
0,1,x,x+1 by integers 0,1,2,3, where x*x=x+1.

Keep check_complete_law.py beside this file; it contains the exact formula
and finite-field linear algebra used here.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
from check_complete_law import embeddings, invariants, rank, transverse


def probability(data):
    q,n=data["q"],data["n"]
    if not isinstance(q,int) or q<2 or (q!=4 and any(q%d==0 for d in range(2,int(q**0.5)+1))):
        raise ValueError("This evaluator supports prime q and GF(4) only.")
    if not isinstance(n,int) or n<0:
        raise ValueError("n must be a nonnegative integer (ambient dimension is 2n).")
    H1,H0,A=data["H1"],data["H0"],data["matrix"]
    a,b=len(H1),len(H0)
    def check_array(B,h,w,name):
        if len(B)!=h or any(len(row)!=w for row in B):
            raise ValueError(f"{name} must have shape {h} by {w}.")
        if any(not isinstance(v,int) or not 0<=v<q for row in B for v in row):
            raise ValueError(f"Every {name} entry must be an integer in [0,q).")
    check_array(H1,a,a,"H1")
    check_array(H0,b,b,"H0")
    check_array(A,a,b,"matrix")
    for H in (H1,H0):
        d=len(H)
        if any(H[i][i]!=0 for i in range(d)):
            raise ValueError("Gram matrices must have zero diagonal.")
        if any((H[i][j]^H[j][i] if q==4 else (H[i][j]+H[j][i])%q)!=0
               for i in range(d) for j in range(d)):
            raise ValueError("Gram matrices must be alternating.")
    s1,s0=rank(H1,q)//2,rank(H0,q)//2
    target_count,source_count=embeddings(q,n,a,s1),embeddings(q,n,b,s0)
    if not target_count or not source_count:
        raise ValueError("At least one prescribed frame does not embed in the given ambient dimension.")
    s,r,t0,t1=invariants(H1,H0,A,q)
    numerators=[transverse(q,r,t0,t1,l)*embeddings(q,n,a+b-l,s) for l in range(r+1)]
    total=sum(numerators)
    denominator=target_count*source_count
    p=Fraction(total,denominator)
    return {"q":q,"ambient_dimension":2*n,"target_dimension":a,"source_dimension":b,
            "target_form_rank":2*s1,"source_form_rank":2*s0,
            "combined_form_rank":2*s,"radical_dimension":r,"t0":t0,"t1":t1,
            "minimum_ambient_dimension_for_data":2*(s+max(t0,t1)),
            "supported":bool(total),"exact_probability":str(p),
            "density_relative_to_uniform":str(q**(a*b)*p),
            "joint_matrix_and_intersection_probability":
                {str(l):str(Fraction(v,denominator)) for l,v in enumerate(numerators) if v},
            "conditional_intersection_dimension":None if not total else
                {str(l):str(Fraction(v,total)) for l,v in enumerate(numerators) if v}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input",type=Path,help="JSON file with q,n,H1,H0,matrix")
    args=parser.parse_args()
    try:
        print(json.dumps(probability(json.loads(args.input.read_text())),indent=2))
    except (KeyError,ValueError,TypeError) as exc:
        parser.error(str(exc))


if __name__=="__main__":
    main()
