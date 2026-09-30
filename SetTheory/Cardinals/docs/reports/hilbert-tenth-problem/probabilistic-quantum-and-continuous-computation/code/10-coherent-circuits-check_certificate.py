#!/usr/bin/env python3
"""Independent, standard-library verifier for exported natural witnesses.

Usage: python code/check_certificate.py data/HH_expanded_quartic.json [...]
This checks polynomial equations and, when provided, the expanded sum-of-squares
identity. Semantic correspondence to a quantum circuit is a separate theorem.
No code is imported from the certificate generator.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys


def parse_poly(terms: list, n: int, degree_limit: int) -> dict[tuple[int,...],int]:
    if not isinstance(terms,list): raise ValueError("Polynomial must be a list of terms")
    result={}
    for term in terms:
        c=term["coefficient"]; indices=term["variables"]
        if type(c) is not int or not isinstance(indices,list):
            raise ValueError("Invalid coefficient or monomial")
        if len(indices)>degree_limit or any(type(i) is not int or i<0 or i>=n for i in indices):
            raise ValueError("Invalid variable index or degree")
        monomial=tuple(sorted(indices))
        result[monomial]=result.get(monomial,0)+c
    return {m:c for m,c in result.items() if c}


def evaluate(p: dict, values: list[int]) -> int:
    total=0
    for m,c in p.items():
        term=c
        for i in m: term*=values[i]
        total+=term
    return total


def verify(path: Path) -> dict:
    with path.open(encoding="utf-8") as f: data=json.load(f)
    if data["domain"]!="nonnegative integers": raise ValueError("Unexpected witness domain")
    names=data["variables"];values=data["witness"];n=len(names)
    if len(set(names))!=n or len(values)!=n:
        raise ValueError("Wrong coordinate count or duplicate names")
    if any(type(x) is not int or x<0 for x in values):
        raise ValueError("Every witness coordinate must be a natural number")
    constraints=[parse_poly(p,n,2) for p in data["quadratic_constraints"]]
    for i,p in enumerate(constraints):
        if evaluate(p,values)!=0: raise ValueError(f"Constraint {i} does not vanish")
    checked_expansion=False
    if "expanded_quartic" in data:
        expanded=parse_poly(data["expanded_quartic"],n,4)
        expected={}
        for p in constraints:
            for m,c in p.items():
                for k,d in p.items():
                    monomial=tuple(sorted(m+k))
                    expected[monomial]=expected.get(monomial,0)+c*d
        expected={m:c for m,c in expected.items() if c}
        if expected!=expanded: raise ValueError("Expanded polynomial is not the sum of squares")
        if evaluate(expanded,values)!=0: raise ValueError("Quartic does not vanish")
        checked_expansion=True
    metadata=data.get("metadata",{})
    if "output_coordinates" in metadata:
        actual=[]
        for wire in metadata["output_coordinates"]:
            p,m=wire["positive"],wire["negative"]
            if not 0<=p<n or not 0<=m<n: raise ValueError("Invalid output wire")
            actual.append(values[p]-values[m])
        if actual!=metadata["expected_numerator_coefficients"]:
            raise ValueError("Output metadata does not match witness")
    return {"file":path.name,"status":"PASS","variables":n,
            "equations":len(constraints),"expanded_identity_checked":checked_expansion}


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files",nargs="+",type=Path)
    args=parser.parse_args()
    try:
        for path in args.files: print(json.dumps(verify(path),sort_keys=True))
        return 0
    except (OSError,ValueError,KeyError,TypeError) as error:
        print(f"FAIL: {error}",file=sys.stderr)
        return 1


if __name__=="__main__": raise SystemExit(main())
