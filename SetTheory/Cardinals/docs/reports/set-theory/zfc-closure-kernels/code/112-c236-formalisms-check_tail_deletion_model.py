#!/usr/bin/env python3
"""Finite transcription checks for an explicit infinite tail-deletion model.

The proof on all natural numbers is in tail_deletion_model.tex.  The finite
cases below check the literal inherited AST against its mathematical model;
they do not purport to verify an infinite theory by bounded testing.
"""
from __future__ import annotations

import argparse
from functools import cache
from itertools import product
import json
from math import isqrt
from pathlib import Path


def cantor(x, y):
    return (x+y)*(x+y+1)//2+y


def unpair(n):
    diagonal = (isqrt(8*n+1)-1)//2
    y = n - diagonal*(diagonal+1)//2
    return diagonal-y, y


def nand(x, y):
    """Finite/cofinite BA on N: 2m means complement(m), 2m+1 means m.

    Here a finite set is represented by its ordinary binary bit mask m.
    Boolean top is 0 and bottom is 1. Complement toggles the low bit.
    """
    mx, my, fx, fy = x//2, y//2, x%2, y%2
    if fx and fy:
        intersection = 2*(mx & my)+1
    elif fx:
        intersection = 2*(mx & ~my)+1
    elif fy:
        intersection = 2*(my & ~mx)+1
    else:
        intersection = 2*(mx | my)
    return intersection ^ 1


def pair(x, s):
    return 3*cantor(x,s)+1


def atom(i,j):
    return 3*cantor(i,j)+2


def quantified(a):
    return 3*a+3


def value(s, i):
    # Deliberately ignores the coordinate i. This is exactly what tail would
    # prohibit; it retains the genuine head equation.
    return unpair((s-1)//3)[0] if s%3 == 1 else 0


@cache
def truth(code):
    if code == 0:
        return 1                        # the base class is constantly false
    if code%3 == 1:
        a,b = unpair((code-1)//3)
        assert a < code and b < code
        return nand(truth(a),truth(b))  # NAND class
    if code%3 == 2:
        return 1                        # all atomic classes are false
    a = (code-3)//3
    assert 0 <= a < code
    return nand(truth(a),truth(a))       # complemented binder


def membership(x,y):
    return 0 if x<y else 1              # true is top=0, false is bottom=1


OPS = {
    "d": lambda: 0,
    "N": nand,
    "V": value,
    "P": pair,
    "A": atom,
    "Q": quantified,
    "W": lambda s,a: 0,
    "Target": lambda b: 0,
    "Next": lambda b,z: z+2,
    "Mem": lambda b,z: z+1,
    "p_E": membership,
    "p_eps": lambda s,a: truth(a),
}


def variables(t):
    if isinstance(t,str):
        return {t}
    result = set()
    for c in t[1:]:
        result.update(variables(c))
    return result


def evaluate(t,env):
    if isinstance(t,str):
        return env[t]
    return OPS[t[0]](*(evaluate(c,env) for c in t[1:]))


def main():
    here=Path(__file__).resolve().parent
    parser=argparse.ArgumentParser()
    parser.add_argument("--input",type=Path,default=here/"generated/E688.json")
    parser.add_argument("--out",type=Path,default=here/"generated/tail_deletion_checks.json")
    parser.add_argument("--range",type=int,default=8)
    args=parser.parse_args()
    data=json.loads(args.input.read_text())
    tail=[ ["V",["P","x","s"],["A","j",["d"]]], ["V","s","j"] ]
    assert data["equations"][2] == tail
    counts=[]
    for index,(lhs,rhs) in enumerate(data["equations"]):
        if index==2:
            continue
        names=sorted(variables(lhs)|variables(rhs))
        count=0
        for values in product(range(args.range),repeat=len(names)):
            env=dict(zip(names,values))
            assert evaluate(lhs,env)==evaluate(rhs,env),(index,env)
            count+=1
        counts.append({"E688_equation":index+1,"variables":names,"cases":count})
    witness={"x":1,"s":0,"j":0}
    lhs,rhs=(evaluate(t,witness) for t in tail)
    assert (lhs,rhs)==(1,0)
    start=evaluate(data["start"],{})
    target=evaluate(data["target"],{})
    assert (start,target)==(1,0)
    result={
        "status":"PASS",
        "model":"explicit infinite algebra on N; finite/cofinite Boolean operations",
        "finite_check_range": [0,args.range-1], "literal_equation_cases": counts,
        "total_literal_cases":sum(row["cases"] for row in counts),
        "tail_counterexample":{"assignment":witness,"lhs":lhs,"rhs":rhs},
        "query_separation":{"N(d,d)":start,"d":target},
        "scope":"finite transcription checks; the separate written proof establishes every equation at all natural arguments",
    }
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Run without -O: checks use assertions.")
    main()
