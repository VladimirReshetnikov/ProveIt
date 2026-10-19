"""Attributed minimal runtime copied from the ProveIt FC ground kernel.

Source: research/agent_formalism/reference/ground_kernel.py
Source SHA-256: 2ceebc265a6d2dc5d487f4b9d078a53d6b37d7718184e6f2c6da920b6a4985fb
License: MIT No Attribution, copyright 2026 ProveIt Contributors.
The full supplied license is preserved as three_function_LICENSE.ProveIt.
Only arithmetic pairing and the existing exact DPLL routines are copied.
"""
from math import isqrt
PREDICATES = ['E', 'Inc', 'G', 'Eq']

def pair(a: int, b: int) -> int:
    return (a+b)*(a+b+1)//2+b

def unpair(n: int) -> tuple[int,int]:
    w=(isqrt(8*n+1)-1)//2
    b=n-w*(w+1)//2
    return w-b,b

def tuple_code(xs) -> int:
    if len(xs)==1:
        return xs[0]
    return pair(xs[0],tuple_code(xs[1:]))

def tuple_decode(n: int, k: int) -> tuple[int,...]:
    if k==1:
        return (n,)
    a,b=unpair(n)
    return (a,)+tuple_decode(b,k-1)

def atom_code(pred,a,b):
    return PREDICATES.index(pred)+4*pair(a,b)

def normalize(cnf):
    out=set()
    for clause in cnf:
        c=frozenset(clause)
        if any(-l in c for l in c):
            continue
        out.add(c)
    return tuple(sorted(out,key=lambda c:(len(c),tuple(sorted(c)))))

def simplify(cnf,literal):
    return tuple(c-{ -literal } for c in cnf if literal not in c)

def solve(cnf):
    """Exact iterative DPLL. Return a satisfying partial valuation or None.

    Unassigned atoms may be set false. Every input clause is independently
    reevaluated before a SAT result is returned by the command-line runner.
    """
    pending=[(normalize(cnf),{})]
    while pending:
        work,assignment=pending.pop()
        while True:
            if not work:
                return assignment
            if any(not c for c in work):
                break
            unit=next((next(iter(c)) for c in work if len(c)==1),None)
            if unit is not None:
                assignment[abs(unit)]=unit>0
                work=simplify(work,unit)
                continue
            signs=set().union(*work)
            pure=next((l for l in sorted(signs,key=lambda x:(abs(x),x)) if -l not in signs),None)
            if pure is not None:
                assignment[abs(pure)]=pure>0
                work=simplify(work,pure)
                continue
            shortest=min(work,key=lambda c:(len(c),tuple(sorted(c))))
            literal=min(shortest,key=lambda x:(abs(x),x))
            other=dict(assignment)
            other[abs(literal)]=literal<0
            pending.append((simplify(work,-literal),other))
            assignment[abs(literal)]=literal>0
            work=simplify(work,literal)
    return None

def valuation_satisfies(cnf,valuation):
    return all(any(valuation.get(abs(l),False)==(l>0) for l in c) for c in cnf)
