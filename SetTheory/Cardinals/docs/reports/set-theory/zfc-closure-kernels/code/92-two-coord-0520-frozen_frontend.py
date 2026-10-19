#!/usr/bin/env python3
"""Exact ground-clause reference for the six-function frozen kernel.

The default decides one finite propositional stage. --whole-search runs the
ideal, generally infeasible inconsistency semidecision. It halts successfully
only after a completely exhausted exact UNSAT stage. Resource errors are not
caught or converted to refutations. This is not a binary TM implementation.
"""
from __future__ import annotations
import argparse
from itertools import product
import json
from math import isqrt
from pathlib import Path
import frozen_kernel as K

FUNCS=[x for x in K.FUNCS if x[0]!='W']
TAGS={name:i for i,(name,arity) in enumerate(FUNCS)}

def pair(a,b):
    return (a+b)*(a+b+1)//2+b

def unpair(n):
    w=(isqrt(8*n+1)-1)//2
    b=n-w*(w+1)//2
    return w-b,b

def tuple_code(xs):
    return xs[0] if len(xs)==1 else pair(xs[0],tuple_code(xs[1:]))

def tuple_decode(n,k):
    if k==1:
        return (n,)
    a,b=unpair(n)
    return (a,)+tuple_decode(b,k-1)

def encode(t):
    if t==('d',):
        return 0
    tag=TAGS[t[0]] if t[0] in TAGS else int(t[0][4:])
    return 1+tag+8*tuple_code(tuple(encode(x) for x in t[1:]))

def decode(n):
    if n==0:
        return ('d',)
    tag,payload=(n-1)%8,(n-1)//8
    name,arity=FUNCS[tag] if tag<len(FUNCS) else ('junk'+str(tag),1)
    xs=tuple_decode(payload,arity)
    assert all(0<=x<n for x in xs)
    return (name,)+tuple(decode(x) for x in xs)

def instantiate(t,environment):
    if isinstance(t,str):
        return environment[t]
    if t==('d',):
        return 0
    return 1+TAGS[t[0]]+8*tuple_code(tuple(instantiate(x,environment) for x in t[1:]))

def ground_stage(bound,extensional=False):
    """Variables range over codes 0..bound, including all collisions.

    Endpoint terms outside that range are retained. Equality is an explicit
    predicate at finite stages; every required completed universal instance
    eventually appears. No finite-stage certificate is a whole-kernel model.
    """
    if not isinstance(bound,int) or bound<0:
        raise ValueError('bound must be a nonnegative integer')
    clauses=K.reduced_witness_clauses(extensional,True)+K.equality_clauses(FUNCS)
    atom_ids={}
    result=[]
    largest_endpoint_bits=0
    for clause in clauses:
        vs=K.clause_vars(clause)
        for values in product(range(bound+1),repeat=len(vs)):
            env=dict(zip(vs,values))
            literals=[]
            for sign,p,a,b in clause:
                a=instantiate(a,env); b=instantiate(b,env)
                largest_endpoint_bits=max(largest_endpoint_bits,a.bit_length(),b.bit_length())
                atom=(p,a,b)
                if atom not in atom_ids:
                    atom_ids[atom]=len(atom_ids)+1
                literals.append(atom_ids[atom] if sign else -atom_ids[atom])
            result.append(frozenset(literals))
    # Numbered atoms avoid making a gigantic shift by an arithmetic atom code.
    return tuple(result),{'bound':bound,'clauses_before_simplification':len(result),
                         'atoms':len(atom_ids),'largest_endpoint_bits':largest_endpoint_bits}

def simplify(clauses,literal):
    return tuple(c-{-literal} for c in clauses if literal not in c)

def check_valuation(clauses,valuation):
    return all(any(valuation.get(abs(l),False)==(l>0) for l in c) for c in clauses)

def decide(clauses):
    """Exact finite DPLL. Return a checked valuation, or None after exhaustion."""
    clean=tuple(c for c in set(clauses) if not any(-l in c for l in c))
    pending=[(clean,{})]
    while pending:
        residual,assignment=pending.pop()
        while True:
            if not residual:
                if not check_valuation(clauses,assignment):
                    raise AssertionError('independent SAT witness evaluation failed')
                return assignment
            if any(not c for c in residual):
                break
            singleton=next((next(iter(c)) for c in residual if len(c)==1),None)
            if singleton is not None:
                assignment[abs(singleton)]=singleton>0
                residual=simplify(residual,singleton)
                continue
            selected=min(residual,key=lambda c:(len(c),tuple(sorted(c))))
            literal=min(selected,key=lambda l:(abs(l),l))
            other=dict(assignment); other[abs(literal)]=literal<0
            pending.append((simplify(residual,-literal),other))
            assignment[abs(literal)]=literal>0
            residual=simplify(residual,literal)
    return None

def check_solver():
    # All CNFs with at most three distinct clauses on two Boolean variables.
    possible=[]
    for tags in product((-1,0,1),repeat=2):
        possible.append(frozenset((i+1)*v for i,v in enumerate(tags) if v))
    count=0
    for mask in range(1<<len(possible)):
        selected=tuple(c for i,c in enumerate(possible) if mask&(1<<i))
        if len(selected)>3:
            continue
        brute=any(check_valuation(selected,{1:a,2:b}) for a,b in product((False,True),repeat=2))
        result=decide(selected)
        assert (result is not None)==brute
        count+=1
    for n in range(4096):
        assert encode(decode(n))==n
    return {'exhaustive_small_cnf_checks':count,'radix8_roundtrips':4096}

def whole_search(extensional=False):
    bound=0
    while True:
        clauses,stats=ground_stage(bound,extensional)
        witness=decide(clauses)
        if witness is None:
            return stats
        bound+=1

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--stage',type=int,default=1)
    ap.add_argument('--extensional',action='store_true')
    ap.add_argument('--whole-search',action='store_true')
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('frozen-frontend-results.json'))
    args=ap.parse_args()
    regression=check_solver()
    if args.whole_search:
        data={'result':'UNSAT','stage':whole_search(args.extensional),
              'scope':'exact unbounded mathematical reference; no TM state claim'}
    else:
        cs,stats=ground_stage(args.stage,args.extensional)
        witness=decide(cs)
        data={'result':'UNSAT' if witness is None else 'SAT','stage':stats,
              'witness_literals':len(witness) if witness is not None else None,
              'scope':'finite propositional ground stage only; no whole-kernel model claim'}
    data['theory']='FC14S' if args.extensional else 'FC13S'
    data['regressions']=regression
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':
    main()
