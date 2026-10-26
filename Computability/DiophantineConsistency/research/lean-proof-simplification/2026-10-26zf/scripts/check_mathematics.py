#!/usr/bin/env python3
"""Finite boundary diagnostics and an exact algebra identity, not Lean proofs."""
import itertools, json
from pathlib import Path

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def run():
    count=0
    zero_budget=zero_mass=collision_count=0
    for w in itertools.product(range(3), repeat=3):
        for u in itertools.product((-1,0,1), repeat=3):
            e=[0]*3
            for wi,ui in zip(w,u): e[wi]+=ui
            mass=sum(abs(x) for x in u)
            for p in itertools.product((-1,0,1), repeat=3):
                H=max(map(abs,p))
                q=list(p)
                for k in range(4):
                    assert max(map(abs,q)) <= H*mass**k
                    count+=1
                    zero_budget+=H==0
                    zero_mass+=mass==0
                    collision_count+=len(set(w))<len(w)
                    q=mul(e,q)
    failures=[r for r in range(101) if not 2**(2*r+2)+2 <= 16**r]
    assert failures==[0,1]
    # Exact coefficient identity: (t-16)(t+12)+190 = t^2-4t-2.
    rhs=mul([-16,1],[12,1]); rhs[0]+=190
    assert rhs==[-2,-4,1]
    return {'status':'passed','evidence_kind':'finite diagnostics, not a universal or kernel proof',
      'coefficient_envelope_cases':count,'zero_budget_cases':zero_budget,
      'zero_mass_cases':zero_mass,'colliding_exponent_cases':collision_count,
      'ranges':{'w':'{0,1,2}^3','u':'{-1,0,1}^3','p_coefficients':'{-1,0,1}^3','k':'0..3'},
      'power_exponents_checked':'0..100','power_failure_exponents':failures,
      'quadratic_identity_coefficients':rhs,
      'model_naturals':'No finite standard-Nat test is claimed to validate nonstandard model semantics.'}

if __name__=='__main__':
    result=run()
    output=Path(__file__).resolve().parents[1]/'evidence/mathematical-diagnostics.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
