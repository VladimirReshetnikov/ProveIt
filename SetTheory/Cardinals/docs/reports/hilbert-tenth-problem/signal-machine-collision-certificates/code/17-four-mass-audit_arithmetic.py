#!/usr/bin/env python3
"""Independent arithmetic checks; these supplement, rather than prove, the audit."""
import importlib.util
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('candidate_shuttle', ROOT/'test_expanding_shuttle.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

def ceildiv(a,b):
    return -((-a)//b)

# A representative finite phase profile, independently checking contact arithmetic.
S,P,V = 3,5,7
hs=(10,12,13,15,16)
ds=(2,1,3,1,2)

def residue_contact(D):
    rho=D%V
    candidates=[]
    for r,(h,d) in enumerate(zip(hs,ds)):
        kappa=ceildiv(rho-2*S-d-h,V)
        if h+kappa*V <= rho+2*S:
            k=(D-rho)//V+kappa
            assert k>=0
            candidates.append((P*k+r,r,k,h+kappa*V-rho))
    return min(candidates)

def brute_contact(D):
    for t in range(2*D+1):
        k,r=divmod(t,P)
        left=hs[r]+k*V
        if D-2*S-ds[r] <= left <= D+2*S:
            return t,r,k,left-D
    raise AssertionError('No contact')

phase_checks=0
for D in range(50,1001):
    assert residue_contact(D)==brute_contact(D)
    t,r,k,z=residue_contact(D)
    t2,r2,k2,z2=residue_contact(D+V*10**70)
    assert (t2-t,r2,k2-k,z2)==(P*10**70,r,10**70,z)
    phase_checks+=1

# Derive the shuttle state at every time, including both collision instants.
def closed(d,t):
    b=2*d-3
    k=(isqrt(b*b+4*t)-b)//2
    assert k>=0
    T=k*k+b*k
    D=d+k
    s=t-T
    assert 0<=s<2*D-2
    if s<=D-2:
        return {0:'u',1+s:'R',D:'u'}
    return {0:'u',2*D-2-s:'L',D+1:'u'}

transition_checks=0
for d in (3,4,7,18,10**20+3):
    for k in (0,1,2,5,37,10**30,10**80):
        D=d+k
        T=k*k+(2*d-3)*k
        for s in sorted(set((0,1,D-3,D-2,D-1,D,2*D-4,2*D-3))):
            if s<0 or s>=2*D-2:
                continue
            assert module.step(closed(d,T+s))==closed(d,T+s+1)
            transition_checks+=1

# Original-frame cutoff, uniformly throughout a cycle, for both drift signs.
cutoff_checks=0
for d in (3,7,20):
    for delta in (-5,-1,1,4):
        for k in range(0,40):
            T=k*k+(2*d-3)*k
            D=d+k
            for s in range(2*D-2):
                support=[x+delta*(T+s) for x in closed(d,T+s)]
                if delta>0:
                    assert min(support)>=delta*T
                else:
                    assert max(support)<=delta*T+D+1
                cutoff_checks+=1

result={'status':'PASS','finite_phase_contacts':phase_checks,
        'large_integer_phase_shifts':phase_checks,
        'closed_shuttle_transition_checks':transition_checks,
        'uniform_original_frame_phase_bounds':cutoff_checks,
        'largest_section_index':str(10**80),
        'scope':'Independent arithmetic checks, not an exhaustive CA or proof check.'}
Path(__file__).with_name('audit-arithmetic-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
