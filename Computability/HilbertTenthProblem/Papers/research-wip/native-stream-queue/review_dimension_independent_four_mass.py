#!/usr/bin/env python3
"""Independent exact arithmetic checks for the fixed-input mass-four theorem."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

PINS = {'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/19-mass-four-zd-PROOF.md': 'a2cc2bda22d1f3a68435f0f3f7b1c694278e6941f46cdd2ad3de69e512124511', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/data/19-mass-four-zd-source-lineage.json': '143dc15af6bbc1a291add327c3a473bff076754d7fd3cc7aa3e3b30c59892144'}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def same(a, b):
    if type(a) is not type(b): return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b

def plus(a, b): return tuple(x+y for x, y in zip(a, b))
def times(n, a): return tuple(n*x for x in a)
def distance(a, b): return max(abs(x-y) for x, y in zip(a, b))

def ray_index(offset, drift, target):
    # One nonzero coordinate proposes k; every remaining coordinate is checked.
    i = next(i for i, v in enumerate(drift) if v)
    numerator = target[i]-offset[i]
    if numerator % drift[i]: return None
    k = numerator//drift[i]
    return k if k >= 0 and plus(offset, times(k, drift)) == target else None

def first_contact(profile, drift, target, radius):
    options = []
    for phase, points in enumerate(profile):
        for point in points:
            for error in itertools.product(range(-radius, radius+1), repeat=len(drift)):
                offset = plus(point, error)
                k = ray_index(offset, drift, target)
                if k is not None:
                    options.append((len(profile)*k+phase, phase, k, offset))
    return min(options) if options else None

def contacts():
    drift = (4, 2, -2)
    profile = [((0,0,0),(1,0,0)), ((1,0,0),(2,0,0)), ((3,1,-1),(4,1,-1))]
    checked = successful = 0
    for target in itertools.product(range(-4, 7, 2), repeat=3):
        answer = first_contact(profile, drift, target, 2)
        brute = next((t for t in range(61)
                      if any(distance(plus(point, times(t//3, drift)), target) <= 2
                             for point in profile[t%3])), None)
        need(brute == (answer[0] if answer is not None and answer[0] <= 60 else None),
             'ray union equals bounded direct support contact')
        if answer:
            time, phase, k, offset = answer
            need(time == phase+3*k and plus(offset, times(k, drift)) == target,
                 'actual time and complete vector restored')
            # Primitive nu=(2,1,-1), Bezout lambda(v)=v[1], drift=2*nu.
            nu = (2,1,-1);n=target[1];ell=offset[1]
            z=plus(target,times(-n,nu));za=plus(offset,times(-ell,nu))
            need(z==za and (n-ell)%2==0 and (n-ell)//2==k,
                 'transverse offset and residue encode the same ray')
            successful += 1
        checked += 1
    shifts = 0
    for residue in itertools.product(range(-2,3), repeat=3):
        target = plus(times(10, drift), residue)
        first = first_contact(profile, drift, target, 2)
        far = first_contact(profile, drift, plus(target,times(1000000,drift)), 2)
        need((first is None)==(far is None), 'eventual fixed ray eligibility')
        if first:
            need(far[0]-first[0] == 3000000, 'exact large flight-time increment')
        shifts += 1
    need(first_contact(profile,drift,(40,100,0),2) is None,
         'moving toward one coordinate need not hit a marker')
    return dict(dimension=3, bounded_targets=checked, successful_targets=successful,
                periodic_ray_translations=shifts, large_period_shift=1000000,
                off_ray_miss=True, profile_is_claimed_CA_realization=False)

def nonparallel_solution(D, E, rhs):
    pair = next(((i,j) for i in range(len(D)) for j in range(i+1,len(D))
                 if D[i]*E[j]-D[j]*E[i]), None)
    need(pair is not None, 'nonparallel vectors required')
    i,j=pair;det=D[i]*E[j]-D[j]*E[i]
    p=rhs[i]*E[j]-rhs[j]*E[i];q=D[i]*rhs[j]-D[j]*rhs[i]
    if p%det or q%det: return None
    k,h=p//det,q//det
    if min(k,h)<0 or plus(times(k,D),times(h,E)) != rhs: return None
    return k,h

def switches():
    pairs=[((1,0),(0,1)),((2,1),(-1,2)),((1,1,0),(2,2,1)),
           ((2,0,1),(0,3,-1)),((1,-2,1),(2,1,0)),((-2,1,1),(1,1,-2))]
    cases=accepted=0
    for D,E in pairs:
        for rhs in itertools.product(range(-3,4), repeat=len(D)):
            answer=nonparallel_solution(D,E,rhs)
            # Determinants and coefficients in this finite grid bound any
            # solution by18, so the independent 0..20 scan is complete here.
            brute=[(k,h) for k in range(21) for h in range(21)
                   if plus(times(k,D),times(h,E))==rhs]
            need(len(brute)<=1 and answer==(brute[0] if brute else None),
                 'nonparallel full-vector Cramer solution')
            accepted += answer is not None;cases += 1
    D=(2,1,-1);E=times(-1,D)
    for k in (0,1,17,1000000):
        need(plus(times(k,D),times(k,E))==(0,0,0), 'parallel family is unbounded')
    try:
        nonparallel_solution(D,E,(0,0,0))
    except ValueError:
        pass
    else:
        raise ValueError('parallel system must not receive a false finite-switch certificate')
    return dict(vector_pairs=len(pairs), integer_right_sides=cases, accepted=accepted,
                parallel_guard=True, higher_coordinate_consistency=True)

def counter_cycles():
    N=10;x=29;results=[]
    for increments in ((2,-1,2),(2,-1,-1),(2,-4,-1)):
        prefix=[0]
        for step in increments: prefix.append(prefix[-1]+step)
        delta=prefix[-1]
        need(delta%3==0, 'enlarged residue returns')
        minimum=min(x+p for p in prefix)
        need(minimum>N, 'first cycle is live')
        if delta<0:
            last=(minimum-N-1)//(-delta)
            need(all(x+n*delta+p>N for n in range(last+1) for p in prefix), 'all accelerated cycles live')
            need(any(x+(last+1)*delta+p<=N for p in prefix), 'first invalid cycle is found')
            kind='finite descent';valid=last+1
        else:
            # Every future cycle adds a nonnegative multiple of delta to
            # every already-positive guard; no finite sample substitutes.
            kind='translated periodic' if delta==0 else 'expanding';valid=None
        results.append(dict(increments=list(increments),delta=delta,case=kind,
                            consecutive_wholly_live_cycles=valid))
    return results

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo-root',type=Path,required=True)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--expect',type=Path)
    a=ap.parse_args()
    for path,pin in PINS.items():
        need(sha((a.repo_root/path).read_bytes())==pin,'source pin '+path)
    r=dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),proof_pins=PINS,
           contacts=contacts(),nonparallel_switches=switches(),counter_cycles=counter_cycles(),
           scope='Finite exact arithmetic fixtures for the independently read theorem. No general CA analyzer or compiler is implemented, no archive code executes, and no universal arithmetic bound follows.')
    if a.expect:need(same(r,json.loads(a.expect.read_text())),'exact typed receipt')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:r[k] for k in ('status','contacts','nonparallel_switches','counter_cycles')},sort_keys=True))

if __name__=='__main__':main()
