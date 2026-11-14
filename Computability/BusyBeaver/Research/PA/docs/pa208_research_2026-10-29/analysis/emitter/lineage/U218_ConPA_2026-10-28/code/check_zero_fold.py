#!/usr/bin/env python3
"""Independent finite-neighborhood proof certificate for known-zero state quotient.

No baseline source/compiler or symbolic simulator is imported.  The finite
5-cell check is exhaustive for the two local invariant clauses and one-step
quotient commutation; this is not bounded trajectory testing.
"""
from pathlib import Path
import argparse, hashlib, itertools, json

def table(path):
    out = {}
    starts = []
    for line in path.read_text().splitlines():
        if line.startswith('#! start'):
            if line != '#! start 0':
                raise ValueError('initial state header must be exactly #! start 0')
            starts.append(0)
            continue
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        key = int(q), int(b)
        if key in out or d not in ('L', 'R'):
            raise ValueError(('invalid table', line))
        target = int(z)
        if key[0] < 0 or target < 0:
            raise ValueError('negative state or target')
        out[key] = int(w), (-1 if d == 'L' else 1), target
    if starts != [0]:
        raise ValueError('exactly one initial state header is required')
    states = {q for q, b in out}
    if len(out) != 2 * len(states) or any((q, b) not in out for q in states for b in (0,1)):
        raise ValueError('table not total on two symbols')
    if any(b not in (0, 1) or w not in (0, 1) for (q,b), (w,d,z) in out.items()):
        raise ValueError('nonbinary symbol')
    if {z for w,d,z in out.values()} - states != {254}:
        raise ValueError('halt target incorrect')
    return out, states

def f(q):
    return 209 if q == 200 else q

def invariant(q, h, t):
    return (q != 112 or t[h+1] == 0) and (q != 200 or t[h] == 0)

def verify_local(old, new, states, predicate=invariant):
    admissible = 0
    for q in sorted(states):
        for bits in itertools.product((0,1), repeat=5):
            tape = dict(zip(range(-2,3),bits))
            if not predicate(q, 0, tape):
                continue
            admissible += 1
            w,d,z = old[q,tape[0]]
            nxt = dict(tape)
            nxt[0] = w
            if not predicate(z,d,nxt):
                raise ValueError(('noninductive invariant',q,bits,(w,d,z)))
            if new[f(q),tape[0]] != (w,d,f(z)):
                raise ValueError(('quotient does not commute',q,bits))
    return admissible

def check(old_path, new_path):
    old, states = table(old_path)
    new, new_states = table(new_path)
    if new_states != states - {200} or len(new_states) != len(states) - 1:
        raise ValueError('incorrect state set')
    if 0 not in states or 0 in (112, 200):
        raise ValueError('initial invariant not automatic')
    if old[200,0] != old[209,0]:
        raise ValueError('agreement row mismatch')
    if new != {(q,b):(w,d,f(z)) for (q,b),(w,d,z) in old.items() if q != 200}:
        raise ValueError('candidate is not exact quotient')
    pred = {q:[[s,b,*v] for (s,b),v in sorted(old.items()) if v[2] == q] for q in (112,200)}
    if pred != {112:[[172,0,0,-1,112]],200:[[112,1,1,1,200]]}:
        raise ValueError(('predecessor certificate differs',pred))
    admissible = verify_local(old, new, states)
    return {
        'status':'EXHAUSTIVE_LOCAL_INVARIANT_AND_QUOTIENT_PASS',
        'old_sha256':hashlib.sha256(old_path.read_bytes()).hexdigest(),
        'new_sha256':hashlib.sha256(new_path.read_bytes()).hexdigest(),
        'old_working_states':len(states),'new_working_states':len(new_states),
        'fold':{'removed':200,'representative':209},
        'invariant':['q=112 implies tape[head+1]=0','q=200 implies tape[head]=0'],
        'predecessors':pred,
        'radius':2,'all_local_frames':len(states)*32,'admissible_local_frames':admissible,
        'initial_state':0,'halt_state':254,
        'scope':'All tapes from state 0. One-step lockstep simulation for every natural time; identical tape, head, and halting time. Proven by induction from the finite local certificate.',
        'kernel_certificate':False
    }

if __name__ == '__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('old',type=Path)
    ap.add_argument('new',type=Path)
    ap.add_argument('--output',type=Path)
    a=ap.parse_args()
    result=check(a.old,a.new)
    text=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')
