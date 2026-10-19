#!/usr/bin/env python3
"""Finite, whole-tape controls for the added search infrastructure.

This verifies the inherited positive reduction, the terminal observation rule,
input pins, and the exact change in the neutral helper catalogue. It is not a
proof of a new 236-state machine or a lower bound.
"""
from collections import deque, defaultdict
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def table(name):
    raw = (ROOT / 'input' / name).read_bytes()
    rows = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'): continue
        q, b, w, d, z = line.split()
        assert d in ('L','R')
        rows[int(q),int(b)] = (int(w),1 if d == 'R' else -1,int(z))
    states = {q for q,b in rows}
    assert set(rows) == {(q,b) for q in states for b in (0,1)}
    assert {z for w,d,z in rows.values()} - states == {254}
    return rows, sha256(raw).hexdigest()

old, old_hash = table('machine238.tm')
new, new_hash = table('machine237.tm')
assert old_hash == 'ab1f12ceb0b1cbc167977286652dd3be3407e9b24fcd3f8e7c9ac630166514b9'
assert new_hash == 'a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a'
assert (len(old),len(new)) == (476,474)
mp = lambda q: 98 if q == 235 else q
expected = {(q,b):(w,d,mp(z)) for (q,b),(w,d,z) in old.items() if q != 235}
expected[98,0]=(0,-1,240)
expected[240,1]=(1,-1,87)
assert expected == new

# A sufficient inductive invariant for the inherited all-tape fold.
guards = {98:{-1:0},139:{-1:1},156:{-1:1},235:{-2:1,-1:1},240:{-1:0}}
def invariant(q,h,t):
    return all(t[h+k] == b for k,b in guards.get(q,{}).items())
closure = 0
for bits in product((0,1),repeat=7):
    tape = dict(zip(range(-3,4),bits))
    assert invariant(95,0,tape)
    for q in {q for q,b in old}:
        if invariant(q,0,tape):
            w,d,z=old[q,tape[0]]
            t=dict(tape);t[0]=w
            assert invariant(z,d,t)
            closure += 1

def symbolic(T,q,guard,n):
    head=0; changed={}
    initial=lambda h:guard.get(h,('independent_arbitrary_bit',h))
    for _ in range(n):
        b=changed.get(head,initial(head))
        assert type(b) is int and b in (0,1), ('unbound branch',q,head,b)
        w,d,z=T[q,b]
        if w == initial(head): changed.pop(head,None)
        else: changed[head]=w
        q,head=z,head+d
    return q,head,changed

specs=[(98,0,{-1:0},3),(235,0,{-2:1,-1:1},5),(240,1,{-1:0},3)]
exceptional={(q,b) for q,b,g,n in specs}
for q,b,g,n in specs:
    guard={**g,0:b}
    oq,oh,ot=symbolic(old,q,guard,1)
    assert (mp(oq),oh,ot) == symbolic(new,mp(q),guard,n)
for (q,b),(w,d,z) in old.items():
    if (q,b) not in exceptional: assert new[mp(q),b] == (w,d,mp(z))

# The source-constrained empirical profile is a subset of the syntactic
# all-tape window abstraction. This does NOT make the profile exhaustive.
L=5;W=11;N=1<<W;mask=N-1
inv=defaultdict(set);inv[95]=set(range(N));todo=deque((95,t) for t in inv[95])
while todo:
    q,t=todo.popleft()
    if q==254: continue
    w,d,z=new[q,(t>>L)&1]
    u=(t&~(1<<L))|(w<<L)
    ys=(u>>1,(u>>1)|(1<<(W-1))) if d==1 else ((u<<1)&mask,((u<<1)&mask)|1)
    for v in ys:
        if v not in inv[z]: inv[z].add(v);todo.append((z,v))
profile=[tuple(map(int,l.split())) for l in (ROOT/'input/profile5.txt').read_text().splitlines()]
assert len(profile)==29192 and len(set(profile))==29192
assert all(t in inv[q] for q,t in profile)
assert sum(map(len,inv.values()))==93177

# Exactly three added terminal substitutions; all lie at merge endpoint77
# and hence are excluded as helpers in every terminal state77 search.
def catalogue(path):
    return {tuple(map(int,l.split()[:5])) for l in path.read_text().splitlines()}
a=catalogue(ROOT/'input/helpers_strict.txt')
b=catalogue(ROOT/'results/neutral_terminal237.txt')
added={(77,1,0,-1,254),(77,1,0,1,254),(77,1,1,-1,254)}
assert len(a)==601 and len(b)==604 and a<=b and b-a==added
assert {x for x in a if x[0]!=77} == {x for x in b if x[0]!=77}

# A synthetic terminal-only control. It serves solely to validate the search
# rule that halting tapes and positions need not agree.
toy,_=table('terminal_toy.tm')
toynew={k:(w,d,77 if z==96 else z) for k,(w,d,z) in toy.items() if k[0]!=96}
toynew[77,0]=toynew[77,1]=(0,-1,254)
def run_toy(T,bits):
    tape={i-3:b for i,b in enumerate(bits)}
    q=95;h=0
    for n in range(1,10):
        assert -3<=h<=3
        w,d,z=T[q,tape[h]];tape[h]=w;q=z;h+=d
        if q==254:return n,h,tape
    raise AssertionError('nonhalting toy control')
old_lengths=[];new_lengths=[]
for bits in product((0,1),repeat=7):
    a0=run_toy(toy,bits);b0=run_toy(toynew,bits)
    old_lengths.append(a0[0]);new_lengths.append(b0[0])
assert set(old_lengths)=={2,3,4} and set(new_lengths)=={2}
blank_old=run_toy(toy,[0]*7);blank_new=run_toy(toynew,[0]*7)
assert blank_old[1:]!=blank_new[1:]

# Search-engine controls: these are exact retained output records, and can be
# regenerated by run_searches.py --controls.
assert 'HELPER 240 1 1 -1 87 FOLD 98 235 ENCODE 0 0 DIR 1 1 ROWS 0 -1 240; 1 1 16' in (ROOT/'results/control_238_237.txt').read_text().splitlines()
assert 'CANDIDATE 77 96 ENCODE 0 0 DIR 1 -1 ROWS 0 -1 254; 0 -1 254' in (ROOT/'results/control_terminal.txt').read_text().splitlines()

receipt={
 'status':'PASS_CONTROLS_NOT_A_NEW_MACHINE',
 'machine238_sha256':old_hash,'machine237_sha256':new_hash,
 'known_fold':{'deleted':235,'retained':98,'inductive_window_cases':closure,
               'open_tape_exceptional_blocks':3,'durations':[3,5,3],
               'ordinary_commuting_rows':len(old)-len(exceptional)},
 'profile':{'finite_windows':len(profile),'all_tape_abstract_windows_including_halt':93177,
            'outside_abstract_invariant':0,'finite_profile_is_not_exhaustive':True},
 'terminal_catalogue':{'strict':601,'terminal':604,'added':[list(x) for x in sorted(added)],
                        'helper_domains_identical_after_excluding_state77':True},
 'synthetic_terminal_control':{'all_tape_window_cases':128,'old_step_counts':sorted(set(old_lengths)),
                               'new_step_count':2,'blank_final_head_and_tape_differ':True},
 'new_sub237_machine_found':False,'state_lower_bound_claimed':False}
print(json.dumps(receipt,indent=2))
