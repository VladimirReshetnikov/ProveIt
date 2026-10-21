#!/usr/bin/env python3
"""Exact first-prefix checks for all placements of the two bootstrap threes.

The prefix is the unchanged 37-leaf K220 command reader. An optional --sites
binds its literal op/register pairs to a source-sites file. The checker stops
before dispatch, so it never evaluates astronomical formula constructors.
"""
import argparse
from itertools import combinations
from math import isqrt
from pathlib import Path
import hashlib
import json

if not __debug__:
    raise RuntimeError('Run without Python optimization')


# Each row is (operation, register/level, zero-or-sole target, positive target).
PREFIX = [
    ('CD',8,2,1), ('CB',1,9,None), ('CD',0,6,3),
    ('CI',8,4,None), ('CI',6,5,None), ('CC',3,2,None),
    ('CI',0,7,None), ('CD',6,9,8), ('CC',2,6,None),
    ('CD',8,17,10), ('CI',7,11,None), ('CD',6,13,12),
    ('CB',1,16,None), ('CD',7,16,14), ('CI',6,15,None),
    ('CC',2,13,None), ('CC',3,9,None), ('CD',7,20,18),
    ('CI',8,19,None), ('CC',2,17,None), ('CD',6,23,21),
    ('CI',3,22,None), ('CC',2,20,None), ('CD',8,31,24),
    ('CI',7,25,None), ('CD',6,27,26), ('CB',1,30,None),
    ('CD',7,30,28), ('CI',6,29,None), ('CC',2,27,None),
    ('CC',3,23,None), ('CD',7,34,32), ('CI',8,33,None),
    ('CC',2,31,None), ('CD',6,37,35), ('CI',4,36,None),
    ('CC',2,34,None),
]


def unP(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b


def walk(a,b,n):
    for _ in range(n):
        a,b=(b+1,0) if a == 0 else (a-1,b+1)
    return a,b


def abstract_prefix(initial):
    v=list(initial)
    if v[8] == 0:
        v[8]=v[0]
        v[0]+=v[6]+1
        v[6]=0
    else:
        v[8]-=1
    ac,rest=walk(v[6],v[7],v[8])
    v[3]+=ac
    x,v[8]=unP(rest)
    v[4]+=x
    v[6]=v[7]=0
    return v


def concrete_prefix(initial):
    v=list(initial)
    pc=steps=0
    while pc != 37:
        assert steps < 100000, ('prefix_failed_to_terminate',initial,pc,v)
        op,r,z,p=PREFIX[pc]
        if op == 'CD':
            if v[r] == 0:
                pc=z
            else:
                v[r]-=1
                pc=p
        else:
            if op == 'CI':
                v[r]+=1
            pc=z
        steps+=1
    return v,steps


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--sites',type=Path)
    args=ap.parse_args()
    binding=None
    if args.sites:
        raw=args.sites.read_bytes()
        rows=json.loads(raw)
        assert [tuple(x[1:]) for x in rows[:37]] == [x[:2] for x in PREFIX]
        binding={'source':str(args.sites),'sha256':hashlib.sha256(raw).hexdigest(),
                 'literal_prefix_effects_match':True,
                 'scope':'Control-flow targets are the independently recorded baseline prefix contract.'}
    results=[]
    for pair in combinations(range(9),2):
        initial=[3 if r in pair else 0 for r in range(9)]
        final,steps=concrete_prefix(initial)
        assert final == abstract_prefix(initial), (pair,final,abstract_prefix(initial))
        assert final[6] == final[7] == 0
        assert all(final[r] == initial[r] for r in (1,2,5))
        assert final[0] <= 7
        results.append({'three_registers':pair,'dispatch_registers':final,'primitive_steps':steps})
    receipt={
        'status':'ALL_36_BOOTSTRAP_PLACEMENTS_REACH_SAFE_DISPATCH',
        'placements':len(results),
        'register_permutations_covered':362880,
        'maximum_next_proof':max(x['dispatch_registers'][0] for x in results),
        'maximum_prefix_steps':max(x['primitive_steps'] for x in results),
        'theorem_seeds':{'current_or_cache_3':'3=E(0,0)',
                         'stack_3':'3=P(2,0), with 2=Q(0,0)'},
        'binding':binding,
        'cases':results,
        'scope':'Initial-reader/source-dispatch safety; does not certify a recompiled TM or global register renaming.',
    }
    Path(__file__).with_name('boot_permutations_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='cases'},indent=2))


if __name__=='__main__':
    main()
