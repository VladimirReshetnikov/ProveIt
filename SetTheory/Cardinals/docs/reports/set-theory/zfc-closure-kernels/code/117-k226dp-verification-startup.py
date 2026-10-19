#!/usr/bin/env python3
"""Recompute the complete blank bootstrap, in two tape representations.

The endpoint is built from the literal Boot230.v register/zero-gap recipe,
not from a saved finite tape sample. Both implementations compare the entire
finite support; every cell outside it is zero.
"""
from pathlib import Path
import argparse, hashlib, json, sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import build

VALUES = [0,0,0,3,0,0,3,0,0] + [1]*167

def expected():
    head = -5; support = {head-1,head+181}; p = head+182
    for v in VALUES:
        p += 1
        support.update(range(p,p+v+1)); p += v+1
    return support

def sparse(table, ticks):
    state = 95; head = 0; ones = set(); first_dispatch = None
    for time in range(ticks):
        build.require(state != 254, 'Early bootstrap halt')
        w,d,state = table[state,int(head in ones)]
        if w: ones.add(head)
        else: ones.discard(head)
        head += d
        if state == 96 and first_dispatch is None: first_dispatch = time+1
    return state,head,ones,first_dispatch

def zipper(table, ticks):
    state = 95; head = 0; left = []; right = []
    for _ in range(ticks):
        read = right[-1] if right else 0
        w,d,state = table[state,read]
        if right: right.pop()
        if d == 1:
            left.append(w); head += 1
        else:
            right.append(w); right.append(left.pop() if left else 0); head -= 1
    ones = {head+i for i,b in enumerate(reversed(right)) if b}
    ones.update(head-1-i for i,b in enumerate(reversed(left)) if b)
    return state,head,ones

def audit(path,ticks):
    table = build.parse(path.read_bytes(),95,254)
    q,h,ones,first = sparse(table,ticks)
    build.require((q,h,ones) == zipper(table,ticks), 'Independent simulators differ')
    build.require((q,h) == (96,-5) and ones == expected(), 'Wrong calibrated endpoint')
    build.require(len(ones) == 351, 'Unexpected tape support census')
    # The first source leaf is 000, represented by the first three of the
    # same 181 zero cells. Thus the runtime engine gap parameter is 181-64.
    return {'status':'EXACT_WHOLE_TAPE_BOOTSTRAP_PASS',
            'table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'working_states':len(table)//2,'steps':ticks,
            'earlier_visits_to_state96_are_allowed':True,
            'dispatcher':q,'head':h,'one_cells':sorted(ones),'all_other_cells':0,
            'independent_representations':['sparse one-cell set','two list zipper'],
            'first_leaf':'000','extra_gap':117,
            'logical_primary_values':[3,0,0,0,3,0,0,0,0],
            'physical_primary_values':VALUES[:9],'first_spare':1,'remaining_spares':[1]*166}

if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path); ap.add_argument('--steps',type=int,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args(); result=audit(a.table,a.steps); build.dump(a.output,result)
    print(json.dumps({k:v for k,v in result.items() if k not in ('one_cells','remaining_spares')},indent=2))
