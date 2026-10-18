#!/usr/bin/env python3
"""Literal seven-new-state unit-stride loader and exact whole-tape replay.

This is a prepared-frame transducer, not a blank-tape initializer. The first
register must be zero. All other unary blocks, including spares, are fixed
at their original absolute coordinates. notes/gap_unit_loader_review.tex
gives a mathematical invariant for every gap >=1 and every valid suffix.
"""
from pathlib import Path
from gap_loader import paint,read_table
import json
ROOT=Path(__file__).resolve().parent.parent

def rows():
    return {
      (300,0):(1,'L',27),(300,1):(0,'R',308),
      (302,0):(0,'L',303),(302,1):(1,'L',302),
      (303,0):(1,'L',33),(303,1):(1,'L',303),
      (305,0):(0,'R',306),(305,1):(1,'R',305),
      (306,0):(0,'L',307),(306,1):(1,'R',306),
      (307,0):(1,'L',7),(307,1):(1,'R',300),
      (308,0):(1,'R',308),(308,1):(1,'R',300),
      (27,1):(0,'L',302),(33,0):(0,'R',305),
    }

CLEANUP_STATES={7,10,14,20,2,4,6,9,13,19,29,41,58,74,84}
# Conservative all-gap support: both rows of every cleanup label are kept.
SUPPORT=set(rows())|{(q,b) for q in CLEANUP_STATES for b in (0,1)}|{(96,1)}

def simulate(table,gap,values,head=0,via_dispatch=True):
    assert gap>=1 and values and values[0]==0
    expected=paint(gap+1,[gap+1]+list(values[1:]),head-gap-2)
    ones=paint(gap,values,head,pc='1' if via_dispatch else '')
    q,h=(96,head) if via_dispatch else (300,head-1)
    steps=2*gap*gap+15*gap+39+via_dispatch
    used=set()
    for n in range(steps):
        assert q!=254,('unexpected halt',gap,n)
        assert q!=96 or n==0,('early dispatcher',gap,n)
        key=q,int(h in ones);used.add(key);w,d,q=table[key]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    assert (q,h,ones)==(96,head-gap-2,expected),('wrong endpoint',gap,q,h)
    assert (27,0) not in used and (33,1) not in used
    assert used<=SUPPORT
    return {'gap':gap,'values':list(values),'initial_head':head,
      'via_dispatch':via_dispatch,'steps':steps,'output_gap':gap+1,
      'output_first_register':gap+1,'output_head':h,
      'all_tape_cells_equal':True,'used_rows':[list(k) for k in sorted(used)]}

def suite(table):
    return [simulate(table,g,values,h,via)
      for g in (1,2,3,4,8,9,39,40,41,63,100,173)
      for values in ([0],[0]*9,[0,2,0,7,1,0,3,4,0],[0,2,0,7,1,0,3,4,0,2,1])
      for h in (-100,0,17) for via in (False,True)]

def main():
    table=read_table();table.update(rows());table[96,1]=(0,'L',300)
    tests=suite(table)
    result={'status':'PASS','scope':__doc__,'new_working_states':7,
      'overwritten_old_rows':[[27,1],[33,0]],'samples':len(tests),
      'time_including_dispatch':'2*g*g+15*g+40','tests':tests}
    (ROOT/'results/unit_loader_results.json').write_text(json.dumps(result,indent=2)+'\n')
    patch='# Prepared-frame transducer PATCH, not a standalone total machine\n'
    patch+=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows().items()))
    (ROOT/'machines/unit_loader_patch.tm').write_text(patch)
    print(json.dumps({k:v for k,v in result.items() if k!='tests'},indent=2))

if __name__=='__main__':main()
