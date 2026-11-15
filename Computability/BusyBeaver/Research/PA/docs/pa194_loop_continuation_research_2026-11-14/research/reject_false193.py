#!/usr/bin/env python3
"""Replay a tempting 193-state rewrite and its exact source-level rejection.
The existing state46 is not increment-T followed by continue3: it also
increments register6 and changes the continuation target.  The candidate
is an explicit rejected experiment, never a Con(PA) construction.
"""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'construction'))
import build

def main(out):
    raw,nodes,ax,oldsites,oldins,parent=build.load_inputs()
    nodes['node62']=((build.INC,'node60'),'node50')
    sites,ins=build.source(nodes,ax)
    raw[139,0]=(0,True,330);raw[139,1]=(1,True,46)
    raw[330,0]=(0,True,61);raw[330,1]=(1,True,99)
    del raw[190,0];del raw[190,1]
    folds=json.loads((build.INPUT/'folds.json').read_text())+[[41,99,[[0,False,30],[1,False,2035]]]]
    rows,aliases=build.apply_folds(raw,folds);local=build.check_folds(raw,rows,aliases,folds)
    assert len(rows)//2==193 and ins!=oldins and len(ins)==3734
    cycle=ins[124:130]
    assert cycle==[['inc',1,125],['inc',1,126],['inc',1,127],['inc',1,128],['inc',6,129],['jump',124]]
    assert ins[123]==['dec',7,130,124]
    # One complete counter-independent cycle: no test is made after entry.
    pc=124;registers=[0]*9
    for _ in range(6):
        row=ins[pc]
        if row[0]=='inc':registers[row[1]]+=1;pc=row[2]
        else:assert row[0]=='jump';pc=row[1]
    assert pc==124 and registers==[0,4,0,0,0,0,1,0,0]
    seed=build.startup(rows,sites[25][0])
    out.mkdir(parents=True,exist_ok=True)
    (out/'REJECTED_machine.native.tm').write_text(build.table_text(rows))
    build.dump(out/'rejection.json',dict(states=193,local_fold_cases=local['count'],startup_steps=seed['steps'],
      primary_sites=3673,candidate_sites=3734,source_instructions_identical=False,
      entry_instruction=ins[123],cycle_entry=124,cycle=cycle,per_cycle_register_increase=registers,
      reason='Positive entry into this constructor loop never returns to its decrement test; T grows by4 and register6 by1 per six source instructions.',
      status='REJECTED: not a source-preserving consistency construction'))
    print((out/'rejection.json').read_text())

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,default=ROOT/'research/rejected193')
    main(p.parse_args().out)
