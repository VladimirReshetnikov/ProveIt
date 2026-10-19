#!/usr/bin/env python3
"""Reproduce the finite counterexample to a direct, unrepaired source rotation."""
from pathlib import Path
import argparse,json,sys
import independent_runtime as r

def main():
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without -O/-OO.')
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    folder=a.root/'research/source_search/rejected_rotation'
    example=json.loads((folder/'experiment.json').read_text())['failure']
    machine=r.table(folder/'machine.tm');site=example['site'];regs=[0]*9
    goal=r.expected(site,regs,[0])[0]
    actual,steps,_=r.run(machine,site[0],regs,[0])
    assert actual!=goal and steps==658
    assert r.describe(actual)==example['actual'] and r.describe(goal)==example['expected']
    result={'status':'PASS_REPRODUCED_REJECTED_ROTATION_COUNTEREXAMPLE','site_index':40,'site':site,'logical_registers':regs,'spares':[0],'gap':0,'steps':steps,'actual':r.describe(actual),'expected':r.describe(goal),'differing_cells':sorted(actual[2]^goal[2]),'scope':'Failure of the intended instruction interface on a valid prepared frame; no claim that this frame is blank-reachable and no state-count lower bound.'}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
