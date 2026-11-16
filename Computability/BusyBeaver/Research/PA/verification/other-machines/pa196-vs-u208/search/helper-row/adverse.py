#!/usr/bin/env python3
"""Verify larger blank-window closures and one admitted full-tape mismatch."""
from __future__ import annotations
import argparse
import importlib.util
import json
import subprocess
import tempfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('helper',HERE/'replay.py')
helper=importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
require=helper.require

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    fold=helper.load_fold();table,digest=fold.read_table(fold.DEFAULT_TABLE)
    with tempfile.TemporaryDirectory(prefix='pa196-window-') as directory:
        temp=Path(directory);binary=temp/'window';source=temp/'table.txt'
        source.write_text(helper.table_text(table),encoding='ascii')
        subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-Werror',str(HERE/'window_closure.cpp'),'-o',str(binary)],check=True)
        closures=[]
        for radius in (6,7,8):
            out=subprocess.run([str(binary),str(source),str(radius)],check=True,capture_output=True,text=True).stdout.split()
            expected_keys=['radius','closure','projected','may_halt','state184_mask6','full_contexts','target_mask410']
            require(out[::2]==expected_keys,f'unexpected closure output: {out}')
            closures.append(dict(zip(out[::2],map(int,out[1::2]))))
        require([(x['closure'],x['projected'],x['full_contexts']) for x in closures]==
                [(270067,2774,32),(910501,2774,64),(3131937,2774,192)], 'closure mismatch')
        require(all(x['may_halt']==1 and x['state184_mask6']==1 for x in closures), 'target not admitted')
        require(closures[-1]['target_mask410']==1, 'radius-eight full window absent')
    # The abstractly admitted 17-bit window mask 410, extended with zeros,
    # has exactly these five one-cells. This extension is not asserted to
    # occur in the actual PA196 blank run.
    tape={-7,-5,-4,-1,0}
    require(sum((1<<(i+8)) for i in tape)==410, 'wrong window mask')
    parent_state=184;parent_head=0
    write,direction,target=table[parent_state,1]
    require((write,direction,target)==(1,1,78), 'parent step changed')
    expected=(78,1,set(tape));state,head=184,0;trace=[]
    require(table[35,0]==(1,1,35), 'rightward blank-sweep row changed')
    for i in range(11):
        if state==35 and all(x<head for x in tape):break
        require(state!=196 and i<10, 'expected sweep was not reached')
        bit=int(head in tape)
        w,d,n=(1,-1,75) if (state,bit)==(184,1) else table[state,bit]
        trace.append([state,head,bit,w,'R' if d==1 else 'L',160 if n==45 else n])
        if w:tape.add(head)
        else:tape.discard(head)
        state,head=(160 if n==45 else n),head+d
        require((state,head,tape)!=expected, 'parent endpoint matched before the sweep')
    require((len(trace),state,head)==(10,35,2), 'unexpected finite trace')
    # From the current state, every cell at or to the right is zero. The
    # checked row writes one, moves right, and returns to state 35; induction
    # therefore proves it can never reach the parent's projected state 78.
    result={'pa196_table_sha256':digest,'closures':closures,'parent_state':184,
        'parent_read':1,'window_radius':8,'window_mask':410,
        'initial_one_cells':[-7,-5,-4,-1,0], 'parent_one_step_state':78,'parent_one_step_head':1,
        'patch_state':184,'patch_read':1,'patch':[1,'L',75], 'drop':45,'keep':160,
        'trace':trace,'sweep_start_step':len(trace),'sweep_state':35,'sweep_head':2,
        'sweep_row':[1,'R',35],'actual_blank_reachability_not_established':True}
    output=json.dumps(result,indent=2,sort_keys=True)+'\n';print(output,end='')
    if args.output:args.output.write_text(output)

if __name__=='__main__':main()
