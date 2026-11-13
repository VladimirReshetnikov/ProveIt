#!/usr/bin/env python3
"""Verify that the two {56,96} fold candidates halt on the blank tape."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('pa196_local_folds', HERE.parent / 'scan_local_folds.py')
fold = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fold)

def require(condition, message):
    if not condition:
        raise ValueError(message)

def step(table, state, head, tape, candidate=None):
    bit = int(head in tape)
    if candidate is not None and state == candidate[1]:
        row = candidate[2][bit]
    else:
        row = table[state,bit]
    write, direction, target = row
    if write:
        tape.add(head)
    else:
        tape.discard(head)
    if candidate is not None and target == candidate[0]:
        target = candidate[1]
    return target, head + direction

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    table, table_sha = fold.read_table(fold.DEFAULT_TABLE)
    parent_tape = set()
    parent_state, parent_head = 0, 0
    for i in range(5620):
        require(parent_state != 196, f'parent halted before witness at {i}')
        parent_state, parent_head = step(table, parent_state, parent_head, parent_tape)
    require((parent_state,parent_head,len(parent_tape)) == (96,8,35), 'unexpected parent witness')
    expected_relative = [-11,-10,-7,-4,-3,-1,0,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,19,21,23,25,27,29,31,32,34,36,37,39,40]
    require(sorted(x-parent_head for x in parent_tape) == expected_relative, 'parent full tape mismatch')
    candidates = ((56,96,((0,1,59),(1,1,67))), (96,56,((0,1,59),(1,1,67))))
    results=[]
    for candidate in candidates:
        drop, keep, rows = candidate
        state,head=0,0
        tape=set()
        digest=hashlib.sha256()
        for i in range(12039):
            require(state != 196, f'candidate {drop},{keep} halted early at {i}')
            digest.update(f'{state} {head} {int(head in tape)}\n'.encode('ascii'))
            state,head=step(table,state,head,tape,candidate)
            if i+1==5624:
                require(state==keep and head==parent_head and tape==parent_tape,
                        f'candidate {drop},{keep} missed projected boundary at {i+1}')
        require(state==196 and head==1 and len(tape)==29, f'candidate {drop},{keep} did not halt as expected')
        results.append({'drop':drop,'keep':keep,'row0':[rows[0][0],'R',rows[0][2]],
                        'row1':[rows[1][0],'R',rows[1][2]],'working_states':195,
                        'projected_parent_boundary':{'parent_step':5620,'child_step':5624,
                            'parent_state':96,'child_state':keep,'head':8},
                        'first_halt_step':12039,'halt_state':196,'halt_head':head,
                        'final_one_cells':sorted(tape),'trace_sha256':digest.hexdigest()})
    report={'pa196_table_sha256':table_sha,'parent_witness_step':5620,'parent_witness_state':96,
            'parent_witness_head':8,'parent_one_cells_relative_to_head':expected_relative,
            'candidates':results}
    data=json.dumps(report,indent=2,sort_keys=True)+'\n'
    print(data,end='')
    if args.output: args.output.write_text(data)

if __name__ == '__main__': main()
