#!/usr/bin/env python3
"""Bind the literal source graphs to the finite-trace transport proof schema.

Independent of the source compiler and both physical symbolic engines. This is
a structural certificate for the elementary counter-loop argument in proof.tex,
not a PA proof-assistant kernel.
"""
from pathlib import Path
import argparse, hashlib, json

HERE=Path(__file__).resolve().parent.parent
COMPARATOR=[['dec',5,4,1],['dec',6,3,2],['jump',0],['jump',5],
            ['dec',6,10,5],['dec',5,7,6],['jump',5],
            ['dec',6,9,8],['jump',5],['jump',11],['halt']]
COMMON_SHIFT=[['dec',1,3645,3643],['inc',6,3644],['jump',3642],
              ['dec',5,3649,3646],['inc',1,3647],['inc',6,3648],['jump',3645]]
OLD_TAIL=[['dec',6,3652,3650],['inc',5,3651],['jump',3649],['inc',6,3653],['jump',0]]
NEW_TAIL=[['inc',5,3650],['jump',0]]

def targets(row):return row[2:] if row[0] in ('inc','dec') else row[1:]
def main():
    assert __debug__
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--machine',type=Path,default=HERE/'machine')
    ap.add_argument('--out',type=Path,default=HERE/'evidence/source_equivalence.json')
    a=ap.parse_args()
    oldfile=HERE/'inputs/qn/instructions.json';newfile=a.machine/'instructions.json'
    old=json.loads(oldfile.read_text());new=json.loads(newfile.read_text())
    assert len(old)==3654 and len(new)==3651
    assert old[:3649]==new[:3649]
    assert old[:11]==new[:11]==COMPARATOR
    assert old[3642:3649]==new[3642:3649]==COMMON_SHIFT
    assert old[3649:]==OLD_TAIL and new[3649:]==NEW_TAIL
    for program in (old,new):
        assert all(0<=t<len(program) for row in program for t in targets(row))
        entries=[[pc,t] for pc,row in enumerate(program[:3649]) for t in targets(row) if t>=3649]
        assert entries==[[3645,3649]]
        assert program[3645]==['dec',5,3649,3646]
    result=dict(status='PASS',initial_source=25,common_instruction_prefix=3649,
        changed_region_entry=3649,sole_external_entry=[3645,3649],
        entry_condition='Logical H (register5) is zero on this zero decrement branch.',
        old_tail_comparator_input='(H,X)=(x,1)',new_tail_comparator_input='(H,X)=(1,x)',
        common_halting_condition='x=1',
        common_nonhalting_exit='source11, H=X=0; all other logical registers unchanged',
        all_store_shift_statement='At3642, input(T,H,X)=(t,h,x): halt iff x+t+h=1; otherwise source11 with(T,H,X)=(h,0,0).',
        local_termination='Counter-transfer loops strictly decrease the transferred natural counter; the comparator decreases H+X.',
        proof='Finite halting traces from source25 translate both ways by replacing whole terminating blocks between entry3649 and exit11 or halt. Induction on the number of block visits gives the PA-provable equivalence.',
        parent_source_sha256=hashlib.sha256(oldfile.read_bytes()).hexdigest(),
        new_source_sha256=hashlib.sha256(newfile.read_bytes()).hexdigest(),
        kernel_checked=False)
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
