#!/usr/bin/env python3
"""Conditional affine screen for finite box-mixed survivors.

Macros are proposed contracts supported only by finite samples at this stage.
A survivor needs a separate unbounded proof for every altered register box.
"""
import json
from pathlib import Path
import sys
import time
from collections import Counter

HERE=Path(__file__).resolve().parent
BASE=Path('/workspace/scratch/bf00ce1dffdf/source/ProveIt/Computability/BusyBeaver/Research/ZFC')
sys.path.insert(0,str(BASE))
import candidate252_independent_audit as baseline
import breakthrough_register_permutation as affine

def main():
    work=HERE/'affine_scratch'; work.mkdir(exist_ok=True)
    inputs=affine.prepare(baseline.ROOT,work)
    numeric=baseline.read_table((BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes())
    ordinary={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in numeric.items()}
    assert affine.certify(ordinary,baseline.PERM)['passed']
    oracle=affine.strict.oracle
    records=[]; survivors=[]; started=time.monotonic()
    recipes=json.loads((HERE/'box_mixed_results.json').read_text())['survivors']
    for ix,(dead,target,bit) in enumerate(recipes):
        ds,ts=str(dead),str(target)
        def relocated(q,branch,state):
            answer=oracle(q,branch,state)
            if q==ts:
                alias=oracle(ds,branch,state)
                if alias is not None:
                    if answer is not None and alias!=answer:
                        raise AssertionError(('conflicting_proposed_box_inputs',dead,target,state))
                    answer=alias
            if answer is None:return None
            exit_state,effect=answer
            return (ts if exit_state==ds else exit_state),effect
        affine.strict.oracle=relocated
        changed={k:(w,d,ts if t==ds else t) for k,(w,d,t) in ordinary.items() if k[0]!=ds}
        w,d,t=ordinary[ds,bit];changed[ts,bit]=(w,d,ts if t==ds else t)
        check=affine.certify(changed,baseline.PERM)
        rec=dict(deleted=dead,target=target,copied_bit=bit,**check);records.append(rec)
        if check['passed']:
            survivors.append(rec)
            (HERE/f'box_mixed_{dead}_{target}_{bit}.tm').write_bytes(affine.encoded(changed))
            print('CONDITIONAL RUNTIME SURVIVOR',rec,flush=True)
        if ix%100==0:print('PROGRESS',ix,len(survivors),round(time.monotonic()-started,2),flush=True)
    affine.strict.oracle=oracle
    result=dict(scope='Conditional runtime checks of proposed relocated Box contracts; finite box samples do not prove these unbounded contracts.',
                inputs=inputs,recipes=len(records),records=records,survivors=survivors,
                elapsed_seconds=time.monotonic()-started)
    (HERE/'box_mixed_affine_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DONE',len(records),len(survivors),round(time.monotonic()-started,2),flush=True)

if __name__=='__main__':main()
