#!/usr/bin/env python3
"""Reject false invariants and an incorrect replacement, using the fold checker."""
from pathlib import Path
import argparse, copy, json
import check_folds as f
import common as c

def main(parent,output):
    table=f.read_table(parent)
    spec=json.loads((c.ROOT/'inputs/folds.json').read_text())
    fold=spec['folds'][0]
    controls=[]
    def rejected(name,call):
        try:call()
        except (ValueError,KeyError) as exc:
            controls.append(dict(name=name,rejected=True,reason=str(exc)))
        else:raise ValueError('Negative control accepted: '+name)
    rejected('omitted supporting state159 invariant',
             lambda:f.check_inductive_invariant(table,{'118':{'0':0}}))
    rejected('false state118 read-one invariant',
             lambda:f.check_inductive_invariant(table,{'118':{'0':1},'159':{'1':0}}))
    wrong=copy.deepcopy(fold);wrong['a1']=[1,1,173]
    new,_=f.transformed(table,wrong)
    rejected('wrong reclaimed one-row target',
             lambda:f.local_block(new,118,{0:1},(153,1,{0:1}),16))
    premature=copy.deepcopy(spec['folds'][1])
    new,_=f.transformed(table,premature)
    rejected('second fold applied before first fold',
             lambda:f.local_block(new,159,{0:1},(303,1,{0:1}),16))
    answer=dict(status='FOUR_NEGATIVE_CONTROLS_REJECTED',controls=controls)
    c.dump(output,answer)
    return answer

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();print(json.dumps(main(a.parent,a.output),indent=2))
