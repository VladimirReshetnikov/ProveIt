#!/usr/bin/env python3
"""Try the LC splice on 96 frozen compatible literal tables from the corpus.

Inputs include raw parents, already folded tables and rejected diagnostics.
Scores are raw count minus disjoint raw-action matching; local replay is
recorded separately.  This does not promote any table to a consistency result.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'construction'))
import build
from search_support import proposed_folds

REQUIRED={(139,0):(0,True,190),(139,1):(0,False,16),
          (190,0):(0,True,99),(190,1):(1,True,99),
          (99,0):(0,True,61),(99,1):(1,True,61)}

def main(out):
    assert __debug__
    inputs=ROOT/'research/corpus_loop_inputs'
    catalogue=json.loads((inputs/'index.json').read_text())
    assert len(catalogue)==96
    records=[]
    for entry in catalogue:
        path=inputs/entry['file']
        assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256']
        rows=build.read_table(path)
        assert all(rows.get(k)==v for k,v in REQUIRED.items())
        assert not any(q!=139 and n==190 for (q,b),(w,d,n) in rows.items())
        assert len(rows)//2==entry['states']
        rows[139,0]=(0,True,99)
        rows[139,1]=(1,True,190)
        rows[190,1]=(1,False,73)
        folds=proposed_folds(rows)
        child,aliases=build.apply_folds(rows,folds)
        try:
            local=build.check_folds(rows,child,aliases,folds)
            local_pass=True
        except AssertionError:
            local_pass=False
        count=len(child)//2
        assert count==entry['recorded_projected_states']
        assert count>=194
        records.append(dict(input_sha256=entry['sha256'],source_states=entry['states'],
            folds=len(folds),projected_states=count,local_fold_replay=local_pass))
    result=dict(status='PASS',inputs=len(records),projected_sub194=0,
        histogram=dict(Counter(str(r['projected_states']) for r in records)),
        scope='Frozen compatible tables, the three-row LC change, and disjoint raw-action folds only.',
        results=records)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=ROOT/'research/corpus_loop_receipt.json')
    main(ap.parse_args().out)
