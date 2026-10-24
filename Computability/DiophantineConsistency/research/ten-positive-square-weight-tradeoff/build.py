#!/usr/bin/env python3
"""Materialize existing-square transport graphs from exact sealed parents."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/ten-positive-index-weight'
def need(ok,why):
    if not ok:raise ValueError(why)
def dump(obj):return (json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()
def digest(b):return sha256(b).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    for name,h in json.loads((HERE/'SOURCE_PINS.json').read_bytes())['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole parent pin '+name)
    result={}
    for direct,oldname,name,exact in [(False,'zero98.json','zero97.json',368),(True,'direct103.json','direct102.json',344)]:
        raw=(PARENT/oldname).read_bytes();old=json.loads(raw);data=deepcopy(old);rows=[];records=[]
        for i,row in enumerate(old['source']):
            if row[0]=='kI':records.append(dict(parent_index=i,old_row=row,status='deleted_private'));continue
            new=['L','+','I2','cTR'] if row[0]=='L' else deepcopy(row)
            records.append(dict(parent_index=i,old_row=row,child_index=len(rows),new_row=new,status='replaced_operand' if row[0]=='L' else 'retained'));rows.append(new)
        need(len(rows)==len(old['source'])-1,'exactly one deleted private product')
        data.update(name='ten_positive_square_weight_'+('direct102' if direct else 'zero97'),source=rows,operations=len(rows),exact_degree=exact,parent_sha256=digest(raw),proof='PROOF.md',proof_status='Complete ordinary existing-square weight reduction with positive triangular n shear; exact full literal/count/degree verification. No same-input parent equality or Lean theorem asserted.')
        data['operation_breakdown']['*']-=1;data['register_degrees']['L']=10
        cuts=dict(parent_file=oldname,parent_sha256=digest(raw),all_parent_rows=records,inserted_child_rows=[],existing_square='I2=I*I',positive_completeness_shear='n_new=n_parent+I*(I-k)*B')
        for target,obj in [(name,data),(name.replace('.json','_CUTS.json'),cuts)]:
            blob=dump(obj);path=HERE/target
            if args.check:need(path.read_bytes()==blob,'deterministic complete artifact '+target)
            else:need(not path.exists() or path.read_bytes()==blob,'refuse changed artifact overwrite');path.write_bytes(blob)
            result[target]=digest(blob)
    print(json.dumps(dict(status='PASS',check_mode=args.check,optimized_python=bool(sys.flags.optimize),artifacts=result),indent=2,sort_keys=True))
if __name__=='__main__':main()
