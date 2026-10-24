#!/usr/bin/env python3
"""Materialize two complete lower-degree-weight graphs from pinned parents."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/ten-positive-expanded-transport'
def need(ok,why):
    if not ok:raise ValueError(why)
def dump(obj):return (json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()
def digest(b):return sha256(b).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    for name,h in pins['files'].items():need(digest((ROOT/name).read_bytes())==h,'whole parent pin '+name)
    result={}
    for direct,name,degree in [(False,'zero98.json',360),(True,'direct103.json',332)]:
        raw=(PARENT/name).read_bytes();parent=json.loads(raw);data=deepcopy(parent)
        changes=[]
        for i,row in enumerate(data['source']):
            if row[0]=='HI':new=['kI','*','k','I']
            elif row[0]=='L':new=['L','+','kI','cTR']
            else:continue
            changes.append(dict(index=i,old=deepcopy(row),new=new));data['source'][i]=new
        need(len(changes)==2,'only weight product and its L operand changed')
        data.update(name='ten_positive_index_weight_'+('direct103' if direct else 'zero98'),exact_degree=degree,parent_sha256=digest(raw),proof='PROOF.md',proof_status='Complete ordinary index-weight reduction with fresh canonical witnesses; independently checked degree/count. No pointwise parent equality or Lean theorem asserted.')
        data['register_degrees']['L']=6
        cuts=dict(parent_file=name,parent_sha256=digest(raw),changed_rows=changes,retained_rows=[dict(index=i,row=row) for i,row in enumerate(parent['source']) if i not in {x['index'] for x in changes}],deleted_rows=[],inserted_rows=[],witness_map='fresh canonical n; no pointwise old-new polynomial identity')
        for target,obj in [(name,data),(name.replace('.json','_CUTS.json'),cuts)]:
            blob=dump(obj);path=HERE/target
            if args.check:need(path.read_bytes()==blob,'deterministic complete artifact '+target)
            else:need(not path.exists() or path.read_bytes()==blob,'refuse changed artifact overwrite');path.write_bytes(blob)
            result[target]=digest(blob)
    print(json.dumps(dict(status='PASS',check_mode=args.check,optimized_python=bool(sys.flags.optimize),artifacts=result),indent=2,sort_keys=True))
if __name__=='__main__':main()
