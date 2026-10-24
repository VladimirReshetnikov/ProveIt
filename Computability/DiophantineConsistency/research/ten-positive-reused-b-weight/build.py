#!/usr/bin/env python3
"""Build the one-gate b-weight extension from its complete sealed SAT parent."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/ten-positive-saturated-pell'
CASES=['saturated_upper','saturated_sharp','direct_saturated_upper','direct_saturated_sharp']
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(p):return sha256(p.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    for name,h in pins['files'].items():need(digest(ROOT/name)==h,'whole immutable source '+name)
    manifest=json.loads((PARENT/'MANIFEST.json').read_bytes())['files'];need(set(manifest)=={str(p.relative_to(PARENT)) for p in PARENT.rglob('*') if p.is_file() and p!=PARENT/'MANIFEST.json'},'closed SAT parent')
    for name,h in manifest.items():need(digest(PARENT/name)==h,'whole SAT parent member '+name)
    artifacts={};cuts={}
    for name in CASES:
        parent=json.loads((PARENT/(name+'.json')).read_bytes());new=deepcopy(parent);rows=[];mapping=[];deleted=[];changed=[]
        for i,row in enumerate(parent['source']):
            if row[0]=='L':deleted.append(dict(parent_index=i,row=row));continue
            output=list(row)
            if row[0]=='LBt':output[2]='cTR';changed.append(dict(parent_index=i,new_index=len(rows),old=row,new=output))
            mapping.append(dict(parent_index=i,new_index=len(rows),row=output));rows.append(output)
        need(len(deleted)==len(changed)==1 and deleted[0]['row']==['L','*','k','Tp'],'exact single private product removal')
        new.update(name='reused_b_'+name,source=rows,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),parent_sha256=digest(PARENT/(name+'.json')),parent_manifest_sha256=digest(PARENT/'MANIFEST.json'),proof='PROOF.md',proof_status='Complete ordinary reused-b transport proof; every other saturated kernel and whole coherent binding retained. No canonical promotion by this packet.')
        artifacts[name+'.json']=(json.dumps(new,indent=2,sort_keys=True)+'\n').encode()
        cuts[name]=dict(parent_sha256=digest(PARENT/(name+'.json')),deleted_rows=deleted,changed_rows=changed,complete_parent_to_new_rows=mapping)
        artifacts['parents/'+name+'.json']=(PARENT/(name+'.json')).read_bytes()
    artifacts['CUTS.json']=(json.dumps(cuts,indent=2,sort_keys=True)+'\n').encode()
    for name in ['INDEXED_BINDING.json','INCOMING_MEMBERS.json','REVIEWED_INCOMING_VERIFICATION.json','REVIEWED_INCOMING_VERIFICATION_OPTIMIZED.json']:
        artifacts[name]=(PARENT/name).read_bytes()
    for dirname in ['coefficients','source']:
        for p in (PARENT/dirname).rglob('*'):
            if p.is_file():artifacts[str(p.relative_to(PARENT))]=p.read_bytes()
    for name in ['PROOF.md','MANIFEST.json','CODE_REVIEW.json']:artifacts['parents/'+name]=(PARENT/name).read_bytes()
    for name,data in artifacts.items():
        target=HERE/name
        if args.check:need(target.read_bytes()==data,'deterministic whole generated member '+name)
        else:
            need(not target.exists() or target.read_bytes()==data,'refuse changed generated overwrite '+name);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),check_mode=args.check,artifacts={n:sha256(b).hexdigest() for n,b in artifacts.items()},parent_or_incoming_code_executed=False),indent=2,sort_keys=True))
if __name__=='__main__':main()
