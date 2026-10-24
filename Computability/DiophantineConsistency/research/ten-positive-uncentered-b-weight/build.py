#!/usr/bin/env python3
"""Produce the complete uncentered sources from four sealed b-weight parents."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/ten-positive-reused-b-weight'
ROUTES=[('saturated_upper','zero89'),('saturated_sharp','zero89'),('direct_saturated_upper','direct95'),('direct_saturated_sharp','direct95')]
PARENT_SEAL='7042b65701b37773f62b65a4191fdfaaff5d15dccab0374ee5b6e15dcb2c2d1b'
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(p):return sha256(p.read_bytes()).hexdigest()
def encode(d):return (json.dumps(d,indent=2,sort_keys=True)+'\n').encode()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    need(digest(PARENT/'MANIFEST.json')==PARENT_SEAL,'exact reviewed whole b-weight parent')
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'complete frozen dependency '+n)
    for name in pins['closed_dependencies']:
        folder=ROOT/name;files=json.loads((folder/'MANIFEST.json').read_bytes())['files']
        need(set(files)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'},'whole closed dependency '+name)
        for n,h in files.items():need(digest(folder/n)==h,'whole closed member '+name+'/'+n)
    artifacts={};cuts={};sources={}
    for stem,target in ROUTES:
        path=PARENT/(stem+'.json');parent=json.loads(path.read_bytes());rows=[];mapping=[];deleted=[];changed=[]
        for i,row in enumerate(parent['source']):
            if row[0] in ['Cg','nVCg','Afull']:deleted.append(dict(parent_index=i,row=row));continue
            new=list(row)
            if row[0]=='center':need(row==['center','-','nVCg','LBt'],'sole old center consumer');new[2]='nV';changed.append(dict(parent_index=i,new_index=len(rows),old=row,new=new))
            mapping.append(dict(parent_index=i,new_index=len(rows),row=new));rows.append(new)
        need(set(r['row'][0] for r in deleted)==({'Cg','nVCg','Afull'} if 'sharp' in stem else {'Cg','nVCg'}) and len(changed)==1,'exact center-only deletion')
        if target in sources:need(sources[target]==rows,'upper and sharp routes have identical entire source')
        sources[target]=rows
        cuts[stem]=dict(target=target,parent_sha256=digest(path),deleted_rows=deleted,changed_rows=changed,complete_parent_to_new_rows=mapping)
        artifacts['parents/'+stem+'.json']=path.read_bytes()
    for target,rows in sources.items():
        stem='direct_saturated_upper' if target=='direct95' else 'saturated_upper';parent=deepcopy(json.loads((PARENT/(stem+'.json')).read_bytes()))
        parent.update(name='uncentered_b_'+target,source=rows,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=262 if target=='direct95' else 288,parent_sha256=digest(PARENT/(stem+'.json')),parent_manifest_sha256=digest(PARENT/'MANIFEST.json'),proof='PROOF.md',proof_status='Complete ordinary uncentered b-weight theorem; whole coherent fixed tuple retained; no canonical promotion.')
        artifacts[target+'.json']=encode(parent)
    artifacts['CUTS.json']=encode(cuts)
    for name in ['PROOF.md','MANIFEST.json','SOURCE_PINS.json','INDEXED_BINDING.json']:artifacts['parents/'+name]=(PARENT/name).read_bytes()
    artifacts['INDEXED_BINDING.json']=(PARENT/'INDEXED_BINDING.json').read_bytes()
    for p in (PARENT/'coefficients').rglob('*'):
        if p.is_file():artifacts[str(p.relative_to(PARENT))]=p.read_bytes()
    for name,blob in artifacts.items():
        target=HERE/name
        if args.check:need(target.read_bytes()==blob,'deterministic complete generated member '+name)
        else:
            need(not target.exists() or target.read_bytes()==blob,'refuse changed generated overwrite '+name);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(blob)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),check_mode=args.check,generated_files={n:sha256(b).hexdigest() for n,b in artifacts.items()},parent_or_incoming_program_executed=False),indent=2,sort_keys=True))
if __name__=='__main__':main()
