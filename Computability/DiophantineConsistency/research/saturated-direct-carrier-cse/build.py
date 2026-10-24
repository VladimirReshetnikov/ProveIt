#!/usr/bin/env python3
"""Materialize five complete exact direct-carrier contractions."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
ROUTES=[('ten-positive-saturated-pell','direct_saturated_upper','direct_saturated_upper97'),('ten-positive-saturated-pell','direct_saturated_sharp','direct_saturated_sharp98'),('ten-positive-reused-b-weight','direct_saturated_upper','direct_reused_b_upper96'),('ten-positive-reused-b-weight','direct_saturated_sharp','direct_reused_b_sharp97'),('ten-positive-uncentered-b-weight','direct95','direct_uncentered94')]
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(p):return sha256(p.read_bytes()).hexdigest()
def encode(d):return (json.dumps(d,indent=2,sort_keys=True)+'\n').encode()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'whole immutable input '+n)
    for dirname,h in pins['closed_dependencies'].items():
        folder=ROOT/dirname;need(digest(folder/'MANIFEST.json')==h,'exact closed parent seal '+dirname);files=json.loads((folder/'MANIFEST.json').read_bytes())['files'];need(set(files)=={str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'},'closed dependency inventory '+dirname)
        for n,h in files.items():need(digest(folder/n)==h,'whole dependency member '+dirname+'/'+n)
    artifacts={};cuts={}
    for dirname,stem,target in ROUTES:
        folder=ROOT/'research'/dirname;path=folder/(stem+'.json');parent=json.loads(path.read_bytes());rows=[];mapping=[];deleted=[];changed=[];consumers=[r[0] for r in parent['source'] if 'q4' in r[2:]]
        need(consumers==['P1'] and ['qbJ','*','q','bJ'] in parent['source'],'actual sole consumer and shared product')
        for i,row in enumerate(parent['source']):
            if row[0]=='q4':need(row==['q4','*','q3','q'],'exact deleted product');deleted.append(dict(parent_index=i,row=row));continue
            new=list(row)
            if row[0]=='P1':need(row==['P1','*','q4','bJ'],'exact old root product');new=['P1','*','q3','qbJ'];changed.append(dict(parent_index=i,new_index=len(rows),old=row,new=new))
            mapping.append(dict(parent_index=i,new_index=len(rows),row=new));rows.append(new)
        need(len(deleted)==len(changed)==1,'one exact contraction');new=deepcopy(parent);new.update(name=target,source=rows,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),parent_sha256=digest(path),parent_manifest_sha256=digest(folder/'MANIFEST.json'),proof='PROOF.md',proof_status='Exact free polynomial equality to whole sealed parent by sole-consumer direct-carrier contraction; all ordinary/native contracts unchanged.')
        artifacts[target+'.json']=encode(new);artifacts['parents/'+dirname+'/'+stem+'.json']=path.read_bytes();cuts[target]=dict(parent='research/'+dirname+'/'+stem+'.json',parent_sha256=digest(path),q4_consumers=consumers,deleted_rows=deleted,changed_rows=changed,complete_parent_to_new_rows=mapping)
    parent=ROOT/'research/ten-positive-uncentered-b-weight'
    artifacts['CUTS.json']=encode(cuts);artifacts['INDEXED_BINDING.json']=(parent/'INDEXED_BINDING.json').read_bytes()
    for p in (parent/'coefficients').rglob('*'):
        if p.is_file():artifacts[str(p.relative_to(parent))]=p.read_bytes()
    for dirname in {r[0] for r in ROUTES}:
        for name in ['PROOF.md','MANIFEST.json','CHECK.json','CHECK_OPTIMIZED.json']:artifacts['parents/'+dirname+'/'+name]=(ROOT/'research'/dirname/name).read_bytes()
    for n,b in artifacts.items():
        path=HERE/n
        if args.check:need(path.read_bytes()==b,'deterministic whole generated member '+n)
        else:
            need(not path.exists() or path.read_bytes()==b,'refuse changed generated overwrite '+n);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),check_mode=args.check,generated_files={n:sha256(b).hexdigest() for n,b in artifacts.items()},parent_or_incoming_program_executed=False),indent=2,sort_keys=True))
if __name__=='__main__':main()
