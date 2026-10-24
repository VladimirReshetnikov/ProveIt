#!/usr/bin/env python3
"""Delete the redundant scalar4 gate in the pinned positive11 shear graph."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
PARENT_SHA='b482a1e952536c445918dd5a9e03fdaea0081e0e016e6a1bcbf7be9a26b5a92d'

def need(ok,label):
    if not ok:raise ValueError(label)

def encode(x):return (json.dumps(x,indent=2)+'\n').encode()

def build():
    raw=(HERE/'upstream/parent112.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest()==PARENT_SHA,'pinned parent112')
    p=json.loads(raw)
    rows=p['source'];source=[]
    need(['g67','*','Y','q'] in rows and ['S','*',4,'g67'] in rows,'unique deleted gate')
    need(sum(r[0]=='S' for r in rows)==1,'one original S')
    need(sum(x=='g67' for r in rows for x in r[2:])==1,'single deleted-factor input consumer')
    for name,op,a,b in rows:
        if name=='S':continue
        source.append(['S' if name=='g67' else name,op,a,b])
    p.update(name='positive11_adaptive_double_center_degree211',source=source,operations=111,system_operations=108,operation_breakdown=dict(Counter(r[1] for r in source)),coefficient_binding={'file':'../../con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json','ports':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},'warning':'Complete compact44 tuple; MF is already shifted.'},provenance={'parent_sha256':PARENT_SHA,'change':'S=4qY to S=qY, U=qS; rename g67 to S and delete old scalar4 S gate'},proof_status='Ordinary adaptive-carrier proof in PROOF.md, inherited native/compiler calibration; no new Lean/internal derivation')
    return p

def verify_parent_remap(p):
    old=json.loads((HERE/'upstream/parent112.json').read_text())
    rows={r[0]:r for r in old['source']};new={r[0]:r for r in p['source']}
    need(new['S']==['S','*','Y','q'],'new S literal')
    need(set(new)==set(rows)-{'g67'},'only one gate removed')
    need(all(r==new[n] for n,r in rows.items() if n not in {'g67','S'}),'all other literal rows unchanged')
    available=set(p['witnesses']+p['fixed_numerals']);deps={}
    for n,op,a,b in p['source']:
        need(n not in available and op in ['+','-','*'],'fresh binary row')
        need(all(type(x)is int or x in available for x in [a,b]),'backward operands')
        deps[n]=[x for x in [a,b] if type(x)is str];available.add(n)
    live=set();todo=[p['output']]
    while todo:
        n=todo.pop()
        if n not in live:live.add(n);todo+=deps.get(n,[])
    need(live==available,'all gates,11unknowns,4ports live')
    need(p['operation_breakdown']=={'*':63,'+':31,'-':17},'111op breakdown')
    return {'unchanged_other_rows':110,'deleted_scalar_multiplications':1,'all_gates_inputs_ports_live':True,'operations':111,'multiplications':63,'additions':31,'subtractions':17}

def fixed_binding():
    path=ROOT/'con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json'
    binding=json.loads(path.read_text());ports={};hashes={}
    for x in binding['materialization']['files']:
        packed=(path.parent/x['file']).read_bytes();raw=gzip.decompress(packed)
        need(hashlib.sha256(raw).hexdigest()==x['sha256'],'actual raw coefficient hash')
        need(hashlib.sha256(packed).hexdigest()==x['gzip_sha256'],'actual packed coefficient hash')
        ports[x['port']]=int.from_bytes(raw,'little');hashes[x['port']]=x['sha256']
    beta=ports['beta'];need(beta==(1<<590069)-1 and beta%3==1,'fixed beta')
    need(ports['K']>0 and 0<ports['MC']<beta and 0<ports['MF_source']<2*beta,'coherent mask bounds')
    return {'whole_tuple':'compact44','binding_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'payload_raw_hashes':hashes,'MF_already_shifted':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    for item in json.loads((HERE/'SOURCE_PINS.json').read_text())['retained'].values():
        need(hashlib.sha256((HERE/item['stored']).read_bytes()).hexdigest()==item['sha256'],'retained source pin')
    p=build();data=encode(p)
    output=HERE/'positive11.json'
    if args.check:need(output.read_bytes()==data,'deterministic graph')
    else:output.write_bytes(data)
    receipt={'status':'PASS','literal_sha256':hashlib.sha256(data).hexdigest(),'topology':verify_parent_remap(p),'fixed_binding':fixed_binding(),'scope':'Literal remap/topology/fixed payloads; check.py certifies the finite algebra/degree; PROOF.md supplies ordinary existence proof.'}
    raw=encode(receipt);path=HERE/'BUILD.json'
    if args.check:need(path.read_bytes()==raw,'deterministic receipt')
    else:path.write_bytes(raw)
    print(json.dumps({'status':'PASS','operations':111,'degree':211,'check':args.check}))
if __name__=='__main__':main()
