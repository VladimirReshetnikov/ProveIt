#!/usr/bin/env python3
"""Strict deterministic reconstruction of U221 from the pinned U222 table."""
from pathlib import Path
import argparse, hashlib, json

U222_SHA256='88a9c5ea637560bf58dba612d598663213884d7bb7981230164bc058babaa427'
SOURCE_SHA256='1d258cfe56f8b845826a63af57de8134fbc4886b47f95312cf6d49424f3f3072'
U221_NATIVE_SHA256='ea6b259004292b7e8268c20d041ce29ed0b0e7e5428108949b095c40e5a9a7a2'
PARENT_ARCHIVE_SHA256='d23e80857214900f8e0806f03f6df752af501dd0108eb92c6ed7a49795802652'

def require(ok,why):
    if not ok:raise ValueError(why)

def sha(data):return hashlib.sha256(data).hexdigest()

def parse(raw,halt):
    T={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start'):
            require(line=='#! start 0','Invalid start header');starts.append(0)
        elif line.strip() and not line.startswith('#'):
            fields=line.split();require(len(fields)==5,'Wrong row width')
            q,b,w,d,z=fields;q,b,w,z=map(int,(q,b,w,z))
            require(q>=0 and z>=0 and b in(0,1) and w in(0,1) and d in('L','R'),'Invalid row')
            require((q,b)not in T,'Duplicate row');T[q,b]=(w,1 if d=='R' else -1,z)
    require(starts==[0],'Missing or repeated start')
    Q={q for q,b in T}
    require(0 in Q and halt not in Q,'Invalid start/halt states')
    require(set(T)=={(q,b)for q in Q for b in(0,1)},'Incomplete binary table')
    require({z for w,d,z in T.values()}-Q=={halt},'Invalid targets')
    seen={0};todo=[0]
    for q in todo:
        for b in(0,1):
            z=T[q,b][2]
            if z!=halt and z not in seen:seen.add(z);todo.append(z)
    require(seen==Q,'Control-graph unreachable working state')
    return T

def encode(T):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode('ascii')

def build(baseline,source,out):
    oldraw=baseline.read_bytes();src=source.read_bytes()
    require(sha(oldraw)==U222_SHA256,'Wrong U222 baseline bytes')
    require(sha(src)==SOURCE_SHA256,'Wrong source bytes')
    old=parse(oldraw,254);Q={q for q,b in old}
    require(len(Q)==222,'Wrong baseline state count')
    incoming=lambda t:sorted([[q,b,w,d,z]for(q,b),(w,d,z)in old.items()if z==t])
    require(incoming(112)==[[172,0,0,-1,112]],'Wrong predecessor of112')
    require(incoming(200)==[[112,1,1,1,200]],'Wrong predecessor of200')
    require(old[200,0]==old[209,0]==(0,1,157),'Agreement row differs')
    rho=lambda q:209 if q==200 else q
    new={(q,b):(w,d,rho(z))for(q,b),(w,d,z)in old.items()if q!=200}
    native=encode(new);require(sha(native)==U221_NATIVE_SHA256,'Wrong native reconstruction')
    parse(native,254);states=sorted({q for q,b in new});require(len(states)==221,'Wrong count')
    rename={q:i for i,q in enumerate(states)};rename[254]=221
    require(rename[0]==0,'Start renaming failed')
    dense=encode({(rename[q],b):(w,d,rename[z])for(q,b),(w,d,z)in new.items()})
    D=parse(dense,221);inverse={v:k for k,v in rename.items()}
    require({(inverse[q],b):(w,d,inverse[z])for(q,b),(w,d,z)in D.items()}==new,'Relabeling mismatch')
    mapping={'native_to_dense':{str(q):r for q,r in sorted(rename.items())},
             'dense_to_native':{str(r):q for r,q in sorted(inverse.items())},
             'start':0,'native_halt':254,'dense_halt':221,'removed_native_state':200,
             'fold_representative_native':209}
    summary={'status':'EXACT_U221_RECONSTRUCTION_AND_RELABELING_PASS',
             'working_states':221,'transitions':442,'alphabet':[0,1],
             'tapes':1,'heads':1,'moves':['L','R'],'blank_symbol':0,'initial_state':0,
             'native_halt':254,'dense_halt':221,'parent_working_states':222,
             'parent_sha256':U222_SHA256,'native_sha256':sha(native),'dense_sha256':sha(dense),
             'source_sha256':sha(src),'parent_archive_sha256':PARENT_ARCHIVE_SHA256,
             'source_occurrences':len(json.loads(src)),
             'special_native_to_dense':{str(q):rename[q]for q in(112,157,172,209,254)},
             'delta':{'redirect':[112,1,1,1,200,209],'deleted_state':200}}
    out.mkdir(parents=True,exist_ok=True)
    for name,raw in [('u221.native.tm',native),('u221.tm',dense),('sites.json',src)]:
        (out/name).write_bytes(raw)
    for name,data in [('state_map.json',mapping),('machine_summary.json',summary)]:
        (out/name).write_text(json.dumps(data,indent=2)+'\n')
    return summary

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    print(json.dumps(build(a.baseline,a.source,a.output),indent=2))
if __name__=='__main__':main()
