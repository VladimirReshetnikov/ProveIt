#!/usr/bin/env python3
"""Exact state-neutral marker sharing of K215 roles52/176, including deterministic evidence."""
from pathlib import Path
import json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1]/'reference/primary215');ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'machine');args=ap.parse_args()
raw=(args.base/'k215.native.tm').read_bytes();assert hashlib.sha256(raw).hexdigest()=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
T={}
for line in raw.decode().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
assert T[52,0]==(0,1,154) and T[176,0]==(0,1,168) and T[52,1]==T[176,1]==(1,1,150)
assert {key for key,act in T.items()if act[2]==52}=={(190,1),(193,1)}
assert {key for key,act in T.items()if act[2]==176}=={(156,1),(165,0),(193,0)}
assert {key for key,act in T.items()if act[2]==156}=={(189,1)}
assert T[189,1]==(1,-1,156) and T[156,1]==(1,1,176)
assert T[185,0]==(0,1,168) and T[129,0]==(0,1,154)
N={key:(w,d,52 if z==176 else z)for key,(w,d,z)in T.items()}
N[52,0]=(0,-1,176)
N[176,0]=(0,1,185);N[176,1]=(1,1,129)
assert set(N)==set(T) and len(N)==430
# Every state remains graph reachable, with terminal254.
reach={0};todo=[0]
for q in todo:
 for b in(0,1):
  z=N[q,b][2]
  if z!=254 and z not in reach:reach.add(z);todo.append(z)
assert reach=={q for q,b in N}
args.out.mkdir(parents=True,exist_ok=True)
def table(rows,start=0):return (f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(rows.items()))).encode()
(args.out/'marker215.native.tm').write_bytes(table(N))
(args.out/'sites.json').write_bytes((args.base/'sites215.json').read_bytes())
states=sorted(reach);mapping={q:i for i,q in enumerate(states)};mapping[254]=215
D={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in N.items()}
(args.out/'marker215.tm').write_bytes(table(D))
(args.out/'canonicalization.json').write_text(json.dumps({'native_to_dense':mapping,'native_start':0,'dense_start':0,'native_dispatcher':84,'dense_dispatcher':mapping[84],'native_halt':254,'dense_halt':215},indent=2)+'\n')
receipt={'baseline_sha256':hashlib.sha256(raw).hexdigest(),'candidate_sha256':hashlib.sha256(table(N)).hexdigest(),'dense_sha256':hashlib.sha256(table(D)).hexdigest(),'working_states':len(reach),'rows':len(N),'changes':[{ 'state':q,'read':b,'old':T[q,b],'new':N[q,b]}for q,b in sorted(N)if T[q,b]!=N[q,b]],'scheme':'Merge logical52/176 at52; repurpose176 as predecessor marker selector. Incoming156/1 is safe because189/1 fixes its next current cell to1.'}
(args.out/'construction.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
