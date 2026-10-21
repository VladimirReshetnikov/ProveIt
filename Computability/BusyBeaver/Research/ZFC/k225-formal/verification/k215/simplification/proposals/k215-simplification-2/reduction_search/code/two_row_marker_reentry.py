#!/usr/bin/env python3
"""Two-row marker-helper fusion with independent positive join blocks.
Discovery allows same-read branch reentry; opposite-read branch reentry is excluded. Incomplete.
"""
from pathlib import Path
import argparse,collections,hashlib,importlib.util,itertools,json,time
p=argparse.ArgumentParser();p.add_argument('--checker',type=Path,required=True);p.add_argument('--table',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--radius',type=int,default=7);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
s=importlib.util.spec_from_file_location('joint_checker',a.checker);b=importlib.util.module_from_spec(s);s.loader.exec_module(b)
T,start=b.read(a.table);Q=sorted({q for q,_ in T});drop=176;assert drop in Q;I=b.domain(T,start,a.radius);R=sorted(set(Q)-{drop});width=2*a.radius+1;fuel=97
patterns={(q,c):sorted(m for m in I[q] if (m>>a.radius)&1==c)for q in Q for c in(0,1)}
for key,ps in patterns.items():
 if len(ps)>2:patterns[key]=[ps[0],ps[-1],*ps[1:-1]]
paths={};counters=collections.Counter();tried=0;viables=[];hits=[];now=time.monotonic()
def oldpath(q,m):
 if(q,m)in paths:return paths[q,m]
 sq,sh,sm=q,0,m;path=[]
 for k in range(1,fuel+1):
  if sq==254 or not -a.radius<=sh<=a.radius:break
  ob=(sm>>(sh+a.radius))&1;w,d,sq=T[sq,ob];sm=(sm&~(1<<(sh+a.radius)))|(w<<(sh+a.radius));sh+=d;path.append((sq,sh,sm))
 paths[q,m]=path;return path
def branch(keep,bit,action):
 phi=lambda q:keep if q==drop else q
 for q in(keep,drop):
  w,d,z=T[q,bit]
  if action==(w,d,phi(z)):continue
  for word in patterns[q,bit]:
   path=oldpath(q,word);goals={(phi(z),h,m)for z,h,m in path};old_halts=any(z==254 for z,h,m in path)
   w,d,z=action;nq=z;nh=d;nm=(word&~(1<<a.radius))|(w<<a.radius);seen=set()
   for tick in range(1,fuel+1):
    if nq==254:
     if old_halts:break
     return 'new_halt'
    if (nq,nh,nm)in goals:break
    if not -a.radius<=nh<=a.radius:return 'window_exit'
    if nq==keep and ((nm>>(nh+a.radius))&1)!=bit:return 'opposite_branch_reentry'
    if(nq,nh,nm)in seen:return 'repeated'
    seen.add((nq,nh,nm));nb=(nm>>(nh+a.radius))&1;w,d,z=action if nq==keep else T[nq,nb];nq=phi(z);nm=(nm&~(1<<(nh+a.radius)))|(w<<(nh+a.radius));nh+=d
   else:return 'fuel'
 return 'PASS'
for keep in R:
 rows=[]
 for bit in(0,1):
  actions=[]
  for act in itertools.product((0,1),(-1,1),R+[254]):
   tried+=1;out=branch(keep,bit,act);counters[out]+=1
   if out=='PASS':actions.append(act)
  rows.append(actions)
 viables.append({'keep':keep,'zero':rows[0],'one':rows[1]})
 if rows[0] and rows[1]:
  for a0,a1 in itertools.product(*rows):
   phi=lambda q:keep if q==drop else q
   N={(q,c):(w,d,phi(z))for(q,c),(w,d,z)in T.items()if q!=drop};N[keep,0]=a0;N[keep,1]=a1
   proof=b.check(T,N,start,phi(start),keep,drop,a.radius,fuel,I)
   name=f'candidate-{keep}-{len(hits)}.tm';raw=(f'#! start {phi(start)}\n'+''.join(f'{q} {c} {w} {"R"if d==1 else"L"} {z}\n'for(q,c),(w,d,z)in sorted(N.items()))).encode();(a.output/name).write_bytes(raw)
   hits.append({'keep':keep,'rows':[a0,a1],'file':name,'sha256':hashlib.sha256(raw).hexdigest(),'proof':proof});print('HIT',keep,a0,a1,flush=True)
 if keep%20==0:print('progress',keep,tried,round(time.monotonic()-now,2),flush=True)
result={'status':'COMPLETE_BOUNDED_TWO_ROW_SEARCH','table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(a.checker.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'drop':drop,'radius':a.radius,'fuel':fuel,'invariant_contexts':sum(map(len,I.values())),'individual_rows_tried':tried,'outcomes':dict(counters),'viable_branch_actions':viables,'hits':hits,'seconds':time.monotonic()-now,'scope':'All 214 remaining states as keep, both rows independently range over all write/move/remaining-target-or-halt actions. Positive paths must join before reentering the unknown opposite read branch; same-read reentry allowed; hence bounded and incomplete. Every hit checked by independent joint diagram checker.'}
(a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='viable_branch_actions'},indent=2))
