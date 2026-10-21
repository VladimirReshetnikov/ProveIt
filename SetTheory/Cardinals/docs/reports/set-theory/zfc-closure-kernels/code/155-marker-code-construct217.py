#!/usr/bin/env python3
"""Reconstruct K217 from the exact dominated-rho8 K218 source/table.

Python 3.10+, standard library only; no search or external package is used.
Tree syntax/closure conventions follow ProveIt's attributed source utilities.
Runtime and the inherited logical calibration remain separate proof obligations.
"""
from pathlib import Path
from functools import lru_cache
import argparse,hashlib,json
BASE_TM='9c8505bf3731212192b83ee61dbc569085b4675ae9e0539843ae57d43ad9e886'
BASE_SRC='264fba90229974a53c2c5c943cf5fe8924327b6bbc31bd47e64d7f5c670b7495'
FINAL_TM='c902a3c5e81176230a2213d631e2e691573c167fb03e9bdb09ef5c88154f3099'
FINAL_SRC='9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655'
FINAL_DENSE='a2b8bc2d4822962ad32819fe475a7d62b0d483bc4f41977bff292742f70b3e8c'
PREFOLD='34617022def75d88a4f357589d7a48f468d17b58c910947ed0738aa3c6a5760a'
PREFIX='11101001001110010'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def compact(x):return(json.dumps(x,separators=(',',':'))+'\n').encode('ascii')
def leaf(t):return isinstance(t[0],str)
def parse(rows):
 dd={p:(op,arg)for p,op,arg in rows}
 need(len(dd)==len(rows),'duplicate source address')
 def go(p=''):
  if p in dd:return dd[p]
  need(len(p)<100,'missing/full-tree source node')
  return go(p+'0'),go(p+'1')
 t=go();need(sites(t)==rows,'source order/full-tree mismatch');return t
def sites(t,p=''):
 return [[p,*t]]if leaf(t)else sites(t[0],p+'0')+sites(t[1],p+'1')
@lru_cache(None)
def size(t):return 1 if leaf(t)else size(t[0])+size(t[1])
@lru_cache(None)
def boundary(t):
 if leaf(t):
  op,n=t
  if op=='CD':return 1,0,False
  if op=='CB':return n,0,False
  if op=='CC':return 0,n,False
  return 0,0,op=='CH'
 a,b=map(boundary,t)
 return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2]or b[2]
def replace(t,p,n):
 if not p:return n
 b=int(p[0]);cc=list(t);cc[b]=replace(cc[b],p[1:],n);return tuple(cc)
def subtree(t,p):
 for b in p:t=t[int(b)]
 return t
def metrics(t):
 seen=set()
 def go(n):
  if n in seen:return
  seen.add(n)
  if not leaf(n):go(n[0]);go(n[1])
 go(t);rows=sites(t)
 return dict(dag_nodes=len(seen),leaf_occurrences=len(rows),maximum_depth=max(len(p)for p,_,_ in rows),maximum_zero_run=max(len(z)for p,_,_ in rows for z in p.split('1')))
def cfg_intervals(rows):
 spans={}
 for i,(p,op,n)in enumerate(rows):
  for k in range(len(p)+1):
   q=p[:k]
   if q not in spans:spans[q]=[i,i+1]
   else:spans[q][1]=i+1
 def cut(p,bit,n):
  for j in range(len(p)-1,-1,-1):
   if p[j]==bit:
    n-=1
    if n==0:return spans[p[:j]][int(bit=='0')]%len(rows)
  return 0
 ans=[]
 for i,(p,op,n)in enumerate(rows):
  if op=='CI':targets=[(i+1)%len(rows)]
  elif op=='CD':targets=[cut(p,'0',1),(i+1)%len(rows)]
  elif op=='CB':targets=[cut(p,'0',n)]
  elif op=='CC':targets=[cut(p,'1',n)]
  else:need(op=='CH','unknown opcode');targets=[]
  ans.append([op,n,targets])
 return ans
def cfg_arithmetic(rows):
 dd={p:i for i,(p,op,n)in enumerate(rows)};depth=max(map(len,dd))
 def locate(p):
  padded=p+'0'*(depth+1)
  for k in range(1,len(padded)+1):
   if padded[:k]in dd:
    need('1'not in p[k:],'stray successor one');return dd[padded[:k]]
  raise ValueError('unresolved successor')
 def inc(p):return format((int(p,2)+1)%2**len(p),f'0{len(p)}b')if p else''
 def cut(p,b,n):
  js=[i for i,x in enumerate(p)if x==b]
  return p[:js[-n]]if len(js)>=n else''
 ans=[]
 for p,op,n in rows:
  if op=='CI':targets=[locate(inc(p))]
  elif op=='CD':targets=[locate(inc(cut(p,'0',1))),locate(inc(p))]
  elif op=='CB':targets=[locate(inc(cut(p,'0',n)))]
  elif op=='CC':targets=[locate(cut(p,'1',n))]
  else:targets=[]
  ans.append([op,n,targets])
 return ans
def read_table(raw):
 T={};start=[]
 for line in raw.decode('ascii').splitlines():
  if line.startswith('#! start '):start.append(int(line[9:]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in T,'duplicate row')
  need(b in(0,1)and w in(0,1)and d in('L','R'),'invalid transition');T[q,b]=w,1 if d=='R'else-1,z
 Q={q for q,b in T};need(start==[0],'initial label');need(set(T)=={(q,b)for q in Q for b in(0,1)},'partial table')
 need({z for w,d,z in T.values()}-Q=={254},'halt/target census');return T
def table_bytes(T):return('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode('ascii')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline-table',type=Path,required=True);ap.add_argument('--baseline-source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 raw=a.baseline_table.read_bytes();src=a.baseline_source.read_bytes();need(sha(raw)==BASE_TM and sha(src)==BASE_SRC,'incorrect pinned baseline')
 T=read_table(raw);rows=json.loads(src);old=parse(rows)
 A,z=subtree(old,PREFIX);z,E=z;z,D=z;B,C=z
 factors=[A,B,C,D,E];need([size(x)for x in factors]==[14,27,53,374,3682],'factor lengths')
 need(all(boundary(x)==(0,0,False)for x in factors),'open rotation factor')
 new=replace(old,PREFIX,((A,B),((C,D),E)));newrows=sites(new)
 need([r[1:]for r in rows]==[r[1:]for r in newrows],'primitive word changed')
 G=cfg_intervals(rows);need(G==cfg_arithmetic(rows)==cfg_intervals(newrows)==cfg_arithmetic(newrows),'control graph changed')
 need(sum(x[0]!=y[0]for x,y in zip(rows,newrows))==94,'address-change census')
 U=T.copy();patch={(201,0):((0,1,92),(0,1,188)),(188,0):((0,1,90),(0,1,92)),(188,1):((1,1,146),(1,1,90)),(210,0):((0,1,188),(0,1,146))}
 for key,(before,after)in patch.items():need(T[key]==before,'spine row precondition');U[key]=after
 need(sha(table_bytes(U))==PREFOLD,'prefold bytes')
 incoming=lambda q:sorted((k,v)for k,v in U.items()if v[2]==q)
 need(incoming(69)==[((53,1),(1,1,69))],'keeper marker entry')
 need(incoming(400)==[((224,0),(0,1,400))],'deleted marker entry')
 need(U[69,1]==U[400,1]==(1,1,31),'shared branch')
 need(U[69,0]==(0,1,105)and U[400,0]==(0,1,104),'distinct branch')
 M={(q,b):(w,d,69 if z==400 else z)for(q,b),(w,d,z)in U.items()if q!=400};M[69,0]=0,-1,188
 for marker,goal in((0,104),(1,105)):
  cells={-1:marker,0:0};q,h=69,0
  for _ in range(3):
   need(h in cells,'marker block reads exterior');w,d,q=M[q,cells[h]];cells[h]=w;h+=d
  need((q,h)==(goal,1)and cells=={-1:marker,0:0},'marker block mismatch')
 need(len(M)==434,'state-count mismatch')
 order=[0];mp={0:0}
 for q in order:
  for b in(0,1):
   z=M[q,b][2]
   if z!=254 and z not in mp:mp[z]=len(order);order.append(z)
 need(len(order)==217,'graph-reachability census');mp[254]=217
 dense={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in M.items()}
 final=table_bytes(M);source=compact(newrows);canonical=table_bytes(dense)
 need((sha(final),sha(source),sha(canonical))==(FINAL_TM,FINAL_SRC,FINAL_DENSE),'final bytes differ')
 a.output.mkdir(parents=True,exist_ok=True)
 for name,data in [('prefold218.native.tm',table_bytes(U)),('k217.native.tm',final),('k217.tm',canonical),('sites217.json',source)]: (a.output/name).write_bytes(data)
 rec=dict(status='EXACT_K217_CONSTRUCTION_PASS',working_states=217,transition_rows=434,changed_source_addresses=94,source_metrics=metrics(new),source_cfg_sha256=sha(compact(G)),native_sha256=sha(final),canonical_sha256=sha(canonical),source_sha256=sha(source),prefold_sha256=PREFOLD,scope='Deterministic source/table reconstruction, two exact CFG checks, closure and marker-block premises; full primitive runtime and startup are separate checks.')
 (a.output/'reconstruction.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
if __name__=='__main__':main()
