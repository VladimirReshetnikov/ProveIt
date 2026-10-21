#!/usr/bin/env python3
"""Own data-only exact source/table and rooted graph comparison."""
from pathlib import Path
import json,hashlib,collections
P=Path(__file__).resolve().parent;D=P/'extracted/K215_Composed_Selector_2026-10-20';K=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k215')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 T={}
 for line in p.read_text().splitlines():
  if not line.strip()or line.startswith('#'):continue
  q,v,w,d,z=line.split();assert d in('L','R');key=(int(q),int(v));assert key not in T;T[key]=(int(w),d,int(z))
 assert len(T)%2==0 and all((q,b)in T for q,_ in T for b in(0,1));return T
A=read(K/'k215.native.tm');B=read(D/'machine/k215.native.tm');rowsa=json.loads((K/'source/sites215.json').read_text())if(K/'source/sites215.json').exists()else json.loads((K/'sites215.json').read_text());rowsb=json.loads((D/'source/sites215.json').read_text());m={0:0,254:254};inv={0:0,254:254};todo=[0];fails=[]
for q in todo:
 for bit in(0,1):
  x,y=A[q,bit],B[m[q],bit]
  if x[:2]!=y[:2]:fails.append({'kind':'action','old':[q,bit,*x],'new':[m[q],bit,*y]});break
  u,v=x[2],y[2]
  if(u in m and m[u]!=v)or(v in inv and inv[v]!=u):fails.append({'kind':'bijection','old':[q,bit,*x],'new':[m[q],bit,*y],'mapped_target':m.get(u),'inverse_target':inv.get(v)});break
  if u not in m:m[u]=v;inv[v]=u;todo.append(u)
 if fails:break
r={'status':'DATA_COMPARISON_COMPLETE','source_literal_rows_equal':rowsa==rowsb,'source_bytes_equal':sha(D/'source/sites215.json')=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba','source_sha256':sha(D/'source/sites215.json'),'table_sha256':sha(D/'machine/k215.native.tm'),'accepted_table_sha256':sha(K/'k215.native.tm'),'states':[len(A)//2,len(B)//2],'same_native_labels':set(A)==set(B),'literal_changed_rows':[{'key':list(k),'accepted':list(A[k]),'submitted':list(B[k])}for k in sorted(set(A)&set(B))if A[k]!=B[k]],'rooted_isomorphism':not fails and len(m)==len(A)//2+1,'rooted_mapping_size':len(m),'first_failure':fails,'scope':'Own read-only exact data comparison; no supplied scripts or machine execution.'};(P/'comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
