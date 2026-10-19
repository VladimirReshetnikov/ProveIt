#!/usr/bin/env python3
"""Independent pinned table inventory and finite source-graph replay.
Not a compiler/runtime or blank-halting proof.
"""
from pathlib import Path
from functools import cache
import json,hashlib
ROOT=Path(__file__).resolve().parents[1]
F=ROOT/'frontend'
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
expected='bf7f459c9489e3c4cef27044d66d30c8a3d54eaff79a38af68348d06c0bb6275'
need(sha(F/'generic.tm')==expected,'pinned TM hash')
need(sha(F/'source.json')=='df4e316d1862c2e5345104ce4fa1030948be98aaf7eb5e0908a132cdb80ff455','pinned source hash')
rows={}
for line in (F/'generic.tm').read_text().splitlines():
 if line.startswith('#') or not line.strip():continue
 q,b,w,m,t=line.split();q,b,w,t=map(int,(q,b,w,t))
 need((q,b) not in rows,'duplicate row');need(b in(0,1) and w in(0,1) and m in('L','R'),'binary row')
 rows[q,b]=w,m,t
need(set(rows)=={(q,b)for q in range(263)for b in(0,1)},'complete working-state rows')
need(all(0<=t<=263 for w,m,t in rows.values()),'bounded targets')
need((F/'generic.tm').read_text().splitlines()[0]=='#! start 0','exact initial state')

def paths_and_live(data):
 S=data['structures'];active=set();seen=set()
 @cache
 def paths(n):
  need(type(n)==int and 0<=n<len(S),'source index')
  need(n not in active,'source cycle');active.add(n);seen.add(n);x=S[n]
  need(len(x)==2,'binary source node')
  if isinstance(x[0],str):
   need((x[0]=='CH' and x[1] is None) or (x[0] in ('CI','CD','CB','CC') and type(x[1])==int and x[1]>=0),'terminal')
   result=(('',x[0],x[1]),)
  else:result=tuple((str(b)+p,o,r)for b in(0,1)for p,o,r in paths(x[b]))
  active.remove(n);return result
 pp=paths(data['root']);term={n for n in seen if isinstance(S[n][0],str)}
 return pp,seen,term

def signature(pp):
 """Ordered register instruction graph; external exits retain ancestor count."""
 intervals={};N=len(pp)
 for i,(p,o,r)in enumerate(pp):
  for k in range(len(p)+1):
   pref=p[:k]
   if pref not in intervals:intervals[pref]=[i,i+1]
   else:intervals[pref][1]=i+1
 def jump(p,k,bit):
  cuts=[i for i,b in enumerate(p)if b==bit]
  if len(cuts)<k:return ('break'if bit=='0'else'continue',k-len(cuts))
  need(k>0,'nonpositive explicit jump')
  dst=intervals[p[:cuts[-k]]][1 if bit=='0'else 0]
  return dst if dst<N else ('break',0)
 out=[]
 for i,(p,o,r)in enumerate(pp):
  nxt=i+1 if i+1<N else ('break',0)
  dst=(nxt,)if o=='CI'else(jump(p,1,'0'),nxt)if o=='CD'else(jump(p,r,'0'),)if o=='CB'else(jump(p,r,'1'),)if o=='CC'else('halt',)
  out.append((o,r,dst))
 return tuple(out)

rot=load(F/'source.json');mini=load(F/'minimal/source.json')
pp,live,term=paths_and_live(rot);pm,lm,tm=paths_and_live(mini)
need(list(map(list,pp))==load(F/'sites_logical.json'),'rotated paths exact')
need(list(map(list,pm))==load(F/'minimal/sites_logical.json'),'minimal paths exact')
need(len(live)==224 and len(live-term)==201 and len(term)==23,'rotated live inventory')
need(len(pp)==6511,'rotated instruction count')
need(signature(pp)==signature(pm),'entire ordered guarded source graph preserved')
original=load(F/'original_sites_logical.json');edit=mini['edit_path']
need(edit=='111010010011011100','pinned edit path')
need([x for x in original if not x[0].startswith(edit)]==[list(x)for x in pm if not x[0].startswith(edit)],'outside surgical edit literal paths unchanged')
E=['eq','a','b'];need(mini['old_local_formula']==['imp',E,['all','c',E]],'old helper formula')
need(mini['new_local_formula']==['imp',E,['all',E,E]],'exact new native-code helper formula')
for prefix in (F,F/'minimal'):
 cert=load(prefix/'certificate.json')
 need(sha(prefix/'source.json')==cert['source_sha256'],'receipt source hash')
 need(sha(prefix/'sites_logical.json')==cert['sites_sha256'],'receipt sites hash')
need(sha(F/'original_sites_logical.json')==mini['source_sha256'],'original source pin')
g=load(F/'generic_source.json');need(len(g['nodes'])==201,'generic-source node inventory')
# Independently reconstruct the generic graph representation from the structured tree.
S=rot['structures'];nodes={}
def emit(n):
 if str(n) in nodes:return
 es=[]
 for x in S[n]:
  if isinstance(S[x][0],str):
   op,r=S[x];es.append([op[1:],r]if op!='CH'else['H'])
  else:emit(x);es.append(['N',x])
 nodes[str(n)]=es
emit(rot['root']);need(nodes==g['nodes'] and rot['root']==g['root'],'generic source graph conversion')
report={'valid':True,'working_states':263,'rows':526,'start':0,'halt':263,'source_decision_nodes':201,'source_terminal_nodes':23,'instruction_occurrences':6511,'source_graph_reassociation_equal':True,'outside_surgical_edit_literal_paths_equal':True,'table_sha256':expected,'scope':'Finite table inventory, source conversion, and guarded graph equality. No generic compiler/runtime simulation or new blank-halting calibration.'}
print(json.dumps(report,indent=2))
