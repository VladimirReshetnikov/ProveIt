#!/usr/bin/env python3
"""Emit only a new ordinary nine-positive research circuit, preserving all parents."""
import json,hashlib
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]
ROOT=RESEARCH.parents[1]
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
for profile in ['boundary_simple','compact_simple']:
 path=ROOT/'Computability/DiophantineConsistency/candidates/position-zero-norm-sharing'/f'{profile}.json'
 parent=json.loads(path.read_text()); old=parent['nodes']; nodes=[]; remap={}
 def app(n):
  i=len(nodes);nodes.append(n);return i
 def clone(i):
  if i in remap:return remap[i]
  n=dict(old[i])
  if n['kind'] in ('add','sub','mul'):
   n['left']=clone(n['left']);n['right']=clone(n['right'])
  remap[i]=app(n);return remap[i]
 def lit(v):return clone(next(i for i,n in enumerate(old) if n['kind']=='literal' and n['value']==v))
 def op(k,a,b):return app({'kind':k,'left':a,'right':b})
 def mul(a,b):return op('mul',a,b)
 def add(a,b):return op('add',a,b)
 def sub(a,b):return op('sub',a,b)
 def cut(k):return clone(parent['named_nodes'][k])
 one,four=lit(1),lit(4)
 A,C,J=map(cut,['A','C','J'])
 delta=cut('Am1');C2=mul(C,C)
 ivar=clone(next(i for i,n in enumerate(old) if n['kind']=='variable' and n['name']=='i'))
 efull=mul(mul(J,ivar),C2)
 first=cut('a0'); de=mul(first,efull)
 F=add(one,mul(de,mul(delta,efull)))
 Lambda=add(one,mul(A,sub(C,one)))
 G=add(A,mul(F,Lambda))
 Z=cut('Z');H=add(C,mul(F,Z));GH=mul(G,H)
 I=add(one,sub(mul(GH,GH),mul(H,H)))
 Ac=mul(first,F);Vc=mul(A,de)
 Omega=cut('Omega');E=cut('E0')
 Theta=sub(E,mul(Omega,add(Vc,GH)))
 theta2=mul(Theta,Theta);omega2=mul(Omega,Omega)
 inner=add(theta2,mul(omega2,sub(Ac,I)))
 output=sub(mul(inner,inner),mul(mul(mul(four,omega2),Ac),theta2))
 seen=set()
 def visit(i):
  if i in seen:return
  seen.add(i)
  if nodes[i]['kind'] in ('add','sub','mul'):
   visit(nodes[i]['left']);visit(nodes[i]['right'])
 visit(output)
 counts=Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul'))
 deg=[]
 for n in nodes:
  if n['kind']=='variable':d=1
  elif n['kind'] in ('literal','fixed'):d=0
  elif n['kind']=='mul':d=deg[n['left']]+deg[n['right']]
  else:d=max(deg[n['left']],deg[n['right']])
  deg.append(d)
 labels={'A':A,'C':C,'J':J,'Delta':delta,'eFull':efull,'first':first,'de':de,'F':F,'Lambda':Lambda,'G':G,'Z':Z,'H':H,'GH':GH,'I':I,'Ac':Ac,'Vc':Vc,'Omega':Omega,'E0':E,'Theta':Theta,'B1':cut('B1'),'eFullSquared':None}
 labels.pop('eFullSquared')
 a,r,W=parent['A_degree'],parent['source_degree'],parent['W']
 data=dict(parent)
 for key in ['majorant_order','power_plan','named_degree_bounds','algebraic_rewrite','raw_degree_bound']:
  data.pop(key,None)
 data.update({'schema':'nine-folded-saturation-research-v1','parent':str(path.relative_to(ROOT)),'parent_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'nodes':nodes,'output':output,'core_clone_map':{str(k):v for k,v in remap.items()},'named_nodes':labels,'operation_counts':dict(counts),'total_operations':sum(counts.values()),'variables':parent['variables'],'fixed_binding':parent['fixed_binding'],'coherent_tuple':parent['coherent_tuple'],'source_degree':r,'A_degree':a,'W':W,'expected_exact_degree':76*a+14*r+8*W+56,'degree_upper_bound':deg[output],'syntactic_degree':deg[output],'parent_research_relative':str(path.relative_to(RESEARCH)),'named_degrees':{k:deg[v] for k,v in labels.items()},'domain':'strictly positive integers','exact_degree':76*a+14*r+8*W+56,'majorant':'Vc=A*a0*eFull and Vi=G*H','algebraic_rewrite':'new existential folding certificate, not pointwise parent identity'})
 out=HERE/f'{profile}.json';raw=json.dumps(data,indent=2,sort_keys=True)+'\n'
 if args.check:
  if out.read_text()!=raw:raise ValueError('deterministic graph mismatch '+profile)
 else:out.write_text(raw)
 print(profile,'count',sum(counts.values()),counts,'nodes',len(nodes),'unused',len(nodes)-len(seen),'rawdegree',deg[output],'expectedexact',data['expected_exact_degree']); print(data['named_degrees'])
