#!/usr/bin/env python3
"""Independent checker of the mod-four source edit, affine restoration and quartic.
No producer is imported; all arithmetic is exact and assertions are avoided.
The unbounded semantic proof is in PROOF.md and is not inferred from tests.
"""
import copy,hashlib,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PINS={241:'4ac1f58659deee06fdd8d956ebc1f38f72543135759f1174b145e3d8f5b4f9fb',242:'3970268165d2dea4914550913d1e882f9c6f108008de677a919fc2a01b8740a5'}
def read(p):return json.loads(p.read_text())
def need(t,s):
 if not t:raise ValueError(s)
def decode(ts):
 p=Counter()
 for c,m in ts:
  need(type(c)is int and type(m)is list and all(type(v)is int for v in m),'integer term')
  need(m==sorted(m),'canonical monomial');p[tuple(m)]+=c
 return {m:c for m,c in p.items()if c}
def add(p,q):
 d=Counter(p);d.update(q);return {m:c for m,c in d.items()if c}
def mul(p,q):
 d=Counter()
 for m,c in p.items():
  for n,e in q.items():d[tuple(sorted(m+n))]+=c*e
 return {m:c for m,c in d.items()if c}
def subst_all(p,rest):
 d={}
 for m,c in p.items():
  r={():c}
  for j in m:r=mul(r,rest[j])
  d=add(d,r)
 return d

def check(n,linear=False,override=None):
 path=ROOT/(('linear_' if linear else 'mod4_')+'integer'+str(n));o={f:read(path/(f+'.json')) for f in ['equation','expanded_polynomial','certificate','RESTORATION','METRICS']}
 if override:o.update(override)
 eq,ep,cert,rr,met=[o[f]for f in ['equation','expanded_polynomial','certificate','RESTORATION','METRICS']]
 srcpath=ROOT/'sources'/('factorial_free'+str(n+1+int(linear))+'.json');raw=srcpath.read_bytes();src=json.loads(raw)
 need(hashlib.sha256(raw).hexdigest()==PINS[n+1+int(linear)],'pinned source')
 need(cert['source_file']==srcpath.name and cert['source_sha256']==PINS[n+1+int(linear)],'source certificate binding')
 need(eq['domain']==src['domain']=='unrestricted integers','unrestricted integer domain')
 names={v['name']:i for i,v in enumerate(src['variables'])};q=names['pow2.output'];z=names['radix.odd_square_root_half']
 f=names['crt.growth_majorant_F'];rad=names['mul.1']
 need(cert['linear_radius']==linear and cert['majorant_coordinate']==f and cert['radius_coordinate']==rad,'linear radius metadata')
 need(decode(src['residuals'][0]['terms'])=={(f,f):-1,(rad,):1},'old literal square radius')
 if linear:need(cert['radius_edit']=={'row':0,'old':src['residuals'][0],'new':{'label':'radius.linear_majorant','terms':[[-1,[f]],[1,[rad]]]}},'new literal linear radius')
 ix=[i for i,r in enumerate(src['residuals'])if r['label']=='radix.odd_square'];need(len(ix)==1,'single source row');i=ix[0]
 oldguard={():-2,(q,):1,(z,):-4,(z,z):-4}
 need(decode(src['residuals'][i]['terms'])==oldguard,'old literal square guard')
 need(cert['actual_radix']==[[1,[q]],[-1,[]]],'actual radix translation')
 need(cert['source_guard_row']==i and cert['old_guard']==src['residuals'][i],'changed row exactness')
 edit=decode(cert['edited_guard']['terms']);need(edit=={():-2,(q,):1,(z,):-4},'new literal mod-four guard')
 keep=[v for v in range(len(src['variables']))if v not in ({q,rad}if linear else {q})];ren={v:j for j,v in enumerate(keep)}
 need(cert['retained_source_coordinates']==keep,'retained list');need(cert['deleted_coordinate']==q and cert['retained_parameter']==z,'deleted coordinate')
 need(decode(cert['stored_q_replacement'])=={():2,(z,):4},'monic replacement')
 # The explicit old-to-edited witness map changes only the private root.
 older=[{(j,):1}for j in range(len(src['variables']))];older[z]={(z,):1,(z,z):1}
 need(decode(cert['old_to_edited_parameter'])==older[z],'forward semantic witness map')
 need(subst_all(edit,older)==oldguard,'old zeros map into edited guard')
 need(all(not any(z in m for _,m in row['terms'])for j,row in enumerate(src['residuals'])if j!=i),'old radix-root privacy')
 # These restoration identities are only for the edited source.
 rest=[decode(t)for t in rr['coordinates']]
 need(len(rest)==len(src['variables']) and rr['dropped_residual']==i and rr['radius_dropped_residual']==(0 if linear else None),'restoration completeness')
 for j,r in enumerate(rest):need(r==({():2,(ren[z],):4}if j==q else {(ren[f],):1} if linear and j==rad else {(ren[j],):1}),'individual restoration')
 variables=[copy.deepcopy(src['variables'][j])for j in keep];variables[ren[z]]={'name':'radix.mod_four_parameter','kind':'unrestricted_integer'}
 need(eq['variables']==variables,'coordinate metadata')
 need(subst_all(edit,rest)=={},'removed row vanishes identically')
 if linear:need(subst_all({(rad,):1,(f,):-1},rest)=={},'linear radius restoration')
 expected=[(row['label'],subst_all(decode(row['terms']),rest))for j,row in enumerate(src['residuals'])if j!=i and not(linear and j==0)]
 need(len(expected)==len(eq['residuals']),'complete residual list')
 total={};rowh=0
 for (lab,p),row in zip(expected,eq['residuals']):
  need(lab==row['label'] and decode(row['terms'])==p,'pulled-back residual equality')
  need(max(map(len,p),default=0)<=2,'quadratic residual degree')
  rowh=max(rowh,*map(abs,p.values()));total=add(total,mul(p,p))
 need(decode(ep['terms'])==total,'fully collected quartic')
 need(ep['variables']==n and ep['domain']=='unrestricted integers','expanded domain and count')
 need({v for m in total for v in m}==set(range(n)),'coordinate liveness')
 computed={'variables':n,'rows':len(expected),'degree':max(map(len,total)),'monomials':len(total),'height':max(map(abs,total.values())),'row_height':rowh}
 need(computed==met,'every measured metric')
 return computed

def mutations(n,linear):
 path=ROOT/(('linear_'if linear else'mod4_')+'integer'+str(n));cases=[]
 c=read(path/'certificate.json');c['edited_guard']['terms'][-1][0]=-2;cases.append({'certificate':c})
 c=read(path/'certificate.json');c['actual_radix'][-1][0]=1;cases.append({'certificate':c})
 r=read(path/'RESTORATION.json');r['coordinates'][0][0][0]+=1;cases.append({'RESTORATION':r})
 e=read(path/'expanded_polynomial.json');e['terms'][0][0]+=1;cases.append({'expanded_polynomial':e})
 e=read(path/'equation.json');e['residuals'].pop();cases.append({'equation':e})
 m=read(path/'METRICS.json');m['height']+=1;cases.append({'METRICS':m})
 if linear:
  c=read(path/'certificate.json');c['radius_edit']['new']['terms'][0][0]=-2;cases.append({'certificate':c})
 for j,c in enumerate(cases):
  try:check(n,linear,c)
  except (ValueError,IndexError,KeyError):pass
  else:raise ValueError('corruption accepted '+str(j))
 return len(cases)
if __name__=='__main__':
 result={'status':'pass','scope':'Finite source edit, one-way semantic witness map, complete affine restoration, complete quartic collection, liveness, metrics and corruption controls. Unbounded arithmetic proof separate.','endpoints':{}}
 for n,linear in [(239,True),(240,True),(240,False),(241,False)]:result['endpoints'][('linear_'if linear else'mod4_')+str(n)]={'metrics':check(n,linear),'rejected_corruptions':mutations(n,linear)}
 print(json.dumps(result,indent=2,sort_keys=True))
