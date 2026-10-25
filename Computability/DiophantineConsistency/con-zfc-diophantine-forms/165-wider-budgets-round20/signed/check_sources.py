#!/usr/bin/env python3
"""Independent source bindings, exact raw mutations, and monic restorations.
Imports independently authored checkers only, never a producing module.
"""
from pathlib import Path
import copy,json,importlib.util,subprocess,sys
R=Path(__file__).resolve().parent

def need(ok,message):
 if not ok:raise ValueError(message)
def read(p):return json.loads(p.read_text())
def checker():
 p=R/'inherited_free/check_factorial_free.py';s=importlib.util.spec_from_file_location('retained_free_checker',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def expected_shared(A):
 parent=read(R/'parent252/data/factored_source.json');md=read(R/'parent252/upstream/parent/transform_certificate.json')
 n={v['name']:i for i,v in enumerate(parent['variables'])};a,H,f,r,h=[n[k] for k in ['shared.A','cap.H','cap.f','cap.R','cap.h']]
 C=md['cap_variables']['Y'];F=n['fact0.output'];B=n['choose0.output'];V=n['pow0.output'];M=n['pow14.output'];q=n['pow2.output'];fb=n['mul.5'];z=len(parent['variables']);v=z+1;S=z+2
 changes={'cap.comparison_constructor':dict(label='cap.deterministic_factor',terms=A.terms({(f,):1,(H,):-1,tuple(sorted((a,H))):1})), 'cap.index_residue':dict(label='cap.index_residue',terms=A.terms(A.plus({(r,):1,tuple(sorted((C,h))):-1},A.scale(A.poly(md['anchor_index']),-1))))}
 drop={'choose0.digit_bound','domain_guard.2','fact0.ceiling','fact0.remainder_bound','domain_guard.0','domain_guard.1'};rows=[];removed=0
 for row in parent['residuals']:
  p=A.poly(row['terms'])
  if row['label']in drop or p=={tuple(sorted((F,B))):-1,(fb,):1}:removed+=1;continue
  if row['label']=='domain_guard.4':row=dict(row,terms=A.terms(A.plus(p,{(S,S):-4})))
  elif row['label']in changes:row=changes[row['label']]
  rows.append(row)
 need(removed==7,'shared parent deletion census')
 rows += [{'label':'radix.odd_affine','terms':A.terms({(q,):1,(z,):-2,():-1})},{'label':'bootstrap.normalization_ratio','terms':A.terms({(M,):1,tuple(sorted((B,v))):-1})},{'label':'bootstrap.normalized_ceiling','terms':A.terms({tuple(sorted((M,F))):1,tuple(sorted((v,V))):-1,(S,):-1})}]
 names=parent['variables']+[{'name':'radix.odd_square_root_half','kind':'signed_witness'},{'name':'bootstrap.normalizing_ratio','kind':'signed_witness'},{'name':'bootstrap.normalized_ceiling_error','kind':'signed_witness'}]
 need(all(not ({n['fact0.remainder'],n['fact0.slack'],fb}&set(m))for row in rows for c,m in row['terms']),'private removed coordinates')
 need(next(r for r in rows if r['label']=='cap.pooled_index_residue')==next(r for r in parent['residuals']if r['label']=='cap.pooled_index_residue'),'full orientation preserved')
 return names,rows

def project(A,source,folder):
 pc=read(folder/'projection_certificate.json');rows={i:A.poly(r['terms'])for i,r in enumerate(source['residuals'])};deleted=set()
 for st in pc['steps']:
  i,v=st['row_id'],st['variable'];f=A.poly(st['restoration']);need(i in rows and v not in deleted,'monic target');need(all(v not in m for m in f),'acyclic restoration');need(A.degree(f)<=2,'restoration degree')
  rel=A.plus(A.var(v),A.scale(f,-1));need(rows[i]in[rel,A.scale(rel,-1)],'unit restoration identity')
  if A.degree(f)==2:need(all(v not in m or len(m)==1 for j,p in rows.items()if j!=i for m in p),'quadratic linear-only occurrence')
  del rows[i];rows={j:A.subst(p,v,f)for j,p in rows.items()};rows={j:p for j,p in rows.items()if p};need(all(A.degree(p)<=2 for p in rows.values()),'projection degree');deleted.add(v)
 keep=sorted({v for p in rows.values()for m in p for v in m});need(pc['retained_original_variables']==keep and pc['retained_original_rows']==sorted(rows),'live maps');need(pc['unconstrained_removed']==sorted(set(range(len(source['variables'])))-set(keep)-deleted),'unused census')
 names=[source['variables'][v]for v in keep];ren={v:i for i,v in enumerate(keep)};rs=[{tuple(ren[v]for v in m):c for m,c in rows[i].items()}for i in sorted(rows)];p=read(folder/'projected.json');need(p['variables']==names and [A.poly(r['terms'])for r in p['residuals']]==rs,'projected literal data')
 tr=read(folder/'translation_certificate.json');need(tr['convention']=='old=new+shift','translation convention')
 for v,d in tr['shifts']:rs=[A.subst(row,v,A.plus(A.var(v),A.const(d)))for row in rs]
 eq=read(folder/'equation.json');need(eq['variables']==names and [A.poly(r['terms'])for r in eq['residuals']]==rs,'translated literal data')
 return {'unit_restorations':len(deleted),'unused':len(pc['unconstrained_removed']),'variables':len(names),'rows':len(rs)}

def audit_sources():
 A=checker();folder=R/'inherited_shared/candidate244';source=read(folder/'source.json');names,rows=expected_shared(A);need(source['variables']==names and source['residuals']==rows,'shared exact raw-source mutation');shared=project(A,source,folder)
 raw=A.source_check(R/'inherited_free/factorial_free_affine');new=copy.deepcopy(raw);count=0;ns={v['name']:i for i,v in enumerate(raw['variables'])};t=ns['t0'];d=ns['growth.power_base']
 for r in new['residuals']:
  if r['label']=='cofinal.horizon':
   p=A.poly(r['terms']);negative=[m for m,c in p.items()if c==-1];need(len(p)==2 and p.get((t,))==1 and len(negative)==1 and len(negative[0])==2 and negative[0][0]==negative[0][1],'old square horizon');p[negative[0]]=-2;r['terms']=A.terms(p);count+=1
  if r['label']=='growth.base_definition':
   need(A.poly(r['terms'])=={():-34,(t,):-2,(d,):1},'old affine power base');r['terms']=A.terms({():-16,(t,):-1,(d,):1});count+=1
 need(count==2 and new==read(R/'power_majorant245/raw_source.json'),'exact t^t/even-horizon delta')
 power=A.projection_check(R/'power_majorant245',new)
 # Recheck strict linear-occurrence rule separately, not only degree after substitution.
 project(A,read(R/'power_majorant245/factored_source.json'),R/'power_majorant245')
 # Complete inherited finite chain; optimized mode is propagated explicitly.
 p=subprocess.run([sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(R/'parent252/code/verify.py')],capture_output=True,text=True)
 need(p.returncode==0,'common parent verifier: '+p.stderr)
 return {'shared':shared,'power':power,'parent252':'PASS','scope':'Exact retained arithmetic source, raw deltas, Horn identities, monic inverses and translations; unbounded semantics in proofs.'}
if __name__=='__main__':print(json.dumps(audit_sources(),indent=2))
