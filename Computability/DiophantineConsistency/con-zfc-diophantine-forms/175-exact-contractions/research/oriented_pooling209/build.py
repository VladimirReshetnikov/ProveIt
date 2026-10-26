#!/usr/bin/env python3
"""Literal signed-base reciprocal compiler, ordinary integer polynomials only.

The two-pool oriented-weight direction was suggested in the parent report.
The five-block bootstrap and emitted specialization are proved in PROOF.md.
No third-party dependencies. A factored polynomial is an exact finite
definition; no exponential, quotient, or other non-polynomial gate occurs.
"""
from pathlib import Path
from collections import defaultdict
import copy, hashlib, json

ROOT=Path(__file__).resolve().parent
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(x):return hashlib.sha256(canonical(x)).hexdigest()
def poly(ts):return {tuple(m):c for c,m in ts}
def serial(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(p,q,a=1):
 r=p.copy()
 for m,c in q.items():
  z=r.get(m,0)+a*c
  if z:r[m]=z
  else:r.pop(m,None)
 return r
def scale(p,a):return {m:a*c for m,c in p.items() if a*c}
def mul(p,q):
 r=defaultdict(int)
 for m,c in p.items():
  for n,d in q.items():r[tuple(sorted(m+n))]+=c*d
 return {m:c for m,c in r.items() if c}
def coefficient(p,v):
 r={}
 for m,c in p.items():
  if m.count(v)>1:raise ValueError('nonlinear private coordinate')
  if v in m:
   n=list(m);n.remove(v);r[tuple(n)]=c
 return r
def without(p,vs):return {m:c for m,c in p.items() if not set(m)&vs}

def build(parent,operations):
 n=len(parent['variables']);names=[v['name'] for v in parent['variables']]
 rows=[poly(r['terms']) for r in parent['residuals']]
 labels=[r['label'] for r in parent['residuals']]
 one={():1}
 def V(name):return {(names.index(name),):1}
 A=add(V('shared.A'),one)
 groups=[];removed_vars=set();removed_rows=set()
 single=[('initial_growth','mul.1',1,'pow0.output',0,'index0.X_minus_AY','index0.Y','mul.460',0),
         ('initial_B','choose0.output',0,'pow1.output',0,'index12.X_minus_AY','index12.Y','mul.645',1),
         ('initial_BH','self_radix.BH',0,'pow2.output',-1,'index12.X_minus_AY','index12.Y','mul.645',1)]
 for j,(name,base,bo,out,mo,delta,Y,Z,zo) in enumerate(single):
  b=add(V(base),scale(one,bo));m=add(V(out),scale(one,mo));y=V(Y);d=V(delta);z=add(V(Z),scale(one,zo));x=add(d,z)
  t=add(add(scale(mul(A,b),2),mul(b,b),-1),one,-1)
  h=mul(y,add(m,x,-1));s=add(mul(add(m,d,-1),add(m,d,-1)),mul(y,y),-1)
  e=add(s,scale(mul(b,h),2),-1)
  tv=names.index(f'base{j}.T');qv=names.index(f'pow{j}.quotient')
  qrows=[k for k,r in enumerate(rows) if any(qv in mon for mon in r)]
  trows=[k for k,r in enumerate(rows) if any(tv in mon for mon in r)]
  if len(qrows)!=1 or len(trows)!=2:raise ValueError('singleton privacy')
  qr=qrows[0];tr=next(k for k in trows if k!=qr)
  a=rows[tr].get((tv,))
  if a not in (-1,1) or rows[tr]!=scale(add({(tv,):1},t,-1),a):raise ValueError('modulus row')
  delta_poly=add(add(m,d,-1),mul(b,y),-1)
  if rows[qr]!=add(delta_poly,mul({(tv,):1},{(qv,):1})):raise ValueError('power congruence row')
  aygate=add(z,mul(A,y),-1)
  if aygate not in rows:raise ValueError('missing AY gate')
  if add(add(e,mul(t,mul(y,y)),-1),mul(delta_poly,delta_poly),-1)!=scale(mul(mul(b,y),aygate),2):raise ValueError('squared-error identity')
  groups.append({'name':name,'base':serial(b),'E':serial(e),'T':serial(t),'H':serial(h),'S':serial(s),'delta':serial(delta_poly),'Y':serial(y),'AY_gate_row':rows.index(aygate),'private_variables':[tv,qv],'private_rows':[tr,qr],'request_count':1})
  removed_vars|={tv,qv};removed_rows|={tr,qr}
 for name,count in [('radix',3),('radix_plus_one',11)]:
  k=names.index(name+'.K');l=names.index(name+'.L');ia=labels.index(name+'.bilinear_aggregate');ib=labels.index(name+'.pooled_norm');ar,br=rows[ia],rows[ib]
  b=scale(coefficient(br,k),-1);a=coefficient(ar,l);ar0=without(ar,{k,l});br0=without(br,{k,l})
  if ar!=add(add({(k,):1},mul(a,{(l,):1})),ar0) or br!=add(add(br0,mul(b,{(k,):1}),-1),{(l,):1}):raise ValueError('pool structure')
  if add(b,a,-1)!=scale(A,2):raise ValueError('different anchor')
  e=add(br0,mul(b,ar0));t=add(one,mul(b,a));t=scale(t,-1)
  groups.append({'name':name,'base':serial(b),'E':serial(e),'T':serial(t),'H_twice_negated':serial(ar0),'S':serial(br0),'private_variables':[k,l],'private_rows':[ia,ib],'request_count':count})
  removed_vars|={k,l};removed_rows|={ia,ib}
 if len(removed_vars)!=10 or len(removed_rows)!=10:raise ValueError('wrong deletion count')
 for i,r in enumerate(rows):
  if i not in removed_rows and any(set(mon)&removed_vars for mon in r):raise ValueError('nonprivate coordinate')
 # Keep a validated subsequence of integer row additions. By avoiding both
 # sources and targets in the ten deleted rows, privacy remains literal.
 kept=[]
 for i,j,k in operations['operations']:
  if i in removed_rows or j in removed_rows:continue
  rows[i]=add(rows[i],rows[j],k);kept.append([i,j,k])
 retained=[i for i in range(n) if i not in removed_vars];rename={v:i for i,v in enumerate(retained)}
 def remap(p):return {tuple(rename[v] for v in mon):c for mon,c in p.items()}
 ng=[]
 for g in groups:
  ng.append({k:(serial(remap(poly(v))) if k in ['base','E','T'] else v) for k,v in g.items() if k in ['name','request_count','base','E','T']})
 out={'schema':'conzfc-signed-five-base-reciprocal-v1','domain':'unrestricted integers','polynomial':'sum(residual^2) + reciprocal_residual^2','variables':[copy.deepcopy(parent['variables'][i]) for i in retained]+[{'name':'signed_reciprocal.z','kind':'witness'}],
      'residuals':[{'label':parent['residuals'][i]['label'],'terms':serial(remap(r))} for i,r in enumerate(rows) if i not in removed_rows],
      'reciprocal':{'groups':ng,'z_coordinate':len(retained),'definition':'sum_j(base_j * E_j * product_{l!=j} T_l) - z * product_l T_l'}}
 certificate={'schema':'signed-five-base-compiler-v1','source_sha256':digest(parent),'basis_operation_source_sha256':digest(operations),'groups_original_indices':groups,'removed_variables':sorted(removed_vars),'removed_rows':sorted(removed_rows),'retained_old_indices':retained,'retained_integer_row_operations':kept,'output_sha256':digest(out)}
 return out,certificate

def eval_sparse(terms,values):
 result=0
 for c,m in terms:
  for i in m:c*=values[i]
  result+=c
 return result
def evaluate(equation,values):
 if len(values)!=len(equation['variables']) or any(type(v)is not int for v in values):raise ValueError('integer tuple of declared length required')
 p=sum(eval_sparse(r['terms'],values)**2 for r in equation['residuals']);gg=equation['reciprocal']['groups'];ts=[eval_sparse(g['T'],values) for g in gg];r=0
 for j,g in enumerate(gg):
  w=eval_sparse(g['base'],values)*eval_sparse(g['E'],values)
  for k,t in enumerate(ts):
   if k!=j:w*=t
  r+=w
 z=values[equation['reciprocal']['z_coordinate']]
 for t in ts:z*=t
 return p+(r-z)**2

def main():
 source=json.loads((ROOT/'source/affine218.json').read_text());ops=json.loads((ROOT/'source/basis_operations.json').read_text());out,cert=build(source,ops)
 for name,value in [('equation.json',out),('certificate.json',cert)]: (ROOT/name).write_bytes(canonical(value))
 # The factorized degree upper bound is 24. A t*ones substitution has a
 # nonzero degree-24 coefficient iff the degree-12 homogeneous residual is nonzero.
 leads=[]
 for g in out['reciprocal']['groups']:
  b=sum(c for c,m in g['base'] if len(m)==1);e=sum(c for c,m in g['E'] if len(m)==3);t=sum(c for c,m in g['T'] if len(m)==2);leads.append((b,e,t))
 lead=0
 for j,(b,e,t) in enumerate(leads):
  x=b*e
  for k,(_,_,t2) in enumerate(leads):
   if k!=j:x*=t2
  lead+=x
 if not lead:raise ValueError('degree witness vanished')
 metrics={'variables':len(out['variables']),'ordinary_residuals':len(out['residuals']),'total_residuals':len(out['residuals'])+1,'exact_degree':24,'reciprocal_residual_degree':12,'degree_witness':'all coordinates equal t','coefficient_t24':lead*lead,'reciprocal_coefficient_t12':lead,'expanded_support':'not computed','expanded_coefficient_height':'not computed','fixed_integer_coefficients':True}
 (ROOT/'metrics.json').write_bytes(canonical(metrics));print(json.dumps(metrics))
if __name__=='__main__':main()
