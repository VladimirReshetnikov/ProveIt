#!/usr/bin/env python3
"""Independent exact verifier: sparse exponent maps, no builder imports."""
from pathlib import Path
from collections import defaultdict
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent

def read(p):return json.loads(p.read_text())
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def atom(i):return {((i,1),):1}
def load(ts):
 result={}
 for c,mon in ts:
  need(type(c)is int and c!=0,'zero or noninteger coefficient');need(mon==sorted(mon),'unsorted monomial')
  counts={}
  for i in mon:need(type(i)is int and i>=0,'variable index');counts[i]=counts.get(i,0)+1
  key=tuple(sorted(counts.items()));need(key not in result,'duplicate monomial');result[key]=c
 return result
def plus(*polys):
 out=defaultdict(int)
 for p in polys:
  for k,c in p.items():out[k]+=c
 return {k:c for k,c in out.items() if c}
def times(p,q):
 out=defaultdict(int)
 for a,c in p.items():
  for b,d in q.items():
   x=dict(a)
   for i,k in b:x[i]=x.get(i,0)+k
   out[tuple(sorted(x.items()))]+=c*d
 return {k:c for k,c in out.items() if c}
def coeff(c,p):return {k:c*x for k,x in p.items() if c*x}
def replace(p,mapping):
 result={}
 for mon,c in p.items():
  term={():c}
  for i,power in mon:
   for _ in range(power):term=times(term,mapping.get(i,atom(i)))
  result=plus(result,term)
 return result
def degree(p):return max(sum(k for i,k in m) for m in p)
def expand(rows):
 out=defaultdict(int)
 for p in rows:
  terms=list(p.items())
  for j,(a,c) in enumerate(terms):
   for k in range(j,len(terms)):
    b,d=terms[k];x=dict(a)
    for i,power in b:x[i]=x.get(i,0)+power
    out[tuple(sorted(x.items()))]+=(1 if j==k else 2)*c*d
 return {m:c for m,c in out.items() if c}
def metrics(e):
 rows=[load(r['terms']) for r in e['residuals']];ex=expand(rows)
 n=len(e['variables']);need(all(i<n for m in ex for i,p in m),'out of range')
 out={'variables':n,'quadratic_rows' if max(map(degree,rows))<=2 else 'residual_rows':len(rows),'exact_degree':degree(ex),'expanded_monomials':len(ex),'max_abs_expanded_coefficient':max(map(abs,ex.values())),'max_abs_row_coefficient':max(abs(c) for p in rows for c in p.values())}
 return out,ex

def verify_chart(root,n):
 source=read(root/'inherited'/('pooled'+str(n))/'equation.json');target=read(root/('chart'+str(n))/'equation.json');cert=read(root/('chart'+str(n))/'chart_certificate.json')
 need(sha(source)==cert['source_sha256'],'chart source digest');need(sha(target)==cert['target_sha256'],'chart target digest')
 inv={int(v):load(p) for v,p in cert['inverse_map'].items()};fwd={int(v):load(p) for v,p in cert['forward_map'].items()};changed=set(inv)
 need(set(fwd)==changed,'map target sets');need(set(cert['unchanged_variables'])==set(range(n))-changed,'unchanged set')
 F={i:atom(i) for i in range(n)};operation_targets=set()
 for op in cert['operations']:
  v=op['variable'];a=load(op['addition']);need(v in changed,'unexpected target');operation_targets.add(v)
  need(all(c>0 and sum(power for j,power in m)<=1 and all(j!=v for j,power in m) for m,c in a.items()),'nonnegative elementary shear')
  F[v]=plus(F[v],replace(a,F))
 need(operation_targets==changed,'incomplete operation targets')
 for i in range(n):
  need(F[i]==fwd.get(i,atom(i)),'forward map mismatch')
  need(replace(inv.get(i,atom(i)),fwd)==atom(i),'inverse after forward')
  need(replace(fwd.get(i,atom(i)),inv)==atom(i),'forward after inverse')
 need(len(source['residuals'])==len(target['residuals']),'row count')
 for j,(r,s) in enumerate(zip(source['residuals'],target['residuals'])):
  need(replace(load(r['terms']),inv)==load(s['terms']),'literal transformed row '+str(j))
 seen=set();definitions=[]
 for v,j in cert['original_defining_rows']:
  need(v in changed and v not in seen,'duplicate gate definition');p=load(source['residuals'][j]['terms']);need(p.get(((v,1),))==1,'nonmonic gate definition');f=plus(atom(v),coeff(-1,p))
  need(all(c>0 and all(i!=v for i,power in m) for m,c in f.items()),'nonnegative source gate polynomial')
  dependencies={i for m in f for i,power in m if i in changed};need(dependencies<=seen,'cyclic natural-restoration dependency')
  definitions.append({'variable':v,'name':source['variables'][v]['name'],'row':j,'earlier_translated_dependencies':sorted(dependencies)});seen.add(v)
 need(seen==changed,'missing natural restoration gate')
 met,ex=metrics(target);need(met==target['metrics'],'chart metric mismatch');need(ex==load(read(root/('chart'+str(n))/'expanded_polynomial.json')['terms']),'all literal coefficients')
 return {'metrics':met,'forward_and_inverse_affine_identities':True,'all_transformed_rows':True,'all_expanded_coefficients':True,'natural_restoration_order':definitions}

def verify_octic(root):
 source=read(root/'chart202/equation.json');target=read(root/'natural200_degree8/equation.json');cert=read(root/'natural200_degree8/elimination_certificate.json');need(sha(source)==cert['source_sha256'],'octic source digest');need(sha(target)==cert['target_sha256'],'octic target digest')
 ns={x['name']:i for i,x in enumerate(source['variables'])};U=ns['pooled_power.U'];K=ns['pooled_power.K'];M=atom(ns['pooled_power.M']);n=atom(ns['pow2.output']);A=plus(atom(ns['shared.lower_A']),atom(ns['shared.A_slack']))
 names=[('index0.Y','index0.previous_Y',['choose0.modular_remainder','pooled_digits.t0.slack','crt.range.index.modular_remainder']),('index2.Y','index2.previous_Y',['crt.range.S.modular_remainder','pooled_digits.y.slack','crt.range.Sp.modular_remainder']),('index1.Y','index1.previous_Y',['crt.range.u.modular_remainder','pooled_digits.x.slack','crt.range.vq.modular_remainder'])]
 E={};UU={};H={};D2={}
 for yn,zn,ms in names:
  Y=atom(ns[yn]);D=plus({():1},atom(ns[zn]),*[atom(ns[s]) for s in ms]);err=plus(D,coeff(-1,times(n,Y)));E=plus(E,times(err,err));UU=plus(UU,times(Y,Y));H=plus(H,times(Y,D));D2=plus(D2,times(D,D))
 T=plus(coeff(2,times(A,n)),coeff(-1,times(n,n)),{():-1});R=plus(E,coeff(-1,times(T,M)));KK=plus(coeff(2,H),times(plus(coeff(2,A),coeff(-1,n)),M),coeff(-1,times(n,UU)))
 need(plus(times(n,KK),coeff(-1,D2),coeff(-1,M))==coeff(-1,R),'natural K restoration identity')
 removed=cert['deleted_rows'];need(cert['deleted_variables']==[U,K],'deleted variables')
 rows=[load(r['terms']) for r in source['residuals']];need(R==plus(rows[removed[2]],times(n,rows[removed[1]]),coeff(-1,times(times(n,n),rows[removed[0]]))),'quartic elimination identity')
 need(load(cert['unpacked_direct_residual'])==R,'unpacked quartic')
 kept=cert['retained_indices'];need(kept==[i for i in range(202) if i not in (U,K)],'renumbering');ren={v:atom(i) for i,v in enumerate(kept)}
 retained=[p for j,p in enumerate(rows) if j not in removed]
 need(all(all(i not in (U,K) for i,power in m) for p in retained for m in p),'other eliminated incidence')
 expected=[replace(p,ren) for p in retained+[R]];need(expected==[load(r['terms']) for r in target['residuals']],'octic literal rows')
 met,ex=metrics(target);need(met==target['metrics'],'octic metric mismatch');need(ex==load(read(root/'natural200_degree8/expanded_polynomial.json')['terms']),'octic literal coefficients')
 return {'metrics':met,'quartic_identity':True,'natural_U_formula':True,'K_integrality_formula_and_nK_identity':True,'all_expanded_coefficients':True,'unbounded_n_positive_proof':'retained unpooled pow2; see PROOF.md'}

def main(root):
 out={f'chart{n}':verify_chart(root,n) for n in (202,203,204)};out['natural200_degree8']=verify_octic(root);out['status']='PASS';print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=ROOT);main(ap.parse_args().root)
