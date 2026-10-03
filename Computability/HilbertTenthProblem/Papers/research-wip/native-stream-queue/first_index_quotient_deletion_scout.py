#!/usr/bin/env python3
"""Bounded source-only h deletion probe; no positive-converse claim."""
import argparse, collections, hashlib, json
from pathlib import Path
PINS={'complete85_auxiliary_bezout_projection.json':'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc','complete86_ordinary_auxiliary_projection.json':'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6'}
def require(x):
 if not x: raise ValueError('probe assertion failed')
def evaluate(source,values):
 v=dict(values)
 for name,op,a,b in source:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return v

def pell(A,n):
 D,c=1,0
 for _ in range(n):D,c=A*D+(A*A-1)*c,D+A*c
 return D,c

def run(root):
 forms=[]
 for filename,prefix in PINS.items():
  raw=(root/filename).read_bytes();sha=hashlib.sha256(raw).hexdigest();require(sha==prefix)
  p=json.loads(raw)['packet'];src=p['source']
  rows={r[0]:r for r in src};cons=lambda n:[r[0] for r in src if n in r[2:]]
  require(cons('h')==['hpm1'] and cons('hpm1')==['index_difference'])
  require(cons('index_difference')==['norm_index'] and cons('norm_index')==['norm_product'])
  require(rows['hpm1']==['hpm1','*','h','UM'])
  require(rows['index_difference']==['index_difference','-','R10b','hpm1'])
  require(rows['norm_index']==['norm_index','-','index_difference','r_lhs'])
  require(rows['norm_product']==['norm_product','*','norm_four','norm_index'])
  require(rows['all_units']==['all_units','*','norm_product','norm_transport'])
  require(rows['seven_units']==['seven_units','*','all_units','norm_strong'])
  require(rows[p['output']]==[p['output'],'-','seven_units',1])
  removed={'hpm1','index_difference','norm_index','norm_product'}
  child=[[n,op,*['norm_four' if a=='norm_product' else a for a in ab]] for n,op,*ab in src if n not in removed]
  free=[a for a in p['free'] if a!='h'];witnesses=[a for a in p['witnesses'] if a!='h']
  seen=set(free)
  for n,op,a,b in child:
   require(n not in seen and op in ['+','-','*']);require(all(not isinstance(z,str) or z in seen for z in [a,b]));seen.add(n)
  live={p['output']}
  for n,op,a,b in reversed(child):
   require(n in live);live.update(z for z in [a,b] if isinstance(z,str))
  require(set(free)<=live and len(witnesses)==17)
  for trial in range(24):
   vals={a:((i*7+trial*3)%9-4) for i,a in enumerate(p['free'])}
   old=evaluate(src,vals);new=evaluate(child,vals)
   require(old[p['output']]+1==(new[p['output']]+1)*old['norm_index'])
   require(all(old[n]==new[n] for n in ['norm_first','norm_main','norm_input','norm_aux','norm_transport','norm_strong']))
  counts=collections.Counter(r[1] for r in child)
  forms.append({'parent':filename,'parent_sha256':sha,'source':child,'free':free,'witnesses':witnesses,'output':p['output'],'ledger':{'M':counts['*'],'A':counts['+']+counts['-'],'total':len(child)},'exact_degree_by_retained_parent_leaders':p['exact_degree']-7,'correction_cases':24})
 p,n=27,15;X=2**p;Y=162259287306570765957544386371535
 a=Y*(X+1);A=a+2;P=2*X*Y*Y+1;D,c=pell(A,p);tau,khalf=pell(P,n);k=2*khalf;E=X*Y;H=4*a+3
 eta=c-k*Y;zeta=k-eta;gamma=(D-a*c-X)//H
 require(eta>0 and zeta>0 and gamma>1 and (D-a*c-X)%H==0)
 require(D*D-(A*A-1)*c*c==1 and tau*tau-E*k*Y*(E*k*Y+k)==1)
 require((k-p-1)%E==2 and k>p+1 and Y%2==1)
 return {'status':'PASS','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Source-only deletion. Positive inverse unresolved; no universal improvement and no full-source counterexample.','forms':forms,'component_obstruction':{'main_index':p,'first_index':n,'X':X,'Y':Y,'eta_positive':True,'zeta_positive':True,'main_projection_gamma_positive':True,'restored_h_numerator_positive':True,'restored_h_remainder':2,'excluded_full_source_condition':'For this fixed X=2^27, q divides X and q>=16 would force q even; odd Y cannot equal s*q^3.'}}
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if isinstance(a,list):return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 r=run(a.root)
 require(same(r,json.loads(json.dumps(r))))
 if a.expect:require(same(r,json.loads(a.expect.read_text())))
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'ledgers':[p['ledger']for p in r['forms']],'degrees':[p['exact_degree_by_retained_parent_leaders']for p in r['forms']],'component':r['component_obstruction']},sort_keys=True))

if __name__=='__main__':main()
