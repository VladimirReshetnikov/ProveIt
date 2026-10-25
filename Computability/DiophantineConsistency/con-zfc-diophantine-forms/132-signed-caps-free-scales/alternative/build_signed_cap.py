#!/usr/bin/env python3
"""Finite literal signed-cap transformation; standard library and reviewed vendor only."""
from pathlib import Path
from collections import defaultdict
import json,sys,copy,hashlib,argparse,re
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import terminal_elimination as E
import factor_horn as FH

def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def scale(p,c):return {m:c*v for m,v in p.items()}
def build(out,odd_auxiliary=False):
 parent=json.loads((HERE/'source/parent_source.json').read_text()); eq=copy.deepcopy(parent)
 pre=json.loads((HERE/'source/parent_presemantic.json').read_text()); seeds=pre['seed_indices']
 names={v['name']:i for i,v in enumerate(eq['variables'])}; W=names['shared.W'];A=names['shared.A']
 omittedguards={s['slack'] for s in seeds}|{names['shared_index.q4minus1'],names['shared_index.Vquotient_minus1']}
 removed=[];kept=[]
 for rid,r in enumerate(eq['residuals']):
  lab=r['label']
  omit=(lab.startswith('shared_index.') or
   (re.fullmatch(r'index\d+\.(index_at_most_Y|norm3|S_mod_U|R_mod_4Y)',lab) is not None) or
   (lab.startswith('nonnegative.') and int(lab.split('.')[1]) in omittedguards))
  (removed if omit else kept).append((rid,r))
 eq['residuals']=[r for _,r in kept]
 def new(name):
  i=len(eq['variables']);eq['variables'].append({'name':'cap.'+name,'kind':'signed_cap'});return i
 def p(i):return {(i,):1}
 def row(name,poly):
  if E.degree(poly)>2:raise ValueError('nonquadratic '+name)
  eq['residuals'].append({'label':'cap.'+name,'terms':E.as_terms(poly)})
 def product(name,i,j):
  v=new(name);row(name,add(p(v),neg(E.multiply(p(i),p(j)))));return v
 def guard(i):
  a,b,c=(new('nonnegative.'+str(i)+'.'+z) for z in 'abc')
  row('nonnegative.'+str(i),add(p(i),{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}))
  return [a,b,c]
 cap={name:new(name) for name in ('U','V','H','J','B','S','R','d','e','f','g','h','slack','Q')}
 U,V,H,J,B,S,R,d,e,f,g,h,s,Q=(cap[x] for x in ('U','V','H','J','B','S','R','d','e','f','g','h','slack','Q'))
 AV=product('AV',A,V);AJ=product('AJ',A,J);BR=product('BR',B,R);VV=product('VV',V,V)
 row('norm', {(U,U):1,(V,V):1,(AV,AV):-1,():-1})
 row('auxiliary_norm', {(H,H):1,(J,J):1,(AJ,AJ):-1,():-1})
 row('comparison_norm', {(S,S):1,(R,R):1,(BR,BR):-1,():-1})
 row('comparison_progression',{(B,):1,():-1,tuple(sorted((V,d))):-4})
 row('auxiliary_divisibility',{(J,):1,(VV,):-1,tuple(sorted((VV,e))):(-2 if odd_auxiliary else -1)})
 row('comparison_base',{(B,):1,(A,):-1,tuple(sorted((H,f))):-1})
 row('comparison_abscissa',{(S,):1,(U,):-1,tuple(sorted((H,g))):-1})
 row('comparison_ordinate',{(R,):1,(W,):-2,tuple(sorted((V,h))):-4})
 caprow={(V,):1,(W,):-2,():-1,(s,):-1}
 pool={tuple(sorted((A,Q))):-1,(Q,):1}
 for seed in seeds:
  yi=seed['Y'];caprow[(yi,yi)]=-1
  diff=add(p(yi),neg(E.normalize(seed['exponent'])))
  pool=add(pool,E.multiply(diff,diff))
 row('squared_aggregate',caprow);row('pooled_index_residue',pool)
 guards={'slack':guard(s)}
 if not odd_auxiliary:guards['e']=guard(e)
 eq['domain']='unrestricted integers';eq['variant']='direct_signed_pooled_squared_cap'
 factored,fc=FH.transform(eq)
 final,pc,metrics=E.optimize(factored,max_support=16)
 receipt=E.verify(factored,final,pc)
 cert={'schema':'signed_pooled_squared_cap_v1','parent_sha256':hashlib.sha256(E.canonical_bytes(parent)).hexdigest(), 'parent_rows_removed':[{'row':i,'literal':r} for i,r in removed], 'parent_rows_retained':[i for i,_ in kept], 'seed_indices':seeds,'cap_variables':cap,'cap_guard_witnesses':guards,'cap_index':[[2,[W]]],'W':W,'A':A,'theorem':'PROOF.md','comparison_base_domain':'unrestricted; abs(B)>=2 follows from auxiliary norm and abs(J)>1','odd_auxiliary':odd_auxiliary}
 out.mkdir(parents=True,exist_ok=True)
 artifacts={'raw_equation.json':eq,'cap_certificate.json':cert,'factored_source.json':factored,'factorization_certificate.json':fc,'equation.json':final,'projection_certificate.json':pc,'terminal_elimination_certificate.json':pc,'expanded_polynomial.json':E.expand(final),'METRICS.json':metrics|receipt}
 for n,v in artifacts.items():(out/n).write_bytes(E.canonical_bytes(v))
 print(json.dumps(artifacts['METRICS.json'],indent=2))
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('output',type=Path);a.add_argument('--odd-auxiliary',action='store_true');args=a.parse_args();build(args.output,args.odd_auxiliary)
