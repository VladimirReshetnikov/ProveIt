#!/usr/bin/env python3
"""Independent exact affine-chart certification; Python standard library only."""
import json,hashlib,argparse,copy
from pathlib import Path
from collections import defaultdict
ROOT=Path(__file__).resolve().parent
SRC=ROOT/'source_equation.json'
BASIS=ROOT/'row_operations.json'
def read(p):return json.loads(Path(p).read_text())
def dump(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def load(ts):
 d={}
 for c,m in ts:
  if type(c)is not int or not c or m!=sorted(m) or tuple(m) in d:raise ValueError('invalid terms')
  d[tuple(m)]=c
 return d
def atom(i):return {(i,):1}
def plus(*polys):
 d=defaultdict(int)
 for p in polys:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def times(p,q):
 d=defaultdict(int)
 for m,c in p.items():
  for n,e in q.items():d[tuple(sorted(m+n))]+=c*e
 return {m:c for m,c in d.items() if c}
def scale(c,p):return {m:c*d for m,d in p.items() if c*d}
def substitute(p,mp):
 out={}
 for m,c in p.items():
  term={():c}
  for i in m:term=times(term,mp.get(i,atom(i)))
  out=plus(out,term)
 return out
def need(x,m):
 if not x:raise ValueError(m)
def hashobj(o):return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def write(p,x):Path(p).write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('candidate',type=Path);ap.add_argument('base',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--basis',action='store_true');a=ap.parse_args();a.output.mkdir(exist_ok=True,parents=True)
 source=read(SRC);base=read(a.base);candidate=read(a.candidate);n=len(source['variables'])
 original=[load(r['terms']) for r in source['residuals']]
 F={i:load(base['certificate']['forward_map'].get(str(i),[[1,[i]]])) for i in range(n)}
 G={i:load(base['certificate']['inverse_map'].get(str(i),[[1,[i]]])) for i in range(n)}
 # Check parent frame chart by literal simultaneous substitution, not replay assumptions.
 for i in range(n):need(substitute(F[i],G)==atom(i) and substitute(G[i],F)==atom(i),'initial inverse')
 rows=[substitute(p,G) for p in original]
 need([dump(p) for p in rows]==[r['terms'] for r in base['equation']['residuals']],'base rows')
 for op in candidate['operations']:
  v=op['v'];w=tuple(op['w']);c=op['c'];need(v not in w and len(w)<=1 and type(c)is int and c,'elementary operation')
  A={w:c};mapping={v:plus(atom(v),scale(-1,A))}
  F[v]=plus(F[v],substitute(A,F));G={i:substitute(g,mapping) for i,g in G.items()}
  rows=[substitute(p,mapping) for p in rows]
 basis=read(BASIS) if a.basis else []
 for i,j,k in basis:need(i!=j and k,'row shear');rows[i]=plus(rows[i],scale(k,rows[j]))
 need([dump(p) for p in rows]==candidate['residuals'],'candidate row replay')
 need({str(i):dump(f) for i,f in F.items()}==candidate['forward_map'],'candidate forward map replay')
 for i in range(n):need(substitute(F[i],G)==atom(i) and substitute(G[i],F)==atom(i),'final inverse')
 changed={i for i,f in F.items() if f!=atom(i)}
 definitions={}
 for v in changed:
  matches=[]
  for j,r in enumerate(original):
   if r.get((v,))==1 and all(v not in m and c<0 for m,c in r.items() if m!=(v,)):matches.append(j)
  need(len(matches)==1,'nonnegative source gate '+str(v));definitions[v]=matches[0]
 seen=set()
 for v,j in sorted(definitions.items(),key=lambda kv:kv[1]):
  deps={i for m in original[j] for i in m if i in changed and i!=v};need(deps<=seen,'gate dependency order');seen.add(v)
 # Positive representatives certify forward naturalness on original zero set.
 alldefs={}
 for v in range(n):
  if source['variables'][v]['kind'] not in ('gate','shared nonnegative shifted square'):continue
  for j,r in enumerate(original):
   if r.get((v,))==1 and all(v not in m and c<0 for m,c in r.items() if m!=(v,)):alldefs[v]=j;break
 positivity={}
 for v in sorted(changed):
  P=F[v].copy();comb=[]
  for w,j in sorted(alldefs.items(),key=lambda kv:-kv[1]):
   if all(c>=0 for c in P.values()):break
   c=P.get((w,),0)
   if c>0:P=plus(P,scale(-c,original[j]));comb.append([j,c])
  need(all(c>0 for c in P.values()),'forward nonnegative representative '+str(v))
  need(P==plus(F[v],*[scale(-c,original[j]) for j,c in comb]),'positive representative identity')
  positivity[str(v)]={'source_row_combination':comb,'nonnegative_representative':dump(P)}
 expanded=plus(*[times(r,r) for r in rows]);metrics={'variables':n,'quadratic_rows':len(rows),'exact_degree':max(map(len,expanded)),'expanded_monomials':len(expanded),'max_abs_expanded_coefficient':max(map(abs,expanded.values())),'max_abs_row_coefficient':max(abs(c) for r in rows for c in r.values())}
 need([metrics['expanded_monomials'],metrics['max_abs_expanded_coefficient']]==candidate['metrics'],'recorded metrics')
 equation=copy.deepcopy(source);equation['residuals']=[{'label':'round23.gatechart.s'+str(j),'terms':dump(p)} for j,p in enumerate(rows)];equation['metrics']=metrics;equation['variant']='round23_natural202_certified_affine_chart'
 cert={'schema':'natural_zero_set_positive_representative_chart_v1','source_sha256':hashobj(source),'target_sha256':hashobj(equation),'base_sha256':hashobj(base),'additional_operations':candidate['operations'],'row_operations':basis,'forward_map':{str(i):dump(F[i]) for i in sorted(changed)},'inverse_map':{str(i):dump(G[i]) for i in sorted(changed)},'original_defining_rows':sorted([[i,j] for i,j in definitions.items()],key=lambda pair:pair[1]),'forward_positivity':positivity,'unchanged_variables':[i for i in range(n) if i not in changed]}
 write(a.output/'equation.json',equation);write(a.output/'expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1','domain':source['domain'],'variables':n,'terms':dump(expanded)});write(a.output/'certificate.json',cert)
 write(a.output/'CHECK.json',{'status':'PASS','metrics':metrics,'both_affine_inverse_identities':True,'literal_all_residuals':True,'all_expanded_coefficients':True,'forward_positivity':True,'inverse_naturalness_gate_DAG':True,'source_sha256':hashobj(source),'target_sha256':hashobj(equation)})
 print(json.dumps(metrics,sort_keys=True))
if __name__=='__main__':main()
