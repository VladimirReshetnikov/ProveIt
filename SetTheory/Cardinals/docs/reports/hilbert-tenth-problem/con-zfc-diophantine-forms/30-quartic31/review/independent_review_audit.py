if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Independent inert-JSON audits, newly authored for round4."""
from pathlib import Path
from collections import defaultdict,Counter
from itertools import product
from math import comb,factorial
import json,hashlib
ROOT=Path(__file__).resolve().parent

def plus(a,b):
 r=dict(a)
 for m,c in b.items():r[m]=r.get(m,0)+c
 return {m:c for m,c in r.items() if c}
def times(a,b):
 r=defaultdict(int)
 for x,c in a.items():
  for y,d in b.items():r[tuple(u+v for u,v in zip(x,y))]+=c*d
 return {m:c for m,c in r.items() if c}
def records(x):return {tuple(t['powers']):t['coefficient'] for t in x}
def shift_one(p,n):
 out=defaultdict(int)
 for mon,c in p.items():
  at=[i for i in range(n) if mon[i]]
  for exps in product(*(range(mon[i]+1) for i in at)):
   m=list(mon);v=c
   for i,e in zip(at,exps):m[i]=e;v*=comb(mon[i],e)
   out[tuple(m)]+=v
 return {m:c for m,c in out.items() if c}
def parent_audit():
 path=ROOT/'18-jones9/base/quartic32.upstream.json';p=json.loads(path.read_text());n=len(p['variables']);k=len(p['constants']);poly={};s={(0,)*k:2};rho=[]
 for equation in p['equations']:
  r=records(equation['terms']);assert max(sum(m[:n]) for m in r)<=2
  shifted=shift_one(r,n);poly=plus(poly,times(shifted,shifted));rp=defaultdict(int)
  for m,c in r.items():rp[m[n:]]+=abs(c)*2**sum(m[:n])
  rp=dict(rp);rho.append(rp);s=plus(s,{m:24*c for m,c in times(rp,rp).items()})
 constants=json.loads((ROOT/'18-jones9/nine/generated/constants.json').read_text());expected=json.loads((ROOT/'18-jones9/nine/generated/shifted_quartic.json').read_text());index=json.loads((ROOT/'18-jones9/nine/generated/index_bound_s.json').read_text())
 assert poly==records(expected['terms']);assert s==records(index['terms']);assert rho==[records(x) for x in index['rho']]
 grouped=defaultdict(dict)
 for m,c in poly.items():
  alpha=(0,)+m[:n];weight=factorial(4-sum(alpha))
  for e in alpha:weight*=factorial(e)
  grouped[alpha][m[n:]]=c*weight
 assert len(grouped)==len(constants['coefficient_records'])
 for rec in constants['coefficient_records']:
  alpha=tuple(rec['alpha']);assert grouped[alpha]==records(rec['coefficient_polynomial_in_fixed_ports']);assert rec['expo']==sum(v*5**i for i,v in enumerate(alpha))
 assert constants['L']==5**(n+1);assert constants['bounded_sum_cardinality']==comb(n+5,4)
 # All-ones fifth residual, preserving symbolic compiler ports.
 normal=defaultdict(int)
 for m,c in records(p['equations'][4]['terms']).items():normal[m[n:]]+=c
 normal={m:c for m,c in normal.items() if c};assert normal=={(0,)*k:1}
 assert hashlib.sha256(path.read_bytes()).hexdigest()==constants['parent_sha256']
 return dict(variables=n,residuals=len(p['equations']),quartic_terms=len(poly),weighted_coefficients=len(grouped),index_bound_terms=len(s),normalizing_residual=5,normalizing_value=1,checks='Exact symbolic shift, sum of squares, slack factorial coefficients, exponent codes, coefficient majorant, normalization, and source digest all match.')

def circuit_counts():
 result=[]
 for p in sorted(ROOT.glob('[12][0-9]-*/**/*.json')):
  if 'nine/' in str(p) or '/base/' in str(p):continue
  d=json.loads(p.read_text());src=d.get('source');src=src if isinstance(src,list) else None
  if not src and isinstance(d.get('gates'),list):src=[[g['name'],g['op'],*g['args']] for g in d['gates']]
  if not src:continue
  variables=d.get('witnesses',d.get('unknowns',d.get('variables')));fixed=d.get('fixed_numerals',d.get('fixed_ports',d.get('coefficient_ports')))
  if not isinstance(variables,list) or not isinstance(fixed,list):continue
  seen=set(variables+fixed);graph={};counts=Counter()
  for name,op,a,b in src:
   assert name not in seen,(p,name)
   assert op in ('+','-','*')
   for v in (a,b):assert isinstance(v,int) or v in seen,(p,name,v)
   seen.add(name);graph[name]=(a,b);counts[op]+=1
  outputs=[]
  if 'output' in d:outputs.append(d['output'])
  elif 'outputs' in d:outputs+=d['outputs'] if isinstance(d['outputs'],list) else list(d['outputs'].values())
  elif 'comparisons' in d:
   for x in d['comparisons']:
    if isinstance(x,list):outputs.extend(x)
    elif isinstance(x,dict):outputs.extend([x.get('left'),x.get('right')])
  todo=list(outputs);live=set()
  while todo:
   x=todo.pop()
   if not isinstance(x,str) or x in live:continue
   live.add(x)
   if x in graph:todo.extend(graph[x])
  assert set(graph)<=live,(p,set(graph)-live,outputs)
  assert set(variables+fixed)<=live,(p,set(variables+fixed)-live)
  result.append(dict(path=str(p.relative_to(ROOT)),variables=len(variables),operations=len(src),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],declared_degree=d.get('exact_degree',d.get('total_degree',d.get('exact_maximum_degree'))),degree_status='Declared value, not rederived by this count-only audit.'))
 return result

# Exact all-unknowns=t leading coefficient with independent symbolic fixed leaves.
def leading_audit(path):
 d=json.loads(path.read_text());names=sorted(n['name'] for n in d['nodes'] if n['kind']=='fixed');idx={n:i for i,n in enumerate(names)};z=(0,)*len(names);values=[];maximum=0
 def scalar(a):return {} if a==0 else {z:a}
 for pos,n in enumerate(d['nodes']):
  k=n['kind']
  if k=='variable':r=(1,scalar(1))
  elif k=='fixed':m=list(z);m[idx[n['name']]]=1;r=(0,{tuple(m):1})
  elif k=='literal':r=(0,scalar(n['value']))
  else:
   da,a=values[n['left']];db,b=values[n['right']]
   if k=='mul':r=(da+db,times(a,b))
   elif not a:r=(db,b if k=='add' else {m:-v for m,v in b.items()})
   elif not b:r=(da,a)
   elif da>db:r=(da,a)
   elif db>da:r=(db,b if k=='add' else {m:-v for m,v in b.items()})
   else:
    c=plus(a,b if k=='add' else {m:-v for m,v in b.items()})
    if not c:raise ValueError(('Leading cancellation needing deeper terms',pos,n,da))
    r=(da,c)
  values.append(r);maximum=max(maximum,len(r[1]))
 degree,leader=values[d['output']];assert leader==scalar(2**328);assert degree==161844*5**33+484
 return dict(path=str(path.relative_to(ROOT)),exact_degree=degree,uniform_diagonal_leading_coefficient='2^328',maximum_symbolic_leading_terms=maximum,named_degrees={k:values[v][0] for k,v in d['named_nodes'].items()},checks='Every gate has exact symbolic leading term; no unresolved top cancellation; final leader independent of every fixed coefficient.')

def main():
 result={'coefficient_index':parent_audit(),'circuit_counts':circuit_counts(),'nine_leading_audits':[]}
 for p in [ROOT/'18-jones9/nine/generated/nine_majorant_dag.json',ROOT/'nine_optimized/nine_majorant_runs.json']:result['nine_leading_audits'].append(leading_audit(p))
 (ROOT/'INDEPENDENT_REVIEW_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
