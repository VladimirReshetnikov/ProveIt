#!/usr/bin/env python3
"""Read pinned inert source data; generate affine selective-positivity residuals."""
import hashlib,json,pathlib,math
import sympy as s
ROOT=pathlib.Path(__file__).resolve().parent
SOURCE=ROOT/'data/source_system60.json'
HASH='ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48'
SHIFT12=['F','alpha','z','h','i','j','s','w','eta','zeta','gamma','g']

def load_rows():
 raw=SOURCE.read_bytes()
 if hashlib.sha256(raw).hexdigest()!=HASH:raise RuntimeError('Pinned source mismatch')
 data=json.loads(raw);names=data['variables'];ports=data['constants']
 var=s.symbols(' '.join(names));env=dict(zip(names,var));env.update({k:s.Symbol(k) for k in ports})
 def get(k):return s.Integer(k) if isinstance(k,int) else env[k]
 for name,op,a,b in data['source']:
  a,b=get(a),get(b)
  if op=='+':env[name]=a+b
  elif op=='-':env[name]=a-b
  elif op=='*':env[name]=a*b
  else:raise RuntimeError(op)
 return data,var,env,[s.expand(get(a)-get(b)) for a,b in data['comparisons']]

def records(rows,var):
 out=[];active=set()
 for j,r in enumerate(rows):
  poly=s.Poly(s.expand(r),*var)
  terms=[]
  for alpha,coef in poly.terms():
   if sum(alpha)>2:raise RuntimeError('Nonquadratic source')
   mult=math.factorial(2-sum(alpha))*math.prod(math.factorial(a) for a in alpha)
   terms.append(dict(alpha=list(alpha),coefficient=str(coef),weighted_coefficient=str(s.expand(mult*coef))))
   active.add(alpha)
  out.append(dict(original_row_one_based=j+1,polynomial=str(poly.as_expr()),terms=terms))
 return out,active

def main():
 data,var,env,original=load_rows()
 for label,shifts in [('all31',data['variables']),('selective12',SHIFT12)]:
  rows=[s.expand(r.subs({env[k]:env[k]+1 for k in shifts},simultaneous=True)) for r in original]
  rr,active=records(rows,var)
  out=dict(name=label,source_file=str(SOURCE.relative_to(ROOT)),source_sha256=HASH,variables=data['variables'],ports=data['constants'],domain='nonnegative integers',shifted_coordinates=shifts,coordinate_map={k:k+('+1' if k in shifts else '') for k in data['variables']},row_count=len(rows),coefficient_record_count=sum(len(r['terms']) for r in rr),active_monomial_count=len(active),quadratic_monomial_count=sum(sum(a)==2 for a in active),linear_monomial_count=sum(sum(a)==1 for a in active),rows=rr)
  (ROOT/f'{label}_source.json').write_text(json.dumps(out,indent=2)+'\n')
  pairrows=[];pairs=set()
  for j,r in enumerate(rr):
   for t in r['terms']:
    pair=[0]*(2-sum(t['alpha']))
    for i,a in enumerate(t['alpha']):pair.extend([i+1]*a)
    pairrows.append(f'{j} {pair[0]} {pair[1]}')
    pairs.add(tuple(pair))
  (ROOT/f'{label}_row_pairs.txt').write_text('\n'.join(pairrows)+'\n')
  (ROOT/f'{label}_support_pairs.txt').write_text('\n'.join(f'{a} {b}' for a,b in sorted(pairs))+'\n')
  print(label,out['coefficient_record_count'],out['active_monomial_count'])
if __name__=='__main__':main()
