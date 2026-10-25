#!/usr/bin/env python3
"""Independent exact checker for a monic polynomial residual contraction."""
import argparse,copy,hashlib,json
from pathlib import Path

def read_terms(terms):
 p={}
 for c,raw in terms:
  if type(c) is not int or not c:raise ValueError('invalid coefficient')
  if any(type(i) is not int or i<0 for i in raw):raise ValueError('invalid index')
  m=tuple(raw)
  if m!=tuple(sorted(m)) or m in p:raise ValueError('noncanonical monomial')
  p[m]=c
 return p
def plus(p,q,scale=1):
 r=p.copy()
 for m,c in q.items():r[m]=r.get(m,0)+scale*c
 return {m:c for m,c in r.items() if c}
def times(p,q):
 result={}
 for a,c in p.items():
  for b,d in q.items():
   m=tuple(sorted(a+b));result[m]=result.get(m,0)+c*d
 return {m:c for m,c in result.items() if c}
def substitute(p,images):
 result={}
 for monomial,coefficient in p.items():
  term={():coefficient}
  for i in monomial:term=times(term,images[i])
  result=plus(result,term)
 return result
def check(source,equation,expanded,certificate,metrics):
 n=len(source['variables']);v=certificate['deleted_variable'];pivot=certificate['pivot_row']
 if source['domain']!='unrestricted integers' or equation['domain']!='unrestricted integers':raise ValueError('domain')
 source_rows=[read_terms(r['terms']) for r in source['residuals']]
 expected_variables=[i for i in range(n) if i!=v]
 expected_rows=[i for i in range(len(source_rows)) if i!=pivot]
 if certificate['retained_source_variables']!=expected_variables or certificate['retained_source_rows']!=expected_rows:raise ValueError('retention lists')
 if equation['variables']!=[source['variables'][i] for i in expected_variables]:raise ValueError('variables')
 old_pivot=source_rows[pivot];co=old_pivot.get((v,))
 if co not in (-1,1) or any(v in m for m in old_pivot if m!=(v,)):raise ValueError('nonmonic pivot')
 replacement={m:-co*c for m,c in old_pivot.items() if m!=(v,)}
 if replacement!=read_terms(certificate['replacement_in_source_indices']):raise ValueError('replacement')
 images=[replacement if i==v else {(i,):1} for i in range(n)]
 pulled=[substitute(p,images) for p in source_rows]
 if pulled[pivot]:raise ValueError('pivot does not vanish')
 changed=set()
 for op in certificate['post_substitution_residual_operations']:
  i,j=op['target_row'],op['retained_reducer_row']
  if i==j or pivot in (i,j) or j in changed or any(v in m for m in source_rows[j]):raise ValueError('nonreversible operation')
  multiplier=read_terms(op['subtract_multiplier'])
  if any(v in m for m in multiplier):raise ValueError('eliminated coordinate in multiplier')
  pulled[i]=plus(pulled[i],times(multiplier,pulled[j]),-1);changed.add(i)
 renaming={i:k for k,i in enumerate(expected_variables)}
 def ren(p):return {tuple(renaming[i] for i in m):c for m,c in p.items()}
 computed=[ren(pulled[i]) for i in expected_rows]
 supplied=[read_terms(r['terms']) for r in equation['residuals']]
 if computed!=supplied:raise ValueError('residual mismatch')
 if any(max(map(len,p),default=0)>2 for p in supplied):raise ValueError('nonquadratic')
 restore=[ren(p) for p in images]
 if restore!=[read_terms(t) for t in certificate['restoration_in_final_coordinates']]:raise ValueError('restoration mismatch')
 poly={}
 for p in supplied:poly=plus(poly,times(p,p))
 if poly!=read_terms(expanded['terms']):raise ValueError('expanded polynomial mismatch')
 live={i for m in poly for i in m}
 if live!=set(range(n-1)):raise ValueError('dead or missing variable')
 actual={'variables':n-1,'rows':len(supplied),'degree':max(map(len,poly),default=0),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for p in supplied for c in p.values()),'row_support':sum(map(len,supplied))}
 if actual!=metrics:raise ValueError('metrics')
 return actual
def main():
 ap=argparse.ArgumentParser();ap.add_argument('directory');a=ap.parse_args();d=Path(a.directory)
 raw=(d/'source_equation.json').read_bytes();source=json.loads(raw)
 equation=json.loads((d/'equation.json').read_bytes());expanded=json.loads((d/'expanded_polynomial.json').read_bytes());certificate=json.loads((d/'projection_certificate.json').read_bytes());metrics=json.loads((d/'METRICS.json').read_bytes())
 if hashlib.sha256(raw).hexdigest()!=certificate['source_sha256']:raise ValueError('source digest')
 actual=check(source,equation,expanded,certificate,metrics)
 rejected=[]
 for label,target in [('replacement','certificate'),('row','equation'),('expansion','expanded')]:
  e,p,c=copy.deepcopy(equation),copy.deepcopy(expanded),copy.deepcopy(certificate)
  if target=='certificate':c['replacement_in_source_indices'][0][0]+=1
  elif target=='equation':e['residuals'][0]['terms'][0][0]+=1
  else:p['terms'][0][0]+=1
  try:check(source,e,p,c,metrics)
  except ValueError:rejected.append(label)
  else:raise ValueError('mutation accepted: '+label)
 print(json.dumps({'status':'PASS','metrics':actual,'semantic_mutations_rejected':rejected,'proof_scope':'Exact integer zero-set bijection of supplied residual systems; arithmetic source calibration inherited.'},sort_keys=True,indent=2))
if __name__=='__main__':main()
