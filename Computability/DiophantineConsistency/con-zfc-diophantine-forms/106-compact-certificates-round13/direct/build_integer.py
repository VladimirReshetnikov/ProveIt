#!/usr/bin/env python3
"""Integer quartic companion with audited monotone sign closure.
Three triangular-number witnesses impose each remaining nonnegativity condition.
Gauss's three-triangular-number theorem is the named arithmetic dependency.
No upstream executable imports.
"""
import argparse, collections, hashlib, json, pathlib

def write(p,x):
 data=(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode();p.write_bytes(data);return hashlib.sha256(data).hexdigest()
def rules(raw):
 result=[]
 for j,row in enumerate(raw['residuals']):
  coeff={tuple(m):c for c,m in row['terms']}
  for mon,c in coeff.items():
   if len(mon)!=1:continue
   v=mon[0]
   if any(v in other for other in coeff if other!=mon):continue
   rest={m:-d*(1 if c>0 else -1) for m,d in coeff.items() if m!=mon}
   if any(d<0 for d in rest.values()):continue
   deps=set()
   for m,d in rest.items():
    if d:
     for w,power in collections.Counter(m).items():
      if power%2:deps.add(w)
   result.append({'row':j,'variable':v,'positive_divisor':abs(c),'dependencies':sorted(deps)})
 return result
def closure(seed,rs):
 known=set(seed);proof=[]
 changed=True
 while changed:
  changed=False
  for k,r in enumerate(rs):
   v=r['variable']
   if v not in known and set(r['dependencies'])<=known:
    known.add(v);proof.append(k);changed=True
 return known,proof
def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,default=pathlib.Path(__file__).parent/'short_beta_oriented_shared');p.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).parent/'integer');p.add_argument('--free-quotients',action='store_true');args=p.parse_args()
 raw=json.loads((args.source/'circuit.json').read_text());nat=json.loads((args.source/'equation.json').read_text());rest=json.loads((args.source/'affine_restoration.json').read_text());mapping={int(k):v for k,v in rest['old_to_new'].items()}
 rs=rules(raw);exempt=set(raw['bindings'].get('unrestricted_integer_quotients',[])) if args.free_quotients else set();required={i for i,v in enumerate(raw['variables']) if v['kind']!='gate' and i not in exempt};seed=set(required)
 # Remove a seed only if exact sign inference still establishes every semantic variable.
 for v in sorted(required):
  found,_=closure(seed-{v},rs)
  if required<=found:seed.remove(v)
 known,proof=closure(seed,rs)
 if not required<=known:raise ValueError('insufficient nonnegativity seeds')
 variables=list(nat['variables']);rows=list(nat['residuals']);seed_indices=[]
 for old in sorted(seed):
  idx=mapping[old];seed_indices.append(idx);aux=[]
  for r in range(3):
   aux.append(len(variables));variables.append({'name':'triangular.'+str(idx)+'.'+str(r),'kind':'integer_auxiliary'})
  terms=[[2,[idx]]]
  for j in aux:terms += [[-1,[j]],[-1,[j,j]]]
  rows.append({'label':'nonnegative.'+str(idx),'terms':terms})
 polynomial=collections.defaultdict(int)
 for row in rows:
  for a,ma in row['terms']:
   for b,mb in row['terms']:polynomial[tuple(sorted(ma+mb))]+=a*b
 polynomial={m:c for m,c in polynomial.items() if c}
 metrics={'integer_variables':len(variables),'quadratic_residuals':len(rows),'degree':max(map(len,polynomial)),'monomials':len(polynomial),'coefficient_height':max(map(abs,polynomial.values())),'nonnegativity_seeds':len(seed),'semantic_variables':len(required),'nonnegative_semantic_variables_inferred':len(required)-len(seed),'unrestricted_integer_quotients':len(exempt)}
 args.output.mkdir(parents=True,exist_ok=True)
 data={'format':'explicit_quadratic_residuals_v1','domain':'integers','variables':variables,'residuals':rows,'metrics':metrics};poly={'format':'ordinary_sparse_polynomial_v1','domain':'integers','variable_count':len(variables),'terms':[[c,list(m)] for m,c in sorted(polynomial.items())]}
 hashes={name:write(args.output/name,obj) for name,obj in [('equation.json',data),('expanded_polynomial.json',poly),('sign_certificate.json',{'raw_seed_indices':sorted(seed),'exported_seed_indices':seed_indices,'rules':rs,'application_order':proof,'required_semantic_variables':sorted(required),'known_nonnegative_variables':sorted(known),'unrestricted_integer_quotients':sorted(exempt)})]}
 receipt={'metrics':metrics,'sha256':hashes,'natural_equation_sha256':hashlib.sha256((args.source/'equation.json').read_bytes()).hexdigest(),'raw_circuit_sha256':hashlib.sha256((args.source/'circuit.json').read_bytes()).hexdigest(),'dependency':'Gauss three-triangular-number theorem','scope':'explicit quartic integer companion; finite closure certificate and mathematical theorem, not kernel certification'}
 write(args.output/'BUILD.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
