"""Independent integer-domain positivity certificate and exact polynomial audit.
No builder, positivity search, or elimination optimizer is imported.
"""
from pathlib import Path
from copy import deepcopy
import json,hashlib,argparse
from collections import defaultdict
from independent_polynomial import poly,verify_expansion
from verify_projection import verify as verify_projection

def need(ok,msg):
 if not ok:raise ValueError(msg)
def canonical(v):return (json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(v):return hashlib.sha256(canonical(v)).hexdigest()
def domain(parent,signed,conversion):
 need(parent['domain']=='nonnegative integers' and signed['domain']=='unrestricted integers','domain')
 need(digest(parent)==conversion['parent_sha256'],'parent identity')
 need(digest(signed)==conversion['signed_sha256'],'guarded identity')
 n=len(parent['variables']);nr=len(parent['residuals']);proof=conversion['positivity']
 guards=conversion['guards'];seeds=proof['guard_indices']
 need(len(seeds)==len(set(seeds)),'unique positivity seeds')
 need([g['variable'] for g in guards]==seeds,'guard coverage')
 need(signed['variables'][:n]==parent['variables'] and signed['residuals'][:nr]==parent['residuals'],'original prefix')
 need(len(signed['variables'])==n+3*len(guards) and len(signed['residuals'])==nr+len(guards),'guard lengths')
 for i,g in enumerate(guards):
  a,b,c=n+3*i,n+3*i+1,n+3*i+2;v=g['variable']
  need(0<=v<n and g['auxiliary']==[a,b,c],'guard freshness')
  need(poly(signed['residuals'][nr+i]['terms'])=={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1},'guard polynomial')
 known=set(seeds)
 for step in proof['proof_steps']:
  v=step['variable'];c=step['coefficient'];rhs=poly(step['rhs'])
  need(type(c)is int and c>0 and 0<=v<n and v not in known,'new sign inference')
  expected={(v,):c}
  for mon,a in rhs.items():
   need(all(0<=u<n and u!=v for u in mon),'RHS indices')
   expected[mon]=expected.get(mon,0)-a
  if step.get('kind')=='affine_square':
   root=poly(step['square_root']);expanded=defaultdict(int)
   need(all(len(m)<=1 and all(0<=u<n and u!=v for u in m) for m in root),'affine square certificate')
   for m,a in root.items():
    for k,b in root.items():expanded[tuple(sorted(m+k))]+=a*b
   need({m:a for m,a in expanded.items() if a}==rhs,'exact square expansion')
  else:
   for mon,a in rhs.items():
    need(a>0,'nonnegative monomial coefficient')
    need(all(mon.count(u)%2==0 or u in known for u in set(mon)),'monomial nonnegativity')
  expected={m:a for m,a in expected.items() if a}
  row=poly(parent['residuals'][step['row']]['terms'])
  need(row==expected or row=={m:-a for m,a in expected.items()},'exact original row')
  known.add(v)
 need(known==set(range(n)),'all natural source variables recovered')
 return {'status':'PASS','original_variables':n,'guarded_inputs':len(guards),'derived_nonnegative':len(known)-len(guards),'guarded_variables':len(signed['variables'])}
def main(directory):
 d=Path(directory).resolve();parent=json.loads((d/'source_natural.json').read_text());signed=json.loads((d/'guarded.json').read_text());c=json.loads((d/'domain_conversion.json').read_text());eq=json.loads((d/'equation.json').read_text());proj=json.loads((d/'elimination_certificate.json').read_text());expanded=json.loads((d/'expanded_polynomial.json').read_text())
 pins=json.loads((d/'SOURCE_PINS.json').read_text());need(hashlib.sha256((d/'source_natural.json').read_bytes()).hexdigest()==pins['parent_sha256'],'pinned source')
 r={'status':'PASS','domain':domain(parent,signed,c),'projection':verify_projection(signed,eq,proj),'metrics':verify_expansion(eq,expanded)}
 bad=deepcopy(c);bad['positivity']['proof_steps'][0]['rhs'][0][0]+=1
 try:domain(parent,signed,bad)
 except ValueError:r['corrupted_sign_inference_rejected']=True
 else:raise ValueError('corrupt sign inference accepted')
 r['scope']='Integer-domain exact equivalence to pinned natural source; inherited C222/Pell calibration remains a named ordinary theorem.'
 (d/('INDEPENDENT_AUDIT.json' if __debug__ else 'INDEPENDENT_AUDIT_OPTIMIZED.json')).write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r,indent=2))
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('directory',type=Path);main(a.parse_args().directory)
