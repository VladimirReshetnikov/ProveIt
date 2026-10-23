#!/usr/bin/env python3
"""Finite circuit and exact-multiplier checks, independent of the builder."""
import gzip,json,random
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def need(x,m):
 if not x: raise RuntimeError(m)
def evaluate(body, vals, fixed, prime):
 out=[]
 for row in body['nodes']:
  kind=row['kind']
  if kind=='literal':v=row['value']
  elif kind=='fixed':v=fixed[row['name']]
  elif kind=='variable':v=vals[row['name']]
  else:
   a,b=out[row['left']],out[row['right']]
   v=a+b if kind=='add' else a-b if kind=='sub' else a*b
  out.append(v%prime)
 return out[body['output']],{k:out[i] for k,i in body['named_nodes'].items()}
def fixed_values(body,p):
 ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients'/f'{n}.bin.gz').read_bytes()),'little')%p for n in ('beta','K','MC','MF_source')]
 result={'base_scale':pow(2,body['base_scale_exponent'],p),'threshold_scale':pow(2,body['threshold_scale_exponent'],p)}
 for rec in body['coefficient_recipes']:
  s=0
  for term in rec['terms']:
   v=term['coefficient']
   for x,k in zip(ports,term['powers']):v=v*pow(x,k,p)%p
   s=(s+v)%p
  result[rec['name']]=s
 return result
def degree_leader(body,fixed,p):
 # Track the coefficient at the syntactic upper degree on the diagonal.
 # A nonzero final coefficient modulo p proves the bound is attained over Z.
 # This imports neither the builder nor its symbolic degree routine.
 rows=[]
 for n in body['nodes']:
  k=n['kind']
  if k=='variable':r=(1,1)
  elif k=='literal':r=(0,n['value']%p)
  elif k=='fixed':r=(0,fixed[n['name']])
  else:
   (da,ca),(db,cb)=rows[n['left']],rows[n['right']]
   if k=='mul':r=(da+db,ca*cb%p)
   else:
    sign=1 if k=='add' else -1
    degree=max(da,db)
    r=(degree,((ca if da==degree else 0)+sign*(cb if db==degree else 0))%p)
  rows.append(r)
 return rows[body['output']],{k:rows[i] for k,i in body['named_nodes'].items()}
rng=random.Random(134901);count=0
degree_checks=[]
for domain in ('natural','positive'):
 base=json.loads((ROOT/'generated'/f'calibrated_{domain}.json').read_text())
 cert=json.loads((ROOT/'generated'/f'calibrated_{domain}_certificate.json').read_text())
 need(base['degree_certificate_variant'] is False and cert['degree_certificate_variant'] is True,'variant types')
 for body in (base,cert):
  live=set();queue=[body['output']]
  while queue:
   k=queue.pop()
   if k in live:continue
   live.add(k);r=body['nodes'][k]
   if r['kind'] in ('add','sub','mul'):
    need(0<=r['left']<k and 0<=r['right']<k,'invalid order')
    queue.extend((r['left'],r['right']))
  need(len(live)==len(body['nodes']),'dead gate')
  need(sum(r['kind'] in ('add','sub','mul') for r in body['nodes'])==body['total_operations'],'operation count')
 for p in (1000003,1000033,1000000007):
  fixed=fixed_values(base,p)
  (dc,lc),nc=degree_leader(cert,fixed,p)
  dd,ld=nc['D']
  need(lc!=0 and ld!=0,'degree bound not certified modulo prime')
  need(dc==7900853 and dd==139324 and dc-16*dd==5671669,'exact degree mismatch')
  need(cert['exact_degree']==dc and base['exact_degree']==dc-16*dd,'circuit degree metadata mismatch')
  expected=pow(2,667,p)*pow(fixed['base_scale'],3950070,p)*pow(fixed['threshold_scale'],476,p)%p
  need(lc==expected,'certificate diagonal coefficient mismatch')
  primary=lc*pow(pow(ld,16,p),-1,p)%p
  expected_primary=pow(2,507,p)*pow(fixed['base_scale'],2835574,p)*pow(fixed['threshold_scale'],348,p)%p
  need(primary==expected_primary,'primary diagonal coefficient mismatch')
  degree_checks.append({'domain':domain,'modulus':p,'certificate_degree':dc,'D_degree':dd,'primary_degree':dc-16*dd,'nonzero_certificate_leader':lc})
  for _ in range(40):
   vals={n:rng.randrange(1 if domain=='positive' else 0,35) for n in base['variables']}
   f,named=evaluate(base,vals,fixed,p);g,namedc=evaluate(cert,vals,fixed,p)
   need(g==pow(named['D'],16,p)*f%p,'D16 multiplier mismatch')
   count+=1
 fixed=fixed_values(base,4)
 for k in range(20):
  vals={n:rng.randrange(1 if domain=='positive' else 0,35) for n in base['variables']}
  _,named=evaluate(base,vals,fixed,4)
  need(named['R']%2==1 and named['K']%2==0,'parity normalization')
  need(named['a0']==1 and named['a1']==0,'radicand congruence')
receipt={'status':'PASS','circuit_comparisons':count,'congruence_fixtures':40,'certificate_multiplier':'D^16','independent_exact_degree_checks':degree_checks,'scope':'Finite implementation checks and modular nonzero-leading-coefficient degree proof; ring identities and universal inequalities are separately proved.'}
(ROOT/'CIRCUIT_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
