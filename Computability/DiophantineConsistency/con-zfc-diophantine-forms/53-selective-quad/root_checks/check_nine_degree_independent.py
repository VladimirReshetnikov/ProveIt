#!/usr/bin/env python3
"""Independent attained-degree audit, reading delivered DAGs only; no builder imports."""
from pathlib import Path
from functools import reduce
from math import isqrt
import gzip,hashlib,json
ROOT=Path(__file__).resolve().parents[1];R=ROOT/'nine'
def req(c,m):
 if not c:raise RuntimeError(m)
ports=[int.from_bytes(gzip.decompress((R/'coefficients'/(s+'.bin.gz')).read_bytes()),'little') for s in ['beta','K','MC','MF_source']]
results={}
for label in ['calibrated_natural','calibrated_positive']:
 body=json.loads((R/'generated'/(label+'_certificate.json')).read_text());plain=json.loads((R/'generated'/(label+'.json')).read_text())
 certificates=[]
 for p in [101,1009,1000003]:
  req(all(p%d for d in range(2,isqrt(p)+1)),'prime')
  fv={r['name']:sum(t['coefficient']*reduce(lambda a,b:a*b,(pow(v,e,p) for v,e in zip(ports,t['powers'])),1) for t in r['terms'])%p for r in body['coefficient_recipes']}
  fv['base_scale']=pow(2,body['base_scale_exponent'],p);fv['threshold_scale']=pow(2,body['threshold_scale_exponent'],p)
  ds=[];ls=[]
  for i,n in enumerate(body['nodes']):
   k=n['kind']
   if k=='variable':d,l=1,1
   elif k=='literal':d,l=0,n['value']%p
   elif k=='fixed':d,l=0,fv[n['name']]
   else:
    a,b=n['left'],n['right'];req(a<i and b<i,'topological order')
    if k=='mul':d,l=ds[a]+ds[b],ls[a]*ls[b]%p
    else:
     req(k in ['add','sub'],'gate kind');d=max(ds[a],ds[b]);l=((ls[a] if ds[a]==d else 0)+(1 if k=='add' else -1)*(ls[b] if ds[b]==d else 0))%p
   ds.append(d);ls.append(l)
  i=body['output'];req(ds[i]==7344328 and ls[i]!=0,'attained exact degree')
  closed=pow(2,598,p)*pow(fv['base_scale'],3671828,p)*pow(fv['threshold_scale'],448,p)%p
  req(closed==ls[i],'claimed exact leader')
  certificates.append({'prime':p,'leading_coefficient':ls[i],'matches_2^598_a^3671828_c^448':True})
 counts={k:sum(n['kind']==k for n in plain['nodes']) for k in ['add','sub','mul']}
 req(counts==plain['operation_counts'],'operation ledger')
 results[label]={'exact_certificate_degree':ds[body['output']],'primary_operations':sum(counts.values()),'certificates':certificates,
  'primary_sha256':hashlib.sha256((R/'generated'/(label+'.json')).read_bytes()).hexdigest(),'certificate_sha256':hashlib.sha256((R/'generated'/(label+'_certificate.json')).read_bytes()).hexdigest()}
result={'status':'PASS','results':results,'limit':'The degree audit applies directly to the certificate DAG. Its equality to the primary DAG relies on the explicit deltaV and inner-expression polynomial identities reviewed in NINE_INDEPENDENT_REVIEW.md.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
