#!/usr/bin/env python3
"""Independent degree-leading-residue and live-gate audit. Imports no builder."""
from pathlib import Path
import collections,gzip,json,math
ROOT=Path(__file__).resolve().parents[2]/'nine'
ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients/old_tuple'/n).read_bytes()),'little') for n in ['beta.bin.gz','K.bin.gz','MC.bin.gz','MF_source.bin.gz']]
results=[]
for order in [-1,0,1,2,3,4]:
 for domain in ['positive','natural']:
  stem=f'split_108_order{order}_{domain}'
  body=json.loads((ROOT/'generated'/f'{stem}.json').read_text())
  cert=json.loads((ROOT/'generated'/f'{stem}_certificate.json').read_text())
  claim=json.loads((ROOT/'generated'/f'{stem}_certificate_degree.json').read_text())
  def live_counts(data):
   seen=set();todo=[data['output']]
   while todo:
    j=todo.pop()
    if j in seen:continue
    seen.add(j);n=data['nodes'][j]
    if n['kind'] in ['add','sub','mul']:
     if not (0<=n['left']<j and 0<=n['right']<j):raise ValueError('DAG')
     todo.extend([n['left'],n['right']])
   return dict(collections.Counter(data['nodes'][j]['kind'] for j in seen if data['nodes'][j]['kind'] in ['add','sub','mul']))
  counts=live_counts(body)
  if counts!=body['operation_counts'] or sum(counts.values())!=body['total_operations']:raise ValueError('live counts')
  residues=[]
  for prime in [1000003,1000033,1000000007]:
   constants={r['name']:sum(t['coefficient']*math.prod(pow(p,e,prime) for p,e in zip(ports,t['powers'])) for t in r['terms'])%prime for r in cert['coefficient_recipes']}
   constants['base_scale']=pow(2,cert['base_scale_exponent'],prime);constants['threshold_scale']=pow(2,cert['threshold_scale_exponent'],prime)
   dl=[]
   for n in cert['nodes']:
    kind=n['kind']
    if kind=='variable':d,c=1,1
    elif kind=='literal':d,c=0,n['value']%prime
    elif kind=='fixed':d,c=0,constants[n['name']]
    else:
     (d1,c1),(d2,c2)=dl[n['left']],dl[n['right']]
     if kind=='mul':d,c=d1+d2,c1*c2%prime
     else:
      d=max(d1,d2);c=((c1 if d1==d else 0)+(1 if kind=='add' else -1)*(c2 if d2==d else 0))%prime
    dl.append((d,c))
   degree,leader=dl[cert['output']];dd=dl[cert['named_nodes']['D']][0]
   if leader==0:raise ValueError('upper bound not attained')
   exact=degree-16*dd
   if exact!=claim['exact_degree']:raise ValueError('degree mismatch')
   residues.append({'prime':prime,'certificate_leader':leader,'certificate_degree':degree,'D_degree':dd,'primary_degree':exact})
  results.append({'order':order,'domain':domain,'operations':sum(counts.values()),'degree':exact,'independent_residue_certificates':residues})
print(json.dumps({'status':'PASS','scope':'Independent live DAG counts and certificate degree upper bounds with nonzero diagonal leaders for actual payload tuple, modulo three primes. Algebraic certificate equality reviewed separately.','results':results},indent=2))
