#!/usr/bin/env python3
"""Independent upper-degree and actual diagonal leading-coefficient audit.
Read only literal JSON circuits and signed coefficient payloads; never import producers.
"""
import argparse,json,gzip,hashlib
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('circuit',type=Path);ap.add_argument('--fixed',type=Path);a=ap.parse_args()
p=a.circuit;obj=json.loads(p.read_text());nodes=obj['nodes'];root=obj['output']
fpath=a.fixed or p.with_name('FIXED_COEFFICIENTS.json');binding=json.loads(fpath.read_text());fixed={}
for name,entry in binding.items():
 data=(fpath.parent/entry['file']).read_bytes();raw=gzip.decompress(data)
 assert hashlib.sha256(data).hexdigest()==entry['gzip_sha256']
 assert hashlib.sha256(raw).hexdigest()==entry['raw_sha256']
 assert raw[0] in (0,1)
 value=int.from_bytes(raw[1:],'little')*(-1 if raw[0] else 1)
 assert abs(value).bit_length()==entry['bit_length'];fixed[name]=value
reachable=set();work=[root]
while work:
 i=work.pop()
 if i in reachable:continue
 reachable.add(i);node=nodes[i]
 if node['kind'] in ('add','sub','mul'):work.extend([node['left'],node['right']])
deg=[]
for i,n in enumerate(nodes):
 k=n['kind']
 if k=='variable':d=1
 elif k in ('literal','fixed'):d=0
 else:
  l,r=n['left'],n['right'];assert 0<=l<i and 0<=r<i
  d=deg[l]+deg[r] if k=='mul' else max(deg[l],deg[r])
 deg.append(d)
primes=[1000000007,1000000009,998244353];witnesses={}
for prime in primes:
 coeff=[]
 for i,n in enumerate(nodes):
  k=n['kind']
  if k=='variable':v=1
  elif k=='literal':v=int(n['value'])%prime
  elif k=='fixed':v=fixed[n['name']]%prime
  else:
   l,r=n['left'],n['right']
   if k=='mul':v=coeff[l]*coeff[r]%prime
   else:
    vl=coeff[l] if deg[l]==deg[i] else 0
    vr=coeff[r] if deg[r]==deg[i] else 0
    v=(vl+vr if k=='add' else vl-vr)%prime
  coeff.append(v)
 assert coeff[root]!=0,(prime,deg[root]);witnesses[str(prime)]=coeff[root]
operations=sum(nodes[i]['kind'] in ('add','sub','mul') for i in reachable)
assert operations==obj['total_operations'];assert deg[root]==obj['degree_upper_bound']
result={'circuit':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'variables':obj['variables'],'operations':operations,'degree_exact':deg[root],'actual_diagonal_leading_coefficients':witnesses,'fixed_payloads_verified':len(fixed),'status':'PASS'}
out=Path(__file__).with_name(p.stem+'_DEGREE_AUDIT.json');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
