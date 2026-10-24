"""Independent complete source+finalizer checks, actual numerals, exact degree.
Imports the separately written direct formula, but no builder or circuit helper.
"""
from pathlib import Path
import json,gzip,hashlib,random,math
from independent_formula import evaluate
R=Path(__file__).resolve().parent;body=json.loads((R/'integer10.json').read_text());nodes=body['nodes'];names=body['named_nodes'];manifest=json.loads((R/'FIXED_COEFFICIENTS.json').read_text())
fixed={}
for name,info in manifest.items():
 packed=(R/info['file']).read_bytes();raw=gzip.decompress(packed)
 if hashlib.sha256(packed).hexdigest()!=info['gzip_sha256'] or hashlib.sha256(raw).hexdigest()!=info['raw_sha256']:raise RuntimeError('fixed coefficient hash mismatch')
 if raw[0] not in (0,1):raise RuntimeError('sign encoding')
 fixed[name]=(-1 if raw[0] else 1)*int.from_bytes(raw[1:],'little')
ports=[int.from_bytes(gzip.decompress((R/'data'/f'{name}.bin.gz').read_bytes()),'little')for name in ['beta','K','MC','MF_source']]
for name,rows in body['fixed_recipes'].items():
 expect=sum(row['coefficient']*math.prod(v**e for v,e in zip(ports,row['powers']))for row in rows)
 if fixed[name]!=expect:raise RuntimeError('fixed recipe mismatch')
if fixed['radix']!=2**2134940 or fixed['threshold']!=2**34159017:raise RuntimeError('fixed scale mismatch')
code=json.loads((R/'data/code.json').read_text());kernel=json.loads((R/'data/kernels.json').read_text())
def circuit(inputs,p):
 env=dict(zip(body['variables'],inputs));vals=[]
 for n in nodes:
  k=n['kind']
  if k=='variable':v=env[n['name']]
  elif k=='literal':v=n['value']
  elif k=='fixed':v=fixed[n['name']]
  else:
   x,y=vals[n['left']],vals[n['right']];v=x+y if k=='add' else x-y if k=='sub' else x*y
  vals.append(v%p)
 return vals
primes=[1000003,1000033,1000037];rng=random.Random(202610231873);cases=0
for p in primes:
 for trial in range(100):
  inputs=[rng.randrange(-25,26)for _ in body['variables']]
  actual=circuit(inputs,p);expected,env=evaluate(inputs,p,[v%p for v in ports],code,kernel)
  if actual[body['output']]!=expected:raise RuntimeError(('complete equation mismatch',p,trial))
  for name,value in env.items():
   if name in names and actual[names[name]]!=value:raise RuntimeError(('register mismatch',p,trial,name))
  cases+=1
# Every source prefix and literal finalizer congruence is checked also mod3.
mod3cases=0
for _ in range(1000):
 vals=circuit([rng.randrange(-100,101)for _ in body['variables']],3)
 if vals[names['A']] or vals[names['D']] or vals[names['lucas']] or vals[names['guard']]!=1:raise RuntimeError('unconditional residue separation')
 mod3cases+=1
# Exact total-degree upper bound and actual diagonal top coefficients.
deg=[]
for n in nodes:
 k=n['kind'];deg.append(1 if k=='variable' else 0 if k in ('fixed','literal') else deg[n['left']]+deg[n['right']] if k=='mul' else max(deg[n['left']],deg[n['right']]))
leaders={}
for p in primes:
 lead=[]
 for i,n in enumerate(nodes):
  k=n['kind']
  if k=='variable':v=1
  elif k=='literal':v=n['value']
  elif k=='fixed':v=fixed[n['name']]
  elif k=='mul':v=lead[n['left']]*lead[n['right']]
  else:
   x,y=n['left'],n['right'];a=lead[x]if deg[x]==deg[i] else 0;b=lead[y]if deg[y]==deg[i] else 0;v=a+b if k=='add' else a-b
  lead.append(v%p)
 leaders[str(p)]=lead[body['output']]
 if not lead[body['output']]:raise RuntimeError('zero leading certificate')
if deg[body['output']]!=1576864 or deg[names['A']]!=16424:raise RuntimeError('degree mismatch')
seen=set()
def visit(i):
 if i in seen:return
 seen.add(i);n=nodes[i]
 if n['kind'] in ('mul','sub','add'):
  if n['left']>=i or n['right']>=i:raise RuntimeError('nontopological circuit')
  visit(n['left']);visit(n['right'])
visit(body['output'])
if len(seen)!=len(nodes):raise RuntimeError('dead circuit nodes')
ops=sum(n['kind'] in ('add','sub','mul')for n in nodes)
if ops!=481 or ops!=body['total_operations']:raise RuntimeError('operation count')
# New paired recurrence, including negative A and exceptional-rank divisibility.
recurrence_cases=0
for A in range(-40,41):
 if not A:continue
 us=[0,1]
 for n in range(2,83):us.append(A*us[-1]-us[-2])
 for j in range(1,40):
  if (us[2*j]-(-1)**(j-1)*j*A)%(A*A) or (us[2*j+1]-(-1)**j)%(A*A):raise RuntimeError('paired recurrence')
  if us[2*j]%(A*A)==0 and j%A:raise RuntimeError('exceptional rank')
  recurrence_cases+=1
receipt={'status':'PASS','domain':'ten unrestricted integers','exact_degree':deg[body['output']],'degree_A':deg[names['A']],'live_binary_operations':ops,'leading_coefficients_mod_primes':leaders,'complete_equation_modular_cases':cases,'unconditional_mod3_cases':mod3cases,'paired_recurrence_cases':recurrence_cases,'fixed_leaf_count':len(manifest),'materialized_fixed_compressed_bytes':sum((R/info['file']).stat().st_size for info in manifest.values()),'literal_polynomial_sha256':hashlib.sha256((R/'integer10.json').read_bytes()).hexdigest(),'proof_boundary':'Finite checks audit equation transcription, actual fixed numerals, topology, new congruences, and exact degree; full equivalence is the mathematical theorem in section.tex with its identified dependencies.'}
(R/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
