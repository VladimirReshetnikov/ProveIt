#!/usr/bin/env python3
"""Independent univariate-polynomial certificate for finite local class."""
from pathlib import Path
from collections import defaultdict
import ast,gzip,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural79-local-gate-obstruction'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
pin(P/'check.py','a940ea30ab37f32daeb8dd223322f2ed20edd145720a1c8effb566229eab2a2a')
obs=json.loads(pin(P/'result.json','fa68592bf54ee48d10db03b723e52692c3d7f5768bd0ca6ef9a2a911984b8eb1'))
g=json.loads(pin(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
s=pin(D/'research/ordinary14-natural79-corrected-reflection-overlay/source/P79NaturalForcedW.lean.src','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36').decode()
part=s.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('-- END LITERAL GRAPH',1)[0]
program=ast.parse('\n'.join(l.strip()[4:].replace(':=','=') for l in part.splitlines() if l.strip()))
ops={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}
def atom(x):
 if isinstance(x,ast.Name):return x.id
 assert isinstance(x,ast.Constant) and type(x.value)==int and x.value>=0;return x.value
rows=[]
for node in program.body:
 assert isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and isinstance(node.value,ast.BinOp) and type(node.value.op) in ops
 rows.append([node.targets[0].id,ops[type(node.value.op)],atom(node.value.left),atom(node.value.right)])
assert len(rows)==79 and rows==g['source'] and g['output']=='out'
for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 14) := .var {i}' in s
for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in s
assert '⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in s
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=json.loads(pin(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
m=2**61-1;env={}
for n in g['fixed_numerals']:
 x=bind['ports'][n]; assert x['sha256_raw']==b115['ports'][n]['sha256_raw'] and x['sha256_gzip']==b115['ports'][n]['sha256_gzip']
 raw=gzip.decompress(pin(p72/x['path'],x['sha256_gzip']));assert len(raw)==x['raw_bytes'] and sha(raw)==x['sha256_raw']==obs['port_raw_sha256'][n]
 env[n]=int.from_bytes(raw,'little')%m
w={n:7919*i*i+1234567*i+13579 for i,n in enumerate(g['witnesses'],1)}
assert w==obs['natural_witness'] and all(v>=0 for v in w.values());env.update(w)
def value(x):return x % m if isinstance(x,int) else env[x]
def f(a,o,b):return ((a+b) if o=='+' else (a-b) if o=='-' else (a*b))%m
for n,o,a,b in rows:env[n]=f(value(a),o,value(b))
target=env['out'];assert target==obs['original_output_residue']==2118908950514353078
consumers=defaultdict(set);gates={r[0] for r in rows}
for name,_,a,b in rows:
 for child in (a,b):
  if child in gates:consumers[child].add(name)
# Independently represent every downstream value as a polynomial in X,
# where X is the substituted parent gate. All coefficient operations are
# modulo the given modulus; this is exact over Z/mZ (no primality needed).
def combine(a,o,b):
 if o=='*':
  r=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):r[i+j]=(r[i+j]+x*y)%m
 else:
  r=[0]*max(len(a),len(b));sgn=1 if o=='+' else -1
  for i in range(len(r)):r[i]=((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%m
 while len(r)>1 and r[-1]==0:r.pop()
 return r
seen=list(range(-4,5))+g['witnesses']+g['fixed_numerals'];pairs=[];count=0;survivors=0;poly_count=0;maxdegree=0;distinct_checks=0
for idx,(name,oldop,left,right) in enumerate(rows):
 eligible=sorted({n for n in (left,right) if isinstance(n,str) and n in gates and consumers[n]=={name}})
 if eligible:
  poly={name:[0,1]}
  def get(x):return poly.get(x,[value(x)]) if isinstance(x,str) else [x%m]
  for n,o,a,b in rows[idx+1:]:poly[n]=combine(get(a),o,get(b))
  coeff=poly['out'];poly_count+=1;maxdegree=max(maxdegree,len(coeff)-1)
  # Substituting the recorded original parent must reproduce the original.
  def ev(x):
   acc=0
   for c in reversed(coeff):acc=(acc*x+c)%m
   return acc
  assert ev(env[name])==target
  parent_cache={}
  for child in eligible:
   pairs.append((name,child));pool=[v for v in seen if v!=child]
   for a in pool:
    x=value(a)
    for b in pool:
     y=value(b)
     for o in ('+','-','*'):
      count+=1;z=f(x,o,y)
      if z not in parent_cache:parent_cache[z]=ev(z);distinct_checks+=1
      if parent_cache[z]==target:survivors+=1
 seen.append(name)
assert len(pairs)==obs['eligible_parent_child_pairs']==55 and count==obs['candidate_tuples']==1084128 and survivors==obs['equal_output_modulus_survivors']==0
print(json.dumps({'scope':'independent exact modular output-polynomial exclusion for stated finite class only; not zero-set equivalence or minimality',
 'source_rows':len(rows),'eligible_parent_child_pairs':len(pairs),'candidate_tuples':count,'counterexample_input':w,'original_output_residue':target,
 'univariate_parent_polynomials':poly_count,'maximum_univariate_degree':maxdegree,'distinct_parent_values_tested':distinct_checks,'equal_output_survivors':survivors},indent=2,sort_keys=True))
