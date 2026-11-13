from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize
D=Path('reviews/current2011-shear-degree25-syzygy-independent');A=Path('research/current2011-shear-degree25-syzygy')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],stdout=subprocess.PIPE,check=True,timeout=30).stdout==(A/'result.json').read_bytes()
g=json.loads(Path('research/current2011-sheared72-46-candidate/polynomial.json').read_text());names=g['witnesses']+g['fixed_numerals'];n=len(names);zero=(0,)*n
atoms={name:{tuple(int(i==j) for i in range(n)):1} for j,name in enumerate(names)}
rows={row[0]:row[1:] for row in g['source']}; cache={};maxsupport=0

def plus(a,b,s=1):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,0)+s*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 global maxsupport
 if len(a)*len(b)>2_000_000:raise RuntimeError('product guard')
 d=defaultdict(int)
 for x,v in a.items():
  for y,w in b.items():d[tuple(i+j for i,j in zip(x,y))]+=v*w
 if len(d)>100_000:raise RuntimeError('support guard')
 x={k:v for k,v in d.items() if v};maxsupport=max(maxsupport,len(x));return x
def evalnode(k):
 if isinstance(k,int):return {zero:k} if k else {}
 if k in atoms:return atoms[k]
 if k in cache:return cache[k]
 op,a,b=rows[k];a=evalnode(a);b=evalnode(b)
 x=mul(a,b) if op=='*' else plus(a,b,1 if op=='+' else -1);cache[k]=x;return x
def degree(mon):return sum(mon[:14])
def top(poly):
 d=max(map(degree,poly));return d,{m:c for m,c in poly.items() if degree(m)==d}
def powp(p,n):
 x={zero:1}
 for _ in range(n):x=mul(x,p)
 return x
def scale(p,n):return {m:c*n for m,c in p.items() if c*n}
first=scale(mul(atoms['gamma'],mul(evalnode('Nt'),plus(evalnode('N0'),{zero:1},-1))),8)
second=mul(evalnode('kY'),evalnode('rQW'))
assert top(first)[0]==top(second)[0]==25
S=plus(first,second);deg,leader=top(S);assert deg==23 and len(leader)==28
published=json.loads((A/'result.json').read_text());actual={}
for term in published['leader']:
 mon=tuple(term['powers'].get(name,0) for name in names)
 assert mon not in actual
 actual[mon]=term['coefficient']
assert actual==leader and published['syzygy_degree']==23 and published['discarded_ceiling']==21
I=names.index('i');G=names.index('gamma');projected={m:c for m,c in leader.items() if m[I]==0 and m[G]==0}
E=top(evalnode('E'))[1];Y=top(evalnode('Y'))[1];k=top(evalnode('k'))[1];W=top(evalnode('Nt'))[1]
expected=scale(mul(mul(mul(E,powp(k,3)),powp(Y,3)),W),-4);assert projected==expected and len(projected)==16
# Exact specialization to eta=k, zeta=i=gamma=0 and every other symbol 1.
# This is an evaluation homomorphism into Z[k], not a positive-witness claim.
eta=names.index('eta');zeroed=[names.index(x) for x in ['zeta','i','gamma']]
def specialize(poly):
 out=defaultdict(int)
 for mon,c in poly.items():
  if not any(mon[j] for j in zeroed):out[mon[eta]]+=c
 return {i:c for i,c in out.items() if c}
assert specialize(top(evalnode('Na'))[1])=={1:-2}
assert specialize(top(evalnode('N0'))[1])=={2:-1}
assert specialize(top(evalnode('strong_residual'))[1])=={}
assert specialize(top(evalnode('rQW'))[1])=={}
assert specialize(leader)=={3:8}
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'author_receipt_reproduced':True,'method':'independent exact full-polynomial expansion with no discarded terms','summand_degree':25,'sum_degree':deg,'full_sum_terms':len(S),'leader_terms_checked':len(leader),'projected_leader_terms':len(projected),'maximum_intermediate_support':maxsupport,'lean_executed':False},sort_keys=True,indent=2))
