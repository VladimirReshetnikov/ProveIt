from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta-zeta85-single-gate-search-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-eta-zeta85-single-gate-exact-search')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());rows=g['source'];inputs=g['witnesses']+g['fixed_numerals'];assert len(rows)==85 and len(inputs)==17
cons=defaultdict(set)
for n,op,a,b in rows:
 for x in (a,b):
  if isinstance(x,str):cons[x].add(n)
# Independent assignments derive from a second deterministic SHA256 domain;
# zero is allowed, and integer representatives make every mismatch explicit.
mod=1000003;width=8
vals={name:tuple(int.from_bytes(sha256(('second-review:'+name+':'+str(i)).encode()).digest()[:8],'big')%mod for i in range(width)) for name in inputs}
for k in range(5):vals['#'+str(k)]=(k,)*width
available=list(vals);produced=set();pairs=[];tests=0;survivors=[]
for ix,(n,op,a,b) in enumerate(rows):
 def wire(x):return '#'+str(x) if isinstance(x,int) else x
 def apply(op,x,y):return (x+y if op=='+' else x-y if op=='-' else x*y)%mod
 x,y=vals[wire(a)],vals[wire(b)];target=tuple(apply(op,x[i],y[i]) for i in range(width))
 dead={wire(v) for v in (a,b) if isinstance(v,str) and v in produced and cons[v]=={n}}
 for d in sorted(dead):
  options=[z for z in available if z!=d]
  assert len(options)==21+ix
  pairs.append((ix,n,d,len(options)))
  tests+=3*len(options)**2
  for aa in options:
   for bb in options:
    va,vb=vals[aa],vals[bb]
    for kind in '+-*':
     if all(apply(kind,va[i],vb[i])==target[i] for i in range(width)):
      survivors.append((n,d,kind,aa,bb))
 vals[n]=target;available.append(n);produced.add(n)
assert len(pairs)==60 and tests==1099002 and not survivors
assert sum(3*(21+ix)**2 for ix,_,_,_ in pairs)==tests
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'independent_assignment_method':'SHA256 domain-separated input representatives',
 'modulus':mod,'assignments':width,'exclusive_predecessor_pairs':len(pairs),
 'replacement_expressions':tests,'survivors':len(survivors),
 'scope':'One-gate arbitrary-port polynomial identity only; compact specialization, zero-set equivalence and global minimality not checked.',
 'lean_executed':False},sort_keys=True,indent=2))
