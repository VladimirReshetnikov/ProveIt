from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta85-single-gate-exact-search')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
G=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());rows=G['source']
assert len(rows)==85 and len(G['witnesses'])==13 and len(G['fixed_numerals'])==4
consumer=defaultdict(set)
for n,op,a,b in rows:
 for x in (a,b):
  if isinstance(x,str):consumer[x].add(n)
# Each signature coordinate is one explicit finite-field evaluation.
p=1000003;rng=random.Random(1901);inputs=G['witnesses']+G['fixed_numerals'];width=8
vals={x:[rng.randrange(1,p) for _ in range(width)] for x in inputs}
vals.update({str(i):[i]*width for i in range(5)})
def sig(op,x,y):return tuple(((a+b if op=='+' else a-b if op=='-' else a*b)%p) for a,b in zip(x,y))
found=[];tested=0;targetpairs=0;available=list(vals);produced=set()
for n,op,a,b in rows:
 def key(x):return str(x) if isinstance(x,int) else x
 aa,bb=key(a),key(b);target=sig(op,vals[aa],vals[bb]);dead={x for x in (aa,bb) if x in produced and consumer[x]=={n}}
 for d in sorted(dead):
  targetpairs+=1
  for x in available:
   if x==d:continue
   for y in available:
    if y==d:continue
    for oper in '+-*':
     tested+=1
     if sig(oper,vals[x],vals[y])==target:found.append([n,d,oper,x,y])
 vals[n]=target;available.append(n);produced.add(n)
assert targetpairs==60 and tested==1099002 and not found
print(json.dumps({'parent_rows':85,'exclusive_predecessor_target_pairs':targetpairs,'single_gate_replacement_expressions_refuted':tested,'modulus':p,'explicit_modular_assignments':width,'surviving_candidates':found,'scope':'one current gate replaced by one earlier-wire operation, delete one exclusive direct predecessor; polynomial identity at arbitrary ports; constants 0..4', 'global_minimality_or_zero_equivalence':False,'lean_executed':False},sort_keys=True,indent=2))
