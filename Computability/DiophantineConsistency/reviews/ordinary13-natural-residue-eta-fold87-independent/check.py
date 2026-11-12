#!/usr/bin/env python3
"""Independent exact local ring rewrite and inherited graph check, no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
p=json.loads(pin('research/ordinary13-natural-residue-forced88-degree60/candidate.json','cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2'))
c=json.loads(pin('research/ordinary13-natural-residue-eta-fold87-degree60/candidate.json','81a09c0504bc786afb017483225e1fb6b1a52e9ddd98f53b0643dfb23c3a602f'))
pin('research/ordinary13-natural-residue-eta-fold87-degree60/receipt.json','dd6c12c27c974ef90a626cf0f0280d81426b67150c919b01c4dfb9111656ff96')
pin('reviews/ordinary13-natural-residue-forced88-independent/result.json','6f962c799f48c9de0cc7bc4bbb1949abb7b8265ca29eb3604046f0dc337f116e')
assert p['domain']==c['domain']=='nonnegative integers' and p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals'] and p['output']==c['output']
pr={r[0]:r for r in p['source']};cr={r[0]:r for r in c['source']}
assert set(pr)-set(cr)=={'shift_zeta','g52'} and set(cr)-set(pr)=={'kbase'}
assert [n for n in pr.keys() & cr.keys() if pr[n]!=cr[n]] in (['k','r0'],['r0','k'])
assert pr['shift_zeta']==['shift_zeta','+','n_zeta',1]
assert pr['k']==['k','+','shift_eta','shift_zeta'] and pr['g52']==['g52','-','k','R'] and pr['r0']==['r0','-','g52',1]
assert cr['kbase']==['kbase','+','shift_eta','n_zeta'] and cr['k']==['k','+','kbase',1] and cr['r0']==['r0','-','kbase','R']
assert [n for n,o,a,b in p['source'] if 'shift_zeta' in (a,b)]==['k'] and [n for n,o,a,b in p['source'] if 'g52' in (a,b)]==['r0']
# k_old=eta+(zeta+1)=kbase+1 and r0_old=k_old-R-1=kbase-R,
# by associativity and additive inverse in any commutative ring. Every other
# gate has the same operands, so induction over this topology proves equality.
known=set(c['witnesses']+c['fixed_numerals']);deps={}
for n,o,a,b in c['source']:
 assert n not in known and o in '+-*' and all(type(x) is int or x in known for x in (a,b))
 known.add(n);deps[n]=(a,b)
live={c['output']};stack=[c['output']]
while stack:
 for arg in deps.get(stack.pop(),()):
  if isinstance(arg,str) and arg not in live:live.add(arg);stack.append(arg)
assert set(deps)|set(c['witnesses'])|set(c['fixed_numerals'])<=live
assert len(c['source'])==87 and len(p['source'])==87+1
print(json.dumps({'scope':'exact all-ring local fold and unchanged downstream DAG; inherited compact-port degree, no Lean','operations':87,'degree_inherited':60,'identical_output_all_ports_and_inputs':True,'liveness_checked':True,'lean_elaborated':False},sort_keys=True,indent=2))
