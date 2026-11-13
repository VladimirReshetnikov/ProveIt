#!/usr/bin/env python3
"""Independent exact local ring rewrite and inherited graph check, no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
p=json.loads(pin('research/ordinary13-natural-residue-forced89-degree56/candidate.json','c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a'))
c=json.loads(pin('research/ordinary13-natural-residue-eta-fold88-degree56/candidate.json','f71cb18bdc28088a7a7c7c7ae84afc15e49470ee3d4fa4076d8c25d6d2b89b58'))
pin('research/ordinary13-natural-residue-eta-fold88-degree56/receipt.json','a9fc05755b636a5e3ba1d37973b4091998e3bae8346932b940b4deea29cbc2ca')
pin('reviews/ordinary13-natural-residue-forced89-independent/result.json','17b5fcebce8f734b68124b7ecfa477fec1f00ac73cadda915c29128fc27b1df8')
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
assert len(c['source'])==88 and len(p['source'])==88+1
print(json.dumps({'scope':'exact all-ring local fold and unchanged downstream DAG; inherited compact-port degree, no Lean','operations':88,'degree_inherited':56,'identical_output_all_ports_and_inputs':True,'liveness_checked':True,'lean_elaborated':False},sort_keys=True,indent=2))
