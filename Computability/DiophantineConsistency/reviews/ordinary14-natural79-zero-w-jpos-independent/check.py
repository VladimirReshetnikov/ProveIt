#!/usr/bin/env python3
"""Independently check exact zero-J, zero-w guard cut and source assumptions."""
from pathlib import Path
from functools import lru_cache
import hashlib,json
D=Path(__file__).resolve().parents[2]
def pin(path,digest):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b.decode()
s=pin('research/ordinary14-natural79-zero-w-jpos-draft/Natural79ZeroWJPos.lean','f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a')
c=pin('research/ordinary14-natural79-factor-residues-draft/Natural79ConcreteUnits.lean','253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d')
g=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
model=pin('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')
assert 'theorem ι_nonneg' in model
assert 'theorem eval_one_of_pair_unit' in s and 'theorem guard_zero_cut' in s and 'theorem J_pos_of_zero_w_zero' in s
assert 'units.2.2.2.1' in s
start=c.index('theorem units_of_zero_w_zero');end=c.index(' := by',start);sig=c[start:end]
fields=['.first v).1=', '.main v).1=', '.aux v).1=', '.guardFactor v).1=', '.strong v).1=']
assert all(f in sig for f in fields) and [sig.index(f) for f in fields]==sorted(sig.index(f) for f in fields)
start=s.index('theorem J_pos_of_zero_w_zero'); end=s.index(' := by',start);sig=s[start:end]
assert '(hK : (p 1 : DiffRing V)=ι K)' in sig and '(hw : v 6=0)' in sig and '0 < v 0' in sig
assert not any(x in sig for x in ('(hbeta','(hb :','(hKpos','(hgamma','(hMC','(hMF'))
assert '(hz : InternalZero' in sig and 'Natural79ConcreteUnitsDraft.units_of_zero_w_zero p v hz hw' in s
# Compute the guard's entire dependency cone symbolically with n_J=n_w=0.
rows={n:(op,x,y) for n,op,x,y in g['source']}; assert len(rows)==79
def const(n):return {} if n==0 else {():n}
def var(n):return {(n,):1}
def add(a,b):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 out={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(sorted(x+y));out[k]=out.get(k,0)+u*v
 return {k:v for k,v in out.items() if v}
@lru_cache(None)
def ev(t):
 if type(t) is int:return const(t)
 if t in ('n_J','n_w'):return const(0)
 if t not in rows:return var(t)
 op,x,y=rows[t];x=ev(x);y=ev(y)
 return add(x,y) if op=='+' else add(x,neg(y)) if op=='-' else mul(x,y)
F,alpha,K=map(var,('n_F','n_alpha','K0'))
expected=add(neg(mul(add(add(F,alpha),const(1)),K)),neg(F))
assert ev('guard')==expected
for f in range(7):
 for a in range(7):
  for k in range(7):assert -(f+a+1)*k-f<=0
assert -(0+0+1)*0-0==0
for n in ('guard_zero_cut','J_pos_of_zero_w_zero'):assert '#print axioms DiophantineConsistency.Natural79ZeroWJPosDraft.'+n in s
print(json.dumps({'scope':'source assumptions and exact arbitrary-port sparse-polynomial cut; no Lean or iPRA proof','pinned_files':4,'symbolic_J_w_zero_guard_identity':True,'nonnegative_controls':343,'K0_zero_F_zero_boundary':0,'axiom_reports_unexecuted':2},sort_keys=True,indent=2))
