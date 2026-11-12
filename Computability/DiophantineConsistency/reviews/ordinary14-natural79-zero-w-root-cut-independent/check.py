#!/usr/bin/env python3
"""Bounded exact DAG root and source-assumption inspection; no Lean."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary14-natural79-zero-w-root-cut-draft/Natural79ZeroWRootCut.lean','c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec')
n=pin('research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009')
r=pin('research/ordinary14-natural79-w-model-route/ForcedWDivisibility.lean','111f5a6da543baf6f08b3b1c6e5e8371cfb222197ba4566b8693598edffb6833')
a=pin('research/ordinary14-natural79-factor-residues-draft/Natural79ResidueShapes.lean','b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38')
g=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
# The complete DAG is represented as immutable trees; compare the exact root shape.
e={x:('input',x) for x in g['witnesses']};e.update({x:('port',x) for x in g['fixed_numerals']})
def val(x):return ('num',x) if type(x) is int else e[x]
for key,op,x,y in g['source']:e[key]=(op,val(x),val(y))
N=lambda x:('num',x); A=lambda x,y:('+',x,y); S=lambda x,y:('-',x,y); M=lambda x,y:('*',x,y)
q=A(N(1),M(e['n_J'],e['beta']));X=M(q,e['n_w']);shift=S(M(e['U'],e['n_gamma']),S(A(A(e['n_eta'],N(1)),e['n_zeta']),e['R']))
assert e['X']==X and e['shift']==shift
assert e['Dstar']==A(M(e['U'],A(X,M(e['a'],e['c']))),M(A(N(3),M(N(4),e['a'])),shift))
assert e['a']==A(M(X,e['Y']),e['Y'])
for name in ('root_expr_shape','root_eval_zero_w','represented_root_zero_w','divisor_of_root_cut','signed_dvd_three_square_of_zero_w_zero'):assert 'theorem '+name in s
start=s.index('theorem signed_dvd_three_square_of_zero_w_zero');stop=s.index(' := by',start);sig=s[start:stop]
for t in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hb : 0<beta)','(hJ : 0<v 0)','(hz : InternalZero','(hw : v 6=0)'):assert t in sig
assert not any(t in sig for t in ('(hK','(hMC','(hMF','(hgamma','(hDpos'))
for t in ('signed_quotient_of_zero_w_zero p beta v hbeta hb hJ hz hw','divisor_of_main_norm H U d Y C hd hn','divisor_of_three_square H U Q Y rfl hU hHU'):assert t in s
assert 'theorem signed_quotient_of_zero_w_zero' in n and 'theorem atoms_at_zero_w' in n
assert 'theorem divisor_of_main_norm' in r and 'theorem divisor_of_three_square' in r and 'theorem main_shape' in a
# General ring witness: (D=U*a*c+H*shift, D=U*d) implies U(d-ac)=H*shift.
for H in range(-5,6):
 for U in range(-3,4):
  for aa in range(-2,3):
   for cc in range(-2,3):
    for dd in range(-2,3):
     for sh in range(-2,3):
      if U*aa*cc+H*sh==U*dd:assert U*(dd-aa*cc)==H*sh
for t in ('root_expr_shape','root_eval_zero_w','signed_dvd_three_square_of_zero_w_zero'):
 assert '#print axioms DiophantineConsistency.Natural79ZeroWRootCutDraft.'+t in s
print(json.dumps({'scope':'literal root AST and source-assumption review; no Lean/model theorem','pinned_sources':5,'exact_dag_cuts':4,'signed_witness_checked':True,'axiom_reports_unexecuted':3},sort_keys=True,indent=2))
