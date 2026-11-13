#!/usr/bin/env python3
"""Static arity, forcing cut, mixed maps and source premise audit."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
b='research/adaptive-aq17-forced105-model-draft/'
t=pin(b+'AQ17Forced105ConditionalTransfer.lean.src','b77bfbaf3c41ff5d33cfa6a31e797bd4be85af3818ed178aa567b6bf5c526779')
a=pin(b+'AQ17Forced105Arithmetic.lean.src','b3057437cfb476170b28114283783bb0bd392a28f1de1ba4a39b6bf264b5e330')
l=pin(b+'AQ17Forced105Literal.lean.src','ca9548bcdc73ae480fafe801ad249e45a447f615b0d9bca8edda0c2b74376958')
r=pin(b+'AQ17Forced105Residuals.lean.src','d9b5cce48d8f89e6e9ec9823f10ebc4ecc23f5c68ba46218c58ef5da15eeb88b')
pin(b+'AQ17Forced105ResidualZeros.lean.src','767a0adb800e688506f36c2ab4cd5d55deaf05b4c2716fdb3682e204da578021')
pin(b+'receipt.json','b76c64faa7845e9a18ca94c7d5182119ca9d2db0eaf2f26d1d7f33fbb1e497e3')
pin('reviews/adaptive-aq17-natural-forced105-independent/result.json','21c3850d2c12e4324fee60eb5b3bb051b09a73676e1d5609c80e3f9b8541ee91')
g=json.loads(pin('research/adaptive-aq17-natural-forced105/candidate.json','ff131760c176ebd56a593aff49523daf384c03322e2ddaae07f65f8f63bb7bac'))
p=json.loads(pin('research/adaptive-aq17-factored-root94/candidate.json','7f9a6af2c44f1e9b6c763c9dd38cc4a3beb79d5dcd159539dc7275873e67c71a'))
assert 'def residuals (p : Fin 4 → ℤ) : Fin 8 → Expr (Fin 17)' in r
v=re.findall(r'^  !\[([^\n]+)\]$',r,re.M);assert len(v)==1 and len(v[0].split(','))==8
for source in (l,r):
 for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 17) := .var {i}' in source
 for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 17) := .constant (p {i})' in source
 for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in source
assert len(g['source'])==105 and [p['witnesses'][i] for i in (3,5,11,14,15,16)]==['f','T','y','firstQuotient','mainQuotient','vValueVariable']
for x in ['i=3 ∨ i=5 ∨ i=11 ∨ i=14 ∨ i=15 ∨ i=16','if Forced i then v i else v i+1','if Forced i then v i else v i-1','def ZeroEquivalence : Prop','def SixForced : Prop','def ForcingCutExtraction : Prop','(h : ForcingCutExtraction) : SixForced','4≤q ∧ 0<delta ∧ 0<c','ι (v 13+1)','(v 13+1) c hc htime','v 11*v 11+q*(v 16*v 16)=1+q*(v 11*v 11)','(v 11=0 → q*(v 16*v 16)=1)','(he : ZeroEquivalence) (hf : SixForced)','(h22 : AQ22Quotient110ConditionalTransferDraft.GraphZeroObligations)','(h20 : AQ20Substituted104ConditionalTransferDraft.GraphZeroObligations)','(h17 : AQ17Factored94ConditionalTransferDraft.GraphZeroObligations)']:assert x in t,x
for x in ['theorem positive_of_square_one_add (a n : V) (h : a*a=1+n)','theorem ordinate_pos (y z q : V) (hq : 1≤q)','(h : y*y+q*(z*z)=1+q*(y*y))','theorem y_pos_of_zero_product (y z q : V) (hq : 4≤q)','(hy : y=0 → q*(z*z)=1)','theorem time_pos (f time z rank c : V) (hc : 0<c)','theorem f_pos (f delta q : V) (hd : 0<delta) (hq : 0<q)','theorem j_pos_of_root_branch','((p 1 : ℤ) : DiffRing V)=ι k','(hzero : j=0 → ι z=(1-ι f-ι alpha)*(ι x+ι k)-ι f)']:assert x in a,x
for x in ['f_pos (v 3)','time_pos (v 3) (v 5) (v 16) (v 13+1)','y_pos_of_zero_product (v 11) (v 16)','positive_of_square_one_add (v 14)','positive_of_square_one_add (v 15)','ordinate_pos (v 11) (v 16)']:assert x in t,x
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',t+a+l+r)
print(json.dumps({'scope':'static source, graph and forcing-cut audit; no Lean','literal_and_residual_rows':105,'residual_arity':8,'forced_indices':[3,5,11,14,15,16],'time_rank_shift_checked':True,'graph_to_cut_and_zero_equivalence_explicit':True,'aq17_aq20_aq22_obligations_explicit':True,'optional_j_branch_requires_represented_second_port':True},sort_keys=True,indent=2))
