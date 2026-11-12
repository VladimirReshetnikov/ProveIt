#!/usr/bin/env python3
"""Static AQ17/104 J force, branch orientation and transport review."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
b='research/adaptive-aq17-forced104-j-draft/'
f=pin(b+'AQ17Forced104JForce.lean.src','4362d2baa3ff5056b463d1fb3cef294878a1d9d9809ce556c94a042104f68f96')
t=pin(b+'AQ17Forced104Transport.lean.src','6f8a8c649eb59e35776c8c069b95caab7721d07080b28289d1944d0478f0b863')
l=pin(b+'AQ17Forced104Literal.lean.src','d2ed649e06621b6ae1cdfff6c4f33d5ad1835f2fd73855d4227accd56016f9c0')
r=pin(b+'AQ17Forced104Residuals.lean.src','35135a822e757b28877cc6c3a0b013349137d20078d67e9a8fbcf3751da4b72a')
pin(b+'AQ17Forced104ResidualZeros.lean.src','3245b14ff7d92f9159f159ff67a93565b0f638c0456e1a909bc9b8c2bb62bd09')
pin(b+'receipt.json','74a026b7168cba3485c70dc66854cb6889574c4913a46d56fb91fcd789bccc2b')
pin('reviews/adaptive-aq17-natural-forced104-independent/result.json','55c29d6bebbf102b6e15820d25fba14f107d9518a89743233232c5f965ea19f8')
g=json.loads(pin('research/adaptive-aq17-natural-forced104/candidate.json','1a5f4c54fc5ad2768c676eea1bf875cda7917224e3c4bceebc3d852827fcb55a'))
h=json.loads(pin('research/adaptive-aq17-natural-forced105/candidate.json','ff131760c176ebd56a593aff49523daf384c03322e2ddaae07f65f8f63bb7bac'))
assert 'def residuals (p : Fin 4 → ℤ) : Fin 8 → Expr (Fin 17)' in r
v=re.findall(r'^  !\[([^\n]+)\]$',r,re.M);assert len(v)==1 and len(v[0].split(','))==8 and v[0].split(',')[5]=='zDifference'
for source in (l,r):
 for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 17) := .var {i}' in source
 for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 17) := .constant (p {i})' in source
 for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in source
assert [g['witnesses'][i] for i in (0,1,2,6)]==['n_J','n_F','n_alpha','n_X']
# 105 equals 104 with its J coordinate raised once.
rep=lambda x:'shift_J' if x=='n_J' else x
assert h['source']==[['shift_J','+','n_J',1]]+[[n,op,rep(x),rep(y)] for n,op,x,y in g['source']]
assert h['output']==g['output'] and h['witnesses']==g['witnesses'] and h['fixed_numerals']==g['fixed_numerals']
for x in ['.mp hz 5','(hj : v 0=0)','(0 : DiffRing V)=(1-ι (v 1+1)-ι (v 2+1))*(ι (v 6+1)+ι k)-ι (v 1+1)','linear_combination -h','((p 1 : ℤ) : DiffRing V)=ι k','j_pos_of_root_branch','ModelThirteenCarrier.port1 (V:=V)']:assert x in f,x
for x in ['if i=0 then v i+1 else v i','if i=0 then v i-1 else v i','AQ17Forced104JForceDraft.current_j_positive','AQ17Forced105EvaluationDraft.zeroEquivalence','AQ17Forced105CutExtractionDraft.forcingCutExtraction','(h22 : AQ22Quotient110ConditionalTransferDraft.GraphZeroObligations)','(h20 : AQ20Substituted104ConditionalTransferDraft.GraphZeroObligations)','(h17 : AQ17Factored94ConditionalTransferDraft.GraphZeroObligations)']:assert x in t,x
for i in range(8):
 m=re.search(r'(?ms)^theorem relation%02d\b(.*?)(?=^theorem )'%i,t);assert m
 assert f'AQ17Forced105ResidualsDraft.residuals p {i})' in m.group(1) and f'AQ17Forced104ResidualsDraft.residuals p {i})' in m.group(1)
 assert 'raiseJ v k' in m.group(1) and f'relation{i:02d} p v' in t.split('theorem evaluation ',1)[1]
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',t+f+l+r)
print(json.dumps({'scope':'static graph, J-zero orientation, representation and transport audit; no Lean','literal_and_residual_rows':104,'residual_arity':8,'residual_5_J_zero_orientation':'Bt=0 to 0=Bt','pointwise_transport_relations':8,'current_second_port_model_representation_source':True,'prior_graph_obligations_remain':3},sort_keys=True,indent=2))
