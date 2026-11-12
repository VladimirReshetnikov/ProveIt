#!/usr/bin/env python3
"""Static arity, represented-beta, coordinate and residual-case audit."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
b='research/adaptive-aq20-substituted104-model-draft/'
t=pin(b+'AQ20Substituted104ConditionalTransfer.lean.src','a4e44c67ead30d3a9503a01b31d021dc63b182d2af648cbbc80670809f21d93e')
l=pin(b+'AQ20Substituted104Literal.lean.src','4f37e98904b491e3c5d04265917902be23d4b661c28153e890b6e9712f796e4c')
r=pin(b+'AQ20Substituted104Residuals.lean.src','15d6509b3bc49521b1b1e11b7090c9a30d43643116d471e6b596a4f5304acf4d')
pin(b+'AQ20Substituted104ResidualZeros.lean.src','ae0f321216013671a767a2e2c44cf1bbe89ddc0c8f6a67a61345afc8a92ca348')
pin(b+'receipt.json','625a49c9713d41ef90e21996f4e661768b01db1365f2e0457329b47499ff06e8')
s=pin('research/adaptive-aq20-substituted104-residual-maps-draft/AQ20Substituted104ResidualMaps.lean.src','dc8c23f1532b141b3842c20bf3a19a03bce60c7cf62b45935cba26931ed4dd1d')
pin('research/adaptive-aq20-substituted104-residual-maps-draft/receipt.json','1868b020e167538dea60e42a03f273a1ce18e73f709bf95c0f5041c14d4b8f98')
pr=pin('research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Residuals.lean.src','711df4584209b4dcab07e32c55195ea9d9a82357b71d67b3345f37f447e3d7ca')
pin('reviews/adaptive-aq20-substituted-scales104-independent/result.json','b1afbc50dc3a450be310cee4f102f1e0796aaf38c20d107ea5924aff3902901a')
c=json.loads(pin('research/adaptive-aq20-substituted-scales104/candidate.json','e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'))
p=json.loads(pin('research/adaptive-aq22-two-quotients110/candidate.json','b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1'))
for source,num,dim in [(r,11,20),(pr,13,22)]:
 assert f'def residuals (p : Fin 4 → ℤ) : Fin {num} → Expr (Fin {dim})' in source
 v=re.findall(r'^  !\[([^\n]+)\]$',source,re.M);assert len(v)==1 and len(v[0].split(','))==num
for source in (l,r):
 for i,n in enumerate(c['witnesses']):assert f'let {n} : Expr (Fin 20) := .var {i}' in source
 for i,n in enumerate(c['fixed_numerals']):assert f'let {n} : Expr (Fin 20) := .constant (p {i})' in source
 for n,op,x,y in c['source']:assert f'  let {n} := {x} {op} {y}\n' in source
assert c['witnesses']==[x for x in p['witnesses'] if x not in ('scaleVariable','mainScaleVariable')]
for i,n in enumerate(c['witnesses']):assert n==p['witnesses'][i if i<13 else i+2]
for x in ['if h : i.val<13 then v ⟨i.val, by omega⟩ else v ⟨i.val+2, by omega⟩','if i.val=13 then (1+v 0*beta)*((1+v 0*beta)*(1+v 0*beta))*(v 0*beta)','else if i.val=14 then v 7*((1+v 0*beta)*(1+v 0*beta))','0<beta → ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V)=ι beta','ModelThirteenCarrier.port0','ModelCarrierCurrent.beta_pos','ι_lt_ι.mp','(h22 : AQ22Quotient110ConditionalTransferDraft.GraphZeroObligations)','(h20 : GraphZeroObligations)']:assert x in t,x
def theorem(n):
 m=re.search(r'(?ms)^theorem '+re.escape(n)+r'\b(.*?)(?=^theorem |^end DiophantineConsistency)',s);assert m,n;return m.group(1)
for j in range(11):
 i=j if j<4 else j+2;q=theorem('relation%02d'%j)
 assert f'AQ22Quotient110ResidualsDraft.residuals p {i})' in q and f'AQ20Substituted104ResidualsDraft.residuals p {j})' in q,(i,j)
 assert '((p 0 : ℤ) : DiffRing V)=ι beta' in q
for i in (4,5):assert f'AQ22Quotient110ResidualsDraft.residuals p {i})' in theorem('binding%02d'%i)
q=theorem('parent_scales')
for x in ['(hp 4)','(hp 5)','((p 0 : ℤ) : DiffRing V)=ι beta','ι_injective']:assert x in q
assert 'extend beta (project v)=v' in theorem('extend_project')
def branches(n):return re.split(r'(?m)^  · ',theorem(n).split('fin_cases i',1)[1])[1:]
e=branches('extend_zero');z=branches('project_zero');assert len(e)==13 and len(z)==11
for i,x in enumerate(e):
 if i in (4,5):assert f'binding{i:02d} p beta v hb' in x
 else:
  j=i if i<4 else i-2
  assert f'relation{j:02d} p beta v hb' in x and f'hc {j}' in x,(i,j)
for j,x in enumerate(z):
 i=j if j<4 else j+2
 assert f'AQ22Quotient110ResidualsDraft.residuals p {i})' in x and f'using hp {i}' in x and f'relation{j:02d} p beta (project v) hb' in x,(i,j)
assert 'project_zero CurrentWindowCarry2011.ports' in theorem('graphZeroObligations') and 'extend_zero CurrentWindowCarry2011.ports' in theorem('graphZeroObligations')
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',t+l+r+s)
print(json.dumps({'scope':'static source and branch audit, no Lean','corrected_residual_arities':[13,11],'literal_and_residual_rows':104,'common_residuals':11,'parent_zero_cases':13,'child_zero_cases':11,'parent_binding_indices':[4,5],'positive_beta_and_exact_cast_required':True,'prior_aq22_obligation_remains':True,'finite_case_order_assumed':True},sort_keys=True,indent=2))
