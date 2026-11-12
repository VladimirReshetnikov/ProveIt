#!/usr/bin/env python3
"""Static arity, coordinate and residual-case audit of AQ17 source drafts."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
b='research/adaptive-aq17-factored94-model-draft/'
t=pin(b+'AQ17Factored94ConditionalTransfer.lean.src','37d82d6ffc27958025a2752f2c7171b66b8318a801cd314dab74c2a279458d66')
l=pin(b+'AQ17Factored94Literal.lean.src','d419db2a442456bb31c135b3270ab3c19916e04c79f996d02727b36f399333e7')
r=pin(b+'AQ17Factored94Residuals.lean.src','317e919190e12bafd6bd641338ed154bb2ee201fc3f1c8fe71f9ed645d9418e3')
pin(b+'AQ17Factored94ResidualZeros.lean.src','21ee415b10988e4cc9dac54e21b15c72a53de0e53caec7d46db032567403036c')
pin(b+'receipt.json','a21c9d545217d4f3a84a60aebb0bb0b81e1e567e13b35be9b2e18802dfd8e559')
s=pin('research/adaptive-aq17-factored94-residual-maps-draft/AQ17Factored94ResidualMaps.lean.src','031ce00dabc454bda89a8b8a5154f148addc2b7dce127559e467cc710a205584')
pin('research/adaptive-aq17-factored94-residual-maps-draft/receipt.json','c634a3576b2a20650b18f2822c423413f603508d66662a8b8c8216e59b7c557c')
pr=pin('research/adaptive-aq20-substituted104-model-draft/AQ20Substituted104Residuals.lean.src','15d6509b3bc49521b1b1e11b7090c9a30d43643116d471e6b596a4f5304acf4d')
pin('reviews/adaptive-aq17-factored-root94-independent/result.json','0b206d5f4e0652c6d9c7bd63855585cc7a0453802b1dfdf921dd68edb5e289ea')
c=json.loads(pin('research/adaptive-aq17-factored-root94/candidate.json','7f9a6af2c44f1e9b6c763c9dd38cc4a3beb79d5dcd159539dc7275873e67c71a'))
p=json.loads(pin('research/adaptive-aq20-substituted-scales104/candidate.json','e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'))
for source,num,dim in [(r,8,17),(pr,11,20)]:
 assert f'def residuals (p : Fin 4 → ℤ) : Fin {num} → Expr (Fin {dim})' in source
 v=re.findall(r'^  !\[([^\n]+)\]$',source,re.M);assert len(v)==1 and len(v[0].split(','))==num
for source in (l,r):
 for i,n in enumerate(c['witnesses']):assert f'let {n} : Expr (Fin 17) := .var {i}' in source
 for i,n in enumerate(c['fixed_numerals']):assert f'let {n} : Expr (Fin 17) := .constant (p {i})' in source
 for n,op,x,y in c['source']:assert f'  let {n} := {x} {op} {y}\n' in source
assert c['witnesses']==[x for x in p['witnesses'] if x not in ('ellVariable','cSquareVariable','deltaVariable')]
for i,n in enumerate(c['witnesses']):assert n==p['witnesses'][i if i<14 else i+2]
assert [p['witnesses'][i] for i in (14,15,19)]==['ellVariable','cSquareVariable','deltaVariable']
for x in ['if h : i.val<14 then v ⟨i.val, by omega⟩ else v ⟨i.val+2, by omega⟩','if i.val=14 then (v 6*v 7)*(v 7*(v 9+v 10))','else if i.val=15 then (v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))','else if i.val=19 then 3+4*(v 6*v 7+v 7)+(v 6*v 7+v 7)*(v 6*v 7+v 7)','(h22 : AQ22Quotient110ConditionalTransferDraft.GraphZeroObligations)','(h20 : AQ20Substituted104ConditionalTransferDraft.GraphZeroObligations)','(h17 : GraphZeroObligations)']:assert x in t,x
def theorem(n):
 m=re.search(r'(?ms)^theorem '+re.escape(n)+r'\b(.*?)(?=^theorem |^end DiophantineConsistency)',s);assert m,n;return m.group(1)
mapping=[0,1,2,3,4,7,8,9]
for j,i in enumerate(mapping):
 q=theorem('relation%02d'%j)
 assert f'AQ20Substituted104ResidualsDraft.residuals p {i})' in q and f'AQ17Factored94ResidualsDraft.residuals p {j})' in q,(i,j)
for i in (5,6,10):assert f'AQ20Substituted104ResidualsDraft.residuals p {i})' in theorem('binding%02d'%i)
q=theorem('parent_bindings')
for x in ['(hp 5)','(hp 6)','(hp 10)','ι_injective']:assert x in q
assert 'extend (project v)=v' in theorem('extend_project')
def branches(n):return re.split(r'(?m)^  · ',theorem(n).split('fin_cases i',1)[1])[1:]
e=branches('extend_zero');z=branches('project_zero');assert len(e)==11 and len(z)==8
for i,x in enumerate(e):
 if i in (5,6,10):assert f'binding{i:02d} p v' in x
 else:
  j=mapping.index(i);assert f'relation{j:02d} p v' in x and f'hc {j}' in x,(i,j)
for j,x in enumerate(z):
 i=mapping[j]
 assert f'AQ20Substituted104ResidualsDraft.residuals p {i})' in x and f'using hp {i}' in x and f'relation{j:02d} p (project v)' in x,(i,j)
assert 'project_zero CurrentWindowCarry2011.ports' in theorem('graphZeroObligations') and 'extend_zero CurrentWindowCarry2011.ports' in theorem('graphZeroObligations')
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',t+l+r+s)
print(json.dumps({'scope':'static source and branch audit only; no Lean','corrected_residual_arities':[11,8],'literal_and_residual_rows':94,'common_residuals':8,'parent_zero_cases':11,'child_zero_cases':8,'parent_binding_indices':[5,6,10],'inherited_aq20_aq22_obligations_remain':True,'finite_case_order_assumed':True},sort_keys=True,indent=2))
