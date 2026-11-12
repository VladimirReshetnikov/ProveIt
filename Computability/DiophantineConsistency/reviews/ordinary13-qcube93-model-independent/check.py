#!/usr/bin/env python3
"""Static AQ13 q³ arithmetic, graph transcription and premise audit."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
b='research/ordinary13-qcube93-model-draft/'
a=pin(b+'Ordinary13QCube93Arithmetic.lean.src','e9f61ed8c5e3262d9a316ef13cd15fa03dfc70a653c6ba7b85059aa9293be36d')
t=pin(b+'Ordinary13QCube93ConditionalTransfer.lean.src','c1ebe2c158143de433c1922f9b9e30c72c2cf7648a87e928416275f980f52d4e')
pl=pin(b+'Ordinary13QCube93Parent.lean.src','bb55431d8f7e065b4b2744dc6ab636b79d62b4efba8c4a55ac67a2bca2581418')
pr=pin(b+'Ordinary13QCube93ParentResiduals.lean.src','3c736a519e5d72fede02e6a16470c4b70503fc4ff9320ecd3e53547d4c3b2510')
cl=pin(b+'Ordinary13QCube93Child.lean.src','c05027c2a17f2ddb9256294ba1598c64e26b73ce239e8561a8860da63027c10e')
cr=pin(b+'Ordinary13QCube93ChildResiduals.lean.src','df55aaf919b8cc1a9176efaa60fe1b47942d8f9ce33f1b7b45ef769561b8b74f')
pin(b+'receipt.json','3f771bad960690e3ace41bd8e7df68ea51bbe45fe830ae1df0c821fcc8799b1e')
pin('reviews/ordinary13-natural-qcube-quotient93-independent/result.json','44d54929eab76e33a4ccd352fed2c2468e83b8d88d9c6eb4e64f785b54872b9f')
gp=json.loads(pin('research/ordinary13-natural-cfold-forced-x95-degree28/candidate.json','5fd11fa456867a2ed4f3b5bc58db59caab0f58736019ee864403d62124aced4e'))
gc=json.loads(pin('research/ordinary13-natural-qcube-quotient93-degree56/candidate.json','346a4895448a2212ce2617ef805fd3ea164d7d8896d5bad2c210cf19cd3ef21a'))
for source,g in [(pl,gp),(pr,gp),(cl,gc),(cr,gc)]:
 for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 13) := .var {i}' in source
 for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 13) := .constant (p {i})' in source
 for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in source,n
for source in (pr,cr):
 assert 'def residuals (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 13)' in source
 v=re.findall(r'^  !\[([^\n]+)\]$',source,re.M);assert len(v)==1 and len(v[0].split(','))==4
assert gp['witnesses'][0]=='n_J' and gp['witnesses'][7]=='n_Y' and gp['witnesses']==gc['witnesses']
for x in ['(1+b)^3-b*(b*b+3*b+3)=1','(h : (1+b)^3 ∣ y*b) : (1+b)^3 ∣ y','linear_combination -y*hb-(b*b+3*b+3)*hw','ModelRelationCombining.sq_dvd_sq','Trace75IntegralTransport.natural_dvd_of_signed','linear_combination hw-hz','(hy : 0<y)','∃ s : V, 0<s ∧ y=cubeScale b*s']:assert x in a,x
for x in ['if i=7 then cubeScale (b beta v)*(v 7+1)-1 else v i','if i=7 then s-1 else v i','def GraphObligations : Prop','def BetaRepresented (p : Fin 4 → ℤ) : Prop','((p 0 : ℤ) : DiffRing V)=ι beta','(hb : BetaRepresented p)','(hg : GraphObligations)','(hparent : PolynomialBridge (parent p))','positive_quotient_of_signed_norm']:assert x in t,x
assert 'z=ι (cubeScale (b beta v))*ι (b beta v)*t+ι (v 7+1)*ι (b beta v)-ι (cubeScale (b beta v))*bt' in t
assert 'z^2=(ι (cubeScale (b beta v))*ι (b beta v))^2*ι n' in t
sq=pin('Lean/DiophantineConsistency/ModelRelationCombining.lean','559df80321efb3854759ca9dcb20277533bba2568863ddf8e5059d81ac0cc5d6')
assert 'theorem sq_dvd_sq (m s : DiffRing V) (hm : m ≠ 0) (h : m ^ 2 ∣ s ^ 2) : m ∣ s' in sq
ref=pin('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean','4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885')
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in ref
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',a+t+pl+pr+cl+cr)
print(json.dumps({'scope':'static source and premise audit; no Lean elaboration','parent_child_rows':[95,93],'parent_child_residual_arities':[4,4],'changed_coordinate':7,'signed_square_divisibility_source_signature_checked':True,'signed_to_natural_divisibility_source_signature_checked':True,'explicit_bezout_and_quotient_witnesses_checked':True,'compact_beta_graph_maps_and_parent_bridge_remain_premises':True},sort_keys=True,indent=2))
