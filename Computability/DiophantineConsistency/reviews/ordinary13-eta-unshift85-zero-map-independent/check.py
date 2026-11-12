#!/usr/bin/env python3
"""Independent syntax, mapping and bridge interface review; no Lean."""
from pathlib import Path
import hashlib,json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-unshift85-zero-map-model-draft/EtaShifted86Graph.lean.src':'6943667d64f8eb0c6aee5b93f8f2765cd3334b8d1e3149fba28dc400e7fa18db',
'research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src':'ea90e2b20522046d60d0cca3353eb6e9dc62cea0a41d05064efb2fa288615b73',
'research/ordinary13-eta-unshift85-zero-map-model-draft/README.md':'699e068c1d48d47ad162fb24e33a21bd0637ce5bec8d64d0a9bcaffd1daeff65',
'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src':'bad45fb6e83d654f4b0c4f4e28c9906e69cdeddc29a7914e2442419f38fed05f',
'research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src':'11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a',
'research/ordinary13-natural-forced-w86/candidate.json':'75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/HAExpressionAssembly.lean':'15a4c07b1538fa1d9d3d6d5e7d6ab21d9ff9b6c9d80fa10218641fad2ba6b56e',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'Lean/DiophantineConsistency/IPRAExpressionNative.lean':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
parent=json.loads(s['research/ordinary13-natural-forced-w86/candidate.json']);child=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'])
assert parent['witnesses']==child['witnesses'] and parent['fixed_numerals']==child['fixed_numerals']
assert parent['witnesses'][9]=='n_eta' and parent['output']==child['output']=='out'
for graph,path,marker in [(parent,'research/ordinary13-eta-unshift85-zero-map-model-draft/EtaShifted86Graph.lean.src','def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :='),(child,'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src','def graph (p : Fin 4 → ℤ) : Graph :=')]:
 body=s[path].split(marker,1)[1]
 for i,n in enumerate(graph['witnesses']):assert f'let {n} : Expr (Fin 13) := .var {i}' in body
 for i,n in enumerate(graph['fixed_numerals']):assert f'let {n} : Expr (Fin 13) := .constant (p {i})' in body
 rows=[]
 for line in body.splitlines():
  m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
  if m:
   n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
 assert rows==graph['source']
assert '⟨A0, A1, Fa, Fs, out, g72,' in s['research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src']
assert [[('n_eta' if t=='eta' else t) for t in row] for row in parent['source'] if row!=['eta','+','n_eta',1]]==child['source']
t=s['research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src']
for x in ['if i=9 then v i+1 else v i','if i=9 then v i-1 else v i',
 'theorem evaluation','theorem zero_iff','def ForcedEta (K : ℕ)',
 'InternalZero (EtaNaturalUnitGraphDraft.graph (fun j => (ports K j:ℤ))).output v → 0<v 9',
 'theorem compact_no_zero_iff','theorem compact_sameNoZero (K : ℕ) (heta : ForcedEta K) : SameNoZero',
 '(hparent : PolynomialBridge (EtaShifted86GraphDraft.literal (fun j => (ports K j:ℤ))))',
 'HAExpressionNoZeroEquiv.bridge _ _ (compact_sameNoZero K heta) hparent',
 'IPRAExpressionNative.equivalence_of_bridge _ (polynomialBridge K heta hparent)']:
 assert x in t,x
he=s['Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean']
assert 'def SameNoZero {n m : ℕ} (e : Expr (Fin n)) (f : Expr (Fin m))' in he
assert '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in he
assert '∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in he
assert 'theorem equivalence_of_bridge {n : ℕ} (e : Expr (Fin n)) (hp : HAExpressionAssembly.PolynomialBridge e)' in s['Lean/DiophantineConsistency/IPRAExpressionNative.lean']
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in s['Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean']
M=1000000007
def calc(g,v):
 e={k:x%M for k,x in v.items()}
 for n,op,a,b in g['source']:
  a=a%M if isinstance(a,int) else e[a];b=b%M if isinstance(b,int) else e[b]
  e[n]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()%M
 return e[g['output']]
rng=random.Random(864205)
for _ in range(400):
 v={n:rng.randrange(0,15) for n in parent['witnesses']};v.update({n:rng.randrange(-10,11) for n in parent['fixed_numerals']})
 w=dict(v);w['n_eta']+=1
 assert calc(parent,v)==calc(child,w)
 assert w['n_eta']>0 and w['n_eta']-1==v['n_eta']
 z=dict(v);z['n_eta']=rng.randrange(1,15);lo=dict(z);lo['n_eta']-=1
 assert calc(child,z)==calc(parent,lo)
print(json.dumps({'source_sha256':pins,'parent_literal_rows':len(parent['source']),'child_literal_rows':len(child['source']),'slot9_substitution_exact':True,'both_direction_valuation_controls':400,'lean_executed':False,'scope':'syntax, directions and finite controls; forcing, parent bridge, all-model proof, provider closure and iPRA endpoint unproved'},sort_keys=True,indent=2))
