#!/usr/bin/env python3
"""Independent ForcedEta wrapper/source-map audit; no Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta85-forced-map-composition-draft/Eta85ForcedMap.lean.src':'bb8e5897e2a11ddf3c6edfe02a0442d3577a78b52b0fda526c8338e6691dbea1',
'research/ordinary13-eta85-forced-map-composition-draft/README.md':'50e553ed4e20604c3c3df498a3dba53e812fb558c85d4119c4d25767622f0c6b',
'research/ordinary13-eta-natural-graph-parity-composition-draft/EtaNaturalGraphParity.lean.src':'1a5a20a6b87f7521fa27fb8f7aded46b2b8183ec09c22679b857740522b12245',
'research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src':'ea90e2b20522046d60d0cca3353eb6e9dc62cea0a41d05064efb2fa288615b73',
'research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src':'11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a',
'research/ordinary13-natural-forced-w86/candidate.json':'75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'Lean/DiophantineConsistency/IPRAExpressionNative.lean':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta85-forced-map-composition-draft/Eta85ForcedMap.lean.src']
for t in ['theorem forcedEta (K : ℕ) : EtaUnshift85TransportDraft.ForcedEta K',
 'intro V _ _ v hz','EtaNaturalGraphParityDraft.eta_positive K v hz',
 'EtaUnshift85TransportDraft.compact_sameNoZero K (forcedEta K)',
 'EtaUnshift85TransportDraft.polynomialBridge K (forcedEta K) hparent',
 'EtaUnshift85TransportDraft.native_equivalence K (forcedEta K) hparent']:
 assert t in d,t
for name in ('polynomialBridge','native_equivalence'):
 h=d.split('theorem '+name,1)[1].split(':=',1)[0]
 assert '(hparent : PolynomialBridge (EtaShifted86GraphDraft.literal (fun j => (ports K j:ℤ))))' in h
h=s['research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src']
assert '''def ForcedEta (K : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (v : Fin 13 → V),
    InternalZero (EtaNaturalUnitGraphDraft.graph (fun j => (ports K j:ℤ))).output v → 0<v 9''' in h
p=s['research/ordinary13-eta-natural-graph-parity-composition-draft/EtaNaturalGraphParity.lean.src']
assert '''theorem eta_positive (K : ℕ) (v : Fin 13 → V)
    (hz : InternalZero (graph (fun j => (Residue90CompactPortBoundsDraft.ports K j:ℤ))).output v) :
    0<v 9''' in p
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in p
assert '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in s['Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean']
parent=json.loads(s['research/ordinary13-natural-forced-w86/candidate.json']);child=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'])
assert parent['witnesses']==child['witnesses'] and parent['witnesses'][9]=='n_eta'
assert parent['fixed_numerals']==child['fixed_numerals']
assert [[('n_eta' if x=='eta' else x) for x in row] for row in parent['source'] if row!=['eta','+','n_eta',1]]==child['source']
M=1000000007
def calc(g,e):
 e={n:x%M for n,x in e.items()}
 for n,op,a,b in g['source']:
  a=a%M if isinstance(a,int) else e[a];b=b%M if isinstance(b,int) else e[b]
  e[n]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()%M
 return e[g['output']]
rng=random.Random(927508)
for _ in range(200):
 v={n:rng.randrange(0,10) for n in parent['witnesses']};v.update({n:rng.randrange(-5,6) for n in parent['fixed_numerals']})
 w=dict(v);w['n_eta']+=1
 assert calc(parent,v)==calc(child,w) and w['n_eta']>0
print(json.dumps({'source_sha256':pins,'forced_eta_matches_graph_parity_interface':True,'both_parent_bridge_premises_retained':True,'exact_slot9_edit':True,'valuation_controls':200,'lean_executed':False,'scope':'source/interface and finite controls; no Lean, compiled forcing, parent bridge, physical binding or iPRA theorem'},sort_keys=True,indent=2))
