#!/usr/bin/env python3
"""Independent 87/86/85 directional and interface audit; no Lean."""
from pathlib import Path
import hashlib,json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-w86-to87-model-draft/WShifted87Graph.lean.src':'69d02ff50663bdd3e112bbe589ddaf2143d612a2240232912659bfe139527453',
'research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src':'1cbd2cdd357df688806a70f771d8a2a199290bf5e887a38b0b677ea25c845aab',
'research/ordinary13-w86-to87-model-draft/README.md':'8ef503ae40068442ed47914a98f629aaddbe62d94e7c3d96e22b89fb5630d390',
'research/ordinary13-natural-forced-gamma87/candidate.json':'e753c7c5f8110b9f15e84c9f0da88847a54486f442b60b11812ca3688ca55e21',
'research/ordinary13-natural-forced-w86/candidate.json':'75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'research/ordinary13-eta-unshift85-zero-map-model-draft/EtaShifted86Graph.lean.src':'6943667d64f8eb0c6aee5b93f8f2765cd3334b8d1e3149fba28dc400e7fa18db',
'research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src':'ea90e2b20522046d60d0cca3353eb6e9dc62cea0a41d05064efb2fa288615b73',
'research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src':'e3bace196b09c86927bd178c279111ab4c97d076a18711c676ff127f002fe063',
'research/ordinary13-residue-compact-qbound-model-draft/ResidueCompactQBound.lean.src':'79fb9cc240fa5f24c4a89bbce7c10773e2986c53b677320514009fe964bf622c',
'research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src':'11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
g87=json.loads(s['research/ordinary13-natural-forced-gamma87/candidate.json']);g86=json.loads(s['research/ordinary13-natural-forced-w86/candidate.json']);g85=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'])
assert g87['witnesses']==g86['witnesses']==g85['witnesses'] and g87['witnesses'][6]=='n_w' and g87['witnesses'][9]=='n_eta'
assert g87['fixed_numerals']==g86['fixed_numerals']==g85['fixed_numerals']
for g,p in [(g87,'research/ordinary13-w86-to87-model-draft/WShifted87Graph.lean.src'),(g86,'research/ordinary13-eta-unshift85-zero-map-model-draft/EtaShifted86Graph.lean.src')]:
 body=s[p].split('def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=',1)[1]
 for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 13) := .var {i}' in body
 for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 13) := .constant (p {i})' in body
 rs=[]
 for line in body.splitlines():
  m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
  if m:
   name,a,op,b=m.groups();rs.append([name,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
 assert rs==g['source']
assert [[('n_w' if a=='w' else a) for a in row] for row in g87['source'] if row!=['w','+','n_w',1]]==g86['source']
assert [[('n_eta' if a=='eta' else a) for a in row] for row in g86['source'] if row!=['eta','+','n_eta',1]]==g85['source']
t=s['research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src']
for x in ['if i=6 then v i+1 else v i','if i=6 then v i-1 else v i',
 'theorem w_positive','EtaUnshift85TransportDraft.zero_iff','EtaNaturalXPositiveDraft.witness_positive',
 'show (6:Fin 13)≠9 by decide','ResidueCompactQBoundDraft.beta_at_least_46',
 'theorem compact_sameNoZero','(h87 : PolynomialBridge','EtaUnshift85TransportDraft.ForcedEta K']:
 assert x in t,x
w=t.split('theorem w_positive',1)[1].split('theorem compact_no_zero_iff',1)[0]
assert 'ForcedEta' not in w and '(hbeta : 0<(p 0:V))' in w
assert 'zero_iff (fun j => (p j:ℤ)) v).mp hz' in w
assert 'theorem beta_at_least_46 : (46:V)≤(CompactFixedBeta.betaNat:V)' in s['research/ordinary13-residue-compact-qbound-model-draft/ResidueCompactQBound.lean.src']
assert '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in s['Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean']
M=1000000007
def calc(g,v):
 e={n:x%M for n,x in v.items()}
 for n,op,a,b in g['source']:
  a=a%M if isinstance(a,int) else e[a];b=b%M if isinstance(b,int) else e[b]
  e[n]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()%M
 return e[g['output']]
rng=random.Random(420976)
for _ in range(400):
 v={n:rng.randrange(0,15) for n in g87['witnesses']};v.update({n:rng.randrange(-10,11) for n in g87['fixed_numerals']})
 w=dict(v);w['n_w']+=1;e=dict(w);e['n_eta']+=1
 assert calc(g87,v)==calc(g86,w)==calc(g85,e)
 assert e['n_w']==w['n_w'] and w['n_w']-1==v['n_w']
print(json.dumps({'source_sha256':pins,'exact_two_coordinate_edits':True,'two_step_valuation_controls':400,'w_positive_has_no_forced_eta_premise':True,'lean_executed':False,'scope':'source/direction and finite controls; no Lean, graph positivity, parent bridge, provider build or iPRA endpoint'},sort_keys=True,indent=2))
