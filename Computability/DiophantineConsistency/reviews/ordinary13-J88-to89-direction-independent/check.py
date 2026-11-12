#!/usr/bin/env python3
"""Independent J-transfer direction and source audit; no Lean."""
from pathlib import Path
import hashlib,itertools,json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-J88-to89-model-draft/JShifted89Graph.lean.src':'c3c7be9870d8ee8049943152adad3a4f31cfcbd383295152fa0fa6d4ad958ca4',
'research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src':'ac7efbd0c75ecd15ccb19d638ee21806bff9284f092830d074d93c8954d621c5',
'research/ordinary13-J88-to89-model-draft/README.md':'aef4009b034825d0b38cd4ae61a58a8419ab837b51f668e2a35c2b297606d163',
'research/ordinary13-gamma87-to88-model-draft/GammaShifted88Graph.lean.src':'64f0975fed6a869ea1d2edb53086031d4942e1b2d5d44c85e2691be9e44d184b',
'research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src':'a11a673c36c9967e30c3fa68c9ef89b7f8470a64b0ca5d7e1c9bc0113fe0e5ae',
'research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src':'1cbd2cdd357df688806a70f771d8a2a199290bf5e887a38b0b677ea25c845aab',
'research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src':'ea90e2b20522046d60d0cca3353eb6e9dc62cea0a41d05064efb2fa288615b73',
'research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src':'c30a9d4fe05ca8878e7681f1987b27e51af5db5bc4366d65b8cf050589636c63',
'research/ordinary13-natural-unit-product89/candidate.json':'1d865512c2c78580af0d6a5285c009e5fa03deb141dc711dc5e3adb0b268938d',
'research/ordinary13-natural-unit-product88/candidate.json':'95fdd3495b777a0bdf64c95f6dd24cda660dee42f0508c76fdb081da21f42a5a',
'research/ordinary13-natural-forced-gamma87/candidate.json':'e753c7c5f8110b9f15e84c9f0da88847a54486f442b60b11812ca3688ca55e21',
'research/ordinary13-natural-forced-w86/candidate.json':'75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
paths=['research/ordinary13-natural-unit-product89/candidate.json','research/ordinary13-natural-unit-product88/candidate.json','research/ordinary13-natural-forced-gamma87/candidate.json','research/ordinary13-natural-forced-w86/candidate.json','research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']
gs=[json.loads(s[p]) for p in paths]
assert all(g['witnesses']==gs[0]['witnesses'] and g['fixed_numerals']==gs[0]['fixed_numerals'] for g in gs)
assert gs[0]['witnesses'][0]=='n_J' and gs[0]['witnesses'][6]=='n_w' and gs[0]['witnesses'][9]=='n_eta' and gs[0]['witnesses'][12]=='n_gamma'
for (parent,child,name,var) in zip(gs,gs[1:],['J','gamma','w','eta'],['n_J','n_gamma','n_w','n_eta']):
 assert [[var if x==name else x for x in row] for row in parent['source'] if row!=[name,'+',var,1]]==child['source']
for g,p in [(gs[0],'research/ordinary13-J88-to89-model-draft/JShifted89Graph.lean.src'),(gs[1],'research/ordinary13-gamma87-to88-model-draft/GammaShifted88Graph.lean.src')]:
 body=s[p].split('def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=',1)[1];rows=[]
 for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 13) := .var {i}' in body
 for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 13) := .constant (p {i})' in body
 for line in body.splitlines():
  m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
  if m:
   name,a,op,b=m.groups();rows.append([name,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
 assert rows==g['source']
t=s['research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src']
for x in ['if i=0 then v i+1 else v i','if i=0 then v i-1 else v i','theorem J_positive',
 'Gamma87To88TransportDraft.zero_iff','W86To87TransportDraft.zero_iff',
 'EtaUnshift85TransportDraft.zero_iff','EtaNaturalJPositiveDraft.J_positive p e hz85',
 'show (0:Fin 13)≠9 by decide','show (0:Fin 13)≠6 by decide','show (0:Fin 13)≠12 by decide',
 '(h89 : PolynomialBridge (JShifted89GraphDraft.literal (fun j => (ports K j:ℤ))))',
 'Gamma87To88TransportDraft.native85 K heta (bridge88 K h89)']:
 assert x in t,x
j=t.split('theorem J_positive',1)[1].split('theorem compact_no_zero_iff',1)[0]
assert '(p : Fin 4 → ℕ)' in j and 'hbeta' not in j and 'ForcedEta' not in j
assert 'v).mp hz\n' in j and 'g).mp hz87' in j and 'w).mp hz86' in j
assert 'theorem J_positive (p : Fin 4 → ℕ)' in s['research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src']
assert '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in s['Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean']
# J=0 first-root sign controls with natural X,K and arbitrary (including negative) beta.
cases=0
for F,alpha,X,K,beta in itertools.product(range(1,7),range(1,7),range(6),range(6),range(-3,4)):
 J=0;b=J*beta;q=1+b;C=q-F-alpha;Z=F-C*(X+K)
 assert q==1 and C<0 and Z>=F>0
 cases+=1
M=1000000007
def calc(g,v):
 e={n:x%M for n,x in v.items()}
 for n,op,a,b in g['source']:
  a=a%M if isinstance(a,int) else e[a];b=b%M if isinstance(b,int) else e[b]
  e[n]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()%M
 return e[g['output']]
rng=random.Random(880941)
for _ in range(250):
 v={n:rng.randrange(0,10) for n in gs[0]['witnesses']};v.update({n:rng.randrange(-5,6) for n in gs[0]['fixed_numerals']})
 vals=[v]
 for name in ('n_J','n_gamma','n_w','n_eta'):
  w=dict(vals[-1]);w[name]+=1;vals.append(w)
 assert len({calc(g,e) for g,e in zip(gs,vals)})==1
 assert len({e['n_J'] for e in vals[1:]})==1
print(json.dumps({'source_sha256':pins,'exact_four_coordinate_edits':True,'forward_chain_controls':250,'J_zero_sign_controls':cases,'J_proof_has_no_beta_or_eta_forcing_premise':True,'lean_executed':False,'scope':'source directions and finite controls only; no Lean, all-model J proof, parent bridge, physical binding or iPRA endpoint'},sort_keys=True,indent=2))
