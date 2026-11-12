#!/usr/bin/env python3
"""Independent source-signature and bounded index/arithmetic review."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-zero-growth-model-draft/EtaZeroGrowth.lean.src':'8f7f61c667d87c2e302e92a893dab01839cb5c5f5a8c1be26b08bf3a74360ab2',
'research/ordinary13-eta-zero-growth-model-draft/README.md':'6333feee80675de0cf2df9e3e2249d8694f0c241fecb486f8b0933880f269182',
'research/ordinary13-eta-zero-direct-projection-model-draft/EtaZeroDirectProjection.lean.src':'0984da9ba2037fd39b8898d2cf6e91cfb0f453161dd7fda8cdf139bacda7b222',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
'Lean/DiophantineConsistency/ArithmeticAdaptivePowerGrowth2011.lean':'1834de015364d93a8fa06b96e87b0973a2a5281ce3b73e7330cb56d6030fe84c'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
x=s['Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean']
assert '''theorem power_bound (X Y r k c eta zeta : V) (hX : 16≤X) (hY : 1≤Y) (hr : 2≤r)
    (hck : c=k*Y+eta) (hkez : k=eta+zeta) (hz : 0<zeta)
    (hc : c=ycoord (2*r+1) (Y*(X+1)))
    (hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1)) : Exp.exp (2*r+1)<Y''' in x
d=s['research/ordinary13-eta-zero-growth-model-draft/EtaZeroGrowth.lean.src']
for t in ['(hq : 16≤q) (hs : 0<s) (hw0 : 0<w0)', '(hX : X=q*w0) (hY : Y=q^3*s)',
 '(hn : 13≤n) (hindex : 2*n=R+1)', '(hck : c=k*Y+eta) (hk : k=eta+zeta) (hzeta : 0<zeta)',
 '(hmainy : c=ycoord R (Y*(X+1)))', '(hfirst : k=2*ycoord n (2*(X*Y*Y-1)+1))',
 'have hr : 2≤r := by', 'have hR : R=2*r+1 := by', 'apply (add_le_add_iff_right (1:V)).mp', 'apply add_right_cancel (b:=(1:V))',
 'EtaZeroDirectProjectionDraft.power_of_direct_carrier q X Y k R c gamma main s w']:
 assert t in d,t
z=s['research/ordinary13-eta-zero-direct-projection-model-draft/EtaZeroDirectProjection.lean.src']
assert 'theorem power_of_direct_carrier (q X Y k R c gamma main s w : V)' in z
assert '(hx : xcoord R (Y*(X+1))=main)' in z and '(hy : ycoord R (Y*(X+1))=c)' in z
old=s['Lean/DiophantineConsistency/ArithmeticAdaptivePowerGrowth2011.lean']
assert 'have hr2 : 2≤r := by' in old and 'add_le_add_iff_right' in old
assert 'have hR : R=2*r+1 := by' in old and 'apply add_right_cancel' in old
assert 'tsub_add_cancel_of_le' in old
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rows={r[0]:r for r in g['source']}
for row in [['X','*','q','n_w'],['Y','*','q3','s'],['kbase','+','n_eta','n_zeta'],['k','+','kbase',1],['c','+','n_eta','kY']]:assert rows[row[0]]==row
for n in range(13,1013):
 r=n-1;R=2*n-1
 assert r+1==n and r>=2 and R==2*r+1 and 2*n==R+1
rng=random.Random(982202);num=0
for _ in range(500):
 q=rng.randrange(16,55);w0=rng.randrange(1,9);s0=rng.randrange(1,6);eta=rng.randrange(0,6);zeta=rng.randrange(1,6)
 X=q*w0;Y=q**3*s0;k=eta+zeta;c=k*Y+eta
 assert X>=16 and Y>=1 and c==k*Y+eta and k==eta+zeta
 assert 16*(2*(2*X*Y*Y+1)) < (2*(Y*(X+1))+3)**2
 num+=1
print(json.dumps({'source_sha256':pins,'predecessor_conversion_controls':1000,'bounds_and_eta_controls':num,'predecessor_and_index_explicit_model_steps':True,'lean_executed':False,'scope':'source-interface and finite controls; no tactic elaboration, graph extraction, provider build, or iPRA endpoint'},sort_keys=True,indent=2))
