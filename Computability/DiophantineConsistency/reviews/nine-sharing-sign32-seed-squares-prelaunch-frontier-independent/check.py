#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-seed-squares-check'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'05a098974e1804b237fd1cf0c9e4d6ca86a6193479457957d1a2dcba283301a5','source-manifest.json':'d3a79d505051bf33ddd2a40318046fd5b365307f547b8857ff20f8308c280efd'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows']; assert len(rows)==2
for r,(n,h,imports,ts) in zip(rows,[('SharingSeed32Sextic','83ca02c43152569d1145e32052de74f60e840c16b15e13a55800508fc2c8b0b3',['NineFreshJones'],[]),('SharingSign32Squares','d90b685606af0bb4bfd304748ad28d9aa559a63f5d20a20cdf7645bb77b81b44',['SharingSeed32Sextic','SharingSign33Squares'],['seed_zero_iff_residuals'])]):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert r['module']=='DiophantineConsistency.'+n and sha(p)==r['source_sha256']==h
 assert re.findall(r'^import ([\w.]+)$',s,re.M)==r['imports']==['DiophantineConsistency.'+x for x in imports]
 assert re.findall(r'^theorem (\w+)',s,re.M)==ts
s=(P/'src/DiophantineConsistency/SharingSign32Squares.lean').read_text()
for t in ['[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℤ) (v : Fin 33 → V)','InternalZero (SharingSeed32Sextic.seed p) v ↔','∀ e ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p,','InternalZero e v','SharingSign33Squares.squareSum_zero_iff','SharingSign33Squares.square_syntax','SharingSeed32Sextic.seed','#print axioms DiophantineConsistency.SharingSign32Squares.seed_zero_iff_residuals']:assert t in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not r.stderr;pre=json.loads(r.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==2
print(json.dumps({'status':'PASS_NO_LEAN','preflight':pre,'scope':'same-valuation seed iff 23 residual zeros, symbolic integer ports, IΣ₁ model; no bridge, degree proof, numeric port binding or endpoint'},indent=2,sort_keys=True))
