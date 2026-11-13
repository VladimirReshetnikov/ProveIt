#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-seed-iff-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6604e5f7eda0818a32875730cf163b81c009f61f4bed4a7bcd4fa004272e02f5','survey.py':'a66a919b77028966abb5912e8aadb57a6824fd1707f3ea55e9bc9a6e937939e0','forward-provider.json':'f8314eac4f1f9a629fe52598d463f7ee92f9b3cd34f358a5e2908ccba4945115','providers.json':'f46e4aad54ea1f5659b671fb6f677f6b9d3bb95098adbd04526125def9d5e987','source-manifest.json':'737b0ad7cb103b6bf71ac91a70d1bacc5cbdd0f6334d093bb24ffb080b0576e8'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];want=[('Sign32SeedPointwise','6d5c1226c890f268d8b3aa9530bd6f6e01b1920d35a5492723d296ae6f8b9a88',['Sign32ForwardAssemblyAll','Sign32ReverseAssemblyAll'],['drop_lift','pointwise']),('Sign32SeedExistential','2a95bc5012676916c31b0aafeb919cc565f475896b131ef5c259957bf089028c',['Sign32SeedPointwise'],['exists_same_input'])];assert len(rows)==2
for r,(n,h,im,ts) in zip(rows,want):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and r['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in im]
 assert re.findall(r'^theorem (\w+)',s,re.M)==ts and all(f'#print axioms DiophantineConsistency.Sign32SeedIff.{t}' in s for t in ts)
 assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s
p=(P/'src/DiophantineConsistency/Sign32SeedPointwise.lean').read_text();e=(P/'src/DiophantineConsistency/Sign32SeedExistential.lean').read_text()
assert 'Sign32CoordinateRecover.drop (Sign32Substitution00.lift beta v) = v' in p
assert 'InternalZero (SharingSeed32Sextic.seed p) v ↔' in p and 'InternalZero (SharingSeed33.seed p) (Sign32Substitution00.lift beta v)' in p
assert 'Sign32ForwardAssembly.source32_to_source33 p beta v hp0' in p and 'Sign32ReverseAssembly.source33_to_source32 p beta (Sign32Substitution00.lift beta v) hp0 hz' in p and 'simpa only [drop_lift]' in p
assert '(∃ v : Fin 33 → V, v 0 = x ∧ InternalZero (SharingSeed32Sextic.seed p) v) ↔' in e and '(∃ v : Fin 34 → V, v 0 = x ∧ InternalZero (SharingSeed33.seed p) v)' in e
assert '⟨Sign32Substitution00.lift beta v, ?_, Sign32ForwardAssembly.source32_to_source33 p beta v hp0 hz⟩' in e and '⟨Sign32CoordinateRecover.drop v, ?_, Sign32ReverseAssembly.source33_to_source32 p beta v hp0 hz⟩' in e
for s in (p,e):assert '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s
lift=(D/'research/nine-sharing-sign32-substitution-group00-check/src/DiophantineConsistency/Sign32Substitution00.lean').read_text();drop=(D/'research/nine-sharing-sign32-coordinate-recovery-check/src/DiophantineConsistency/Sign32CoordinateReconstruct.lean').read_text();assert 'def lift' in lift and '!['+'v 0,' in lift and 'def drop' in drop and '!['+'v 0,' in drop
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==2
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'symbolic pointwise and same-input existential iff under hp0; no current-port binding or sextic Jones endpoint'},indent=2,sort_keys=True))
