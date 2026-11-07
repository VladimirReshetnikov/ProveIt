#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-coordinate-recovery-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'878b8062c9701cab468d2edf3a82a6ee60d689f0684dfa4a631218e61c9b2970','survey.py':'5f443546621c14ed1283aeff03192f0226235b6ff0a6b165faa786515447276e','providers.json':'f46e4aad54ea1f5659b671fb6f677f6b9d3bb95098adbd04526125def9d5e987','source-manifest.json':'d0138e087cbd60cf86697a04cf25865923ad1877a67d1a95b863280c53094dd9'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];want=[('Sign32CoordinateRecover','71140c5eaffe5f0ff72488c4c76bcb3e03dd734b2f4a5078b8433f4ef2532b11','Sign32Substitution07','q2_coordinate'),('Sign32CoordinateReconstruct','df139121e3ac4acd424a1ca3be914012ea9a974540e5d4d0a1cbe95a871e7d0c','Sign32CoordinateRecover','lift_drop')];assert len(rows)==2
for r,(n,h,im,t) in zip(rows,want):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and r['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+im]
 assert re.findall(r'^theorem (\w+)',s,re.M)==[t] and f'#print axioms DiophantineConsistency.Sign32CoordinateRecover.{t}' in s
 assert '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s and '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s and '(hz : InternalZero (SharingSeed33.seed p) v)' in s
r=(P/'src/DiophantineConsistency/Sign32CoordinateRecover.lean').read_text();z=(P/'src/DiophantineConsistency/Sign32CoordinateReconstruct.lean').read_text();d=(D/'research/nine-sharing-sign32-sextic-lean-draft/SharingSeed32BridgeDraft.lean').read_text()
assert 'v 15 = (beta * (v 1 + 1) + 1) ^ 2' in r and 'SharingSign33Squares.seed_zero_iff_residuals' in r and 'ι_injective' in r
assert z.split('def drop ',1)[1].split('\n\ntheorem',1)[0]==d.split('def drop ',1)[1].split('\n\nvariable',1)[0]
assert 'Sign32Substitution00.lift beta (drop v) = v' in z and 'q2_coordinate p beta v hp0 hz' in z and 'fin_cases j' in z
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==2
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'old q2 coordinate recovery and lift(drop(v))=v only, under hp0 and old zero; no reverse seed theorem'},indent=2,sort_keys=True))
