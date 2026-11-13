#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-substitution-group00-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'4d3064ac57e10c4e4c2d4e3512147408e53e07861ceec91de569da0a7d1a8fe9','source-manifest.json':'55a890536fb75f885c97b5d23d1b65932b73d43b7e83c15fdd2eb7342f1b7622','src/DiophantineConsistency/Sign32Substitution00.lean':'22c01a196c3cef5a6a44e7b447b878af54aaad2461b76f10e16821776329db67'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.SharingSign32Squares']
s=(P/'src/DiophantineConsistency/Sign32Substitution00.lean').read_text();b=(D/'research/nine-sharing-sign32-sextic-lean-draft/SharingSeed32BridgeDraft.lean').read_text()
assert s.split('def lift ',1)[1].split('\n\n/--',1)[0]==b.split('def lift ',1)[1].split('\n\n/--',1)[0]
new=''.join(s.split('def oldQ3',1)[1].split(':=',1)[1].split('theorem',1)[0].split());prev=(D/'research/nine-sharing-sign33-seed-syntax-check/src/DiophantineConsistency/SharingSeed33Syntax.lean').read_text().split('def remainingResiduals',1)[1].split('[\n',1)[1].splitlines()[0].strip().removesuffix(',');assert ''.join(prev.split())=='('+new+')'
assert re.findall(r'^theorem (\w+)',s,re.M)==['old_q3_head','old_q2_zero','old_q3_eval']
assert '(SharingSeed33.remainingResiduals p).head? = some (oldQ3 p)' in s
assert s.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)')==2 and '[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s
assert 'InternalZero (SharingSeed33.firstResidual p) (lift beta v)' in s
assert '(oldQ3 p).evalRing (fun j => ι (lift beta v j)) =' in s and '(SharingSeed32Sextic.firstResidual p).evalRing (fun j => ι (v j))' in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not r.stderr;pre=json.loads(r.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':pre,'scope':'old q2 zero, old q3 head and old/new q3 evaluation only; model hypotheses and port cast explicit; no complete bridge'},indent=2,sort_keys=True))
