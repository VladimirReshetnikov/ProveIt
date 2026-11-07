#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-zero-bridge-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ccd61649bb41575a4e61c47efa041ec62f2ff2ac7c01c34cece8b3441bc6a485','source-manifest.json':'2f05314e8f3c1913fd22d69f7460fd4458a55db196ce1c0b8ad02ef485b94cc7','provider-union-survey.py':'2bd3b58f6934cba8ddedf1abe690a88ecf080c812b1fad11772026ca4d0f9780','union.json':'a7a5de9714fe786dda5eff6d046d97148660fc3368c2bac5c07388739aea5cb3'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign26CoordinateDrop','Sign26ForwardBridge','Sign26ReverseBridge'];texts=[]
for e in m:
 n=e['module'].split('.')[-1];p=P/'src/DiophantineConsistency'/f'{n}.lean';assert H(p)==e['source_sha256']==H(D/f'research/nine-sharing-sign26-zero-bridge-draft/{n}.lean');texts.append(p.read_text())
c,f,b=texts;drop=c.split('def drop ',1)[1].split('![',1)[1].split(']',1)[0].split(', ');assert drop==[f'v {i}' for i in range(22)]+[f'v {i}' for i in range(23,28)]
for x in ['Sign26CongruenceCuts.lift (v 22) (drop v) = v','drop (Sign26CongruenceCuts.lift gap v) = v']:assert x in c
for x in ['(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)','(hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)','(hbeta : 1 ≤ beta)','Sign26SeedGap.exists_gap p beta K v hp0 hp1 hbeta hz','Sign26ZeroExtraction.q3_eq p v hz','∃ gap : V, ι gap = Sign26CongruenceCuts.ringGap p v']:assert x in f
for x in ['theorem backward','(hz : InternalZero (SharingSeed27Sextic.seed p) v)','InternalZero (SharingSeed26Sextic.seed p) (drop v)','have hr := lift_drop v','have hq3 := sub_eq_zero.mp hq3','Sign26CongruenceCuts.old_Gap_row p','have hgap : ι (v 22) = Sign26CongruenceCuts.ringGap p (drop v)']:assert x in b
ids=[1,2,3,4,5,6,7,10,11,13,14,15,16,17]
for s,prefix,count in [(f,'old',18),(b,'new',17)]:
 body=s.split('theorem '+prefix+'_rows ',1)[1].split(':= by rfl',1)[0];assert body.count('Sign26RemainingCuts.'+prefix+'R')==14 and body.count('Sign26CongruenceCuts.'+prefix)==(3 if prefix=='old' else 2) and s.count(' | rfl')==count-1
 for i in ids:assert f'Sign26RemainingCuts.R{i:02d}_eval' in s and f'Sign26RemainingCuts.{"new" if prefix=="old" else "old"}_R{i:02d}_row' in s
 for name in ['Tau','Inner']:assert re.search(rf'Sign26CongruenceCuts\.{name}_eval p .*hgap hq3',s)
assert 'Sign26CongruenceCuts.oldGap_zero p v gap hgap' in f and 'have hfirst' in b
for n,h in [('nine-sharing-sign26-remaining-cuts-terminal-frontier-independent','dfa5e871926f26c7ef693eeb86d561892432cd3219e2dfdcd296745ac969e09a'),('nine-sharing-sign26-seed-gap-terminal-frontier-independent','9a107d39ef50a60c5ea5dfe8e5b1220c8faf35d074a44e4a4b9dc793df4c7347')]:
 p=D/'reviews'/n/'check.py';assert H(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'conditional forward and unconditional-on-ports reverse zero bridge; q3 and represented-gap hypotheses used explicitly, no Lean replay'},sort_keys=True,indent=2))
