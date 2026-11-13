#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-zero-bridge-retry02';O=D/'research/nine-sharing-sign26-zero-bridge-retry01';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ed6519380cb2f20a94684b8fb8be55b6abe95ccfcade96c574c7024490e7940c','source-manifest.json':'8a6a1df37050357dea52177be7bf3d5b6dbe8c6495fa0b1ee269e86349a5c2a8','provider-union-survey.py':'2bd3b58f6934cba8ddedf1abe690a88ecf080c812b1fad11772026ca4d0f9780','union.json':'a7a5de9714fe786dda5eff6d046d97148660fc3368c2bac5c07388739aea5cb3','src/DiophantineConsistency/Sign26ReverseGap.lean':'b852e6633471547daef53a81e6a092ae2f304ee1df3b1c050a6b225d05a28159','src/DiophantineConsistency/Sign26ReverseBridgeRetry.lean':'9a419a7ed8592b083bef3040804b7ce426e3fc2093b40a238eb1d0b94d253334'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign26CoordinateDrop','Sign26ForwardBridge','Sign26ReverseGap','Sign26ReverseBridgeRetry']
for e in m:
 n=e['module'].split('.')[-1];assert H(P/'src/DiophantineConsistency'/f'{n}.lean')==e['source_sha256']
for n in ['Sign26CoordinateDrop','Sign26ForwardBridge','Sign26ReverseBridgeRetry']:assert (P/'src/DiophantineConsistency'/f'{n}.lean').read_bytes()==(O/'src/DiophantineConsistency'/f'{n}.lean').read_bytes()
a=(O/'src/DiophantineConsistency/Sign26ReverseGap.lean').read_text();b=(P/'src/DiophantineConsistency/Sign26ReverseGap.lean').read_text();old='simpa only [Sign26CongruenceCuts.ringGap] using (sub_eq_zero.mp h)';new='simpa [Sign26CongruenceCuts.ringGap] using (sub_eq_zero.mp h)';assert a.count(old)==1 and a.replace(old,new)==b
up=D/'reviews/nine-sharing-sign26-zero-bridge-retry01-failure-frontier-independent/check.py';assert H(up)=='2bbbc7fce0790848bf17cf527ea9be6a7780a5dc16ce97be5cdc770f2e92313f';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'same bridge statements; helper simpa uses standard simplifier to address unreduced Fin applications; no Lean replay'},sort_keys=True,indent=2))
