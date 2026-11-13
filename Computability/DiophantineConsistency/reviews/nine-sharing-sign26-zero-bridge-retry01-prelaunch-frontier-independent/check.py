#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-zero-bridge-retry01';O=D/'research/nine-sharing-sign26-zero-bridge-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'201f274c9b168abd0f1be634089b8635da19019d215486727f851a240e843aa9','source-manifest.json':'174ae228d7c9a064d718c92546b9d751d5c6a92976525548146c27cfec4ff08c','provider-union-survey.py':'2bd3b58f6934cba8ddedf1abe690a88ecf080c812b1fad11772026ca4d0f9780','union.json':'a7a5de9714fe786dda5eff6d046d97148660fc3368c2bac5c07388739aea5cb3','src/DiophantineConsistency/Sign26ReverseGap.lean':'5f0e45f99c49bea6cfe5f578f83baac4da871fad09503c91806b8ffa92f32c19','src/DiophantineConsistency/Sign26ReverseBridgeRetry.lean':'9a419a7ed8592b083bef3040804b7ce426e3fc2093b40a238eb1d0b94d253334'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign26CoordinateDrop','Sign26ForwardBridge','Sign26ReverseGap','Sign26ReverseBridgeRetry']
for e in m:
 n=e['module'].split('.')[-1];assert H(P/'src/DiophantineConsistency'/f'{n}.lean')==e['source_sha256']
for n in ['Sign26CoordinateDrop','Sign26ForwardBridge']:assert (P/'src/DiophantineConsistency'/f'{n}.lean').read_bytes()==(O/'src/DiophantineConsistency'/f'{n}.lean').read_bytes()
old=(O/'src/DiophantineConsistency/Sign26ReverseBridge.lean').read_text();new=(P/'src/DiophantineConsistency/Sign26ReverseBridgeRetry.lean').read_text();a='''  have hge := (internalZero_iff _ _).mp hgold
  simp only [Sign26CongruenceCuts.oldGap, Sign26CongruenceCuts.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at hge
  have hgap : ι (v 22) = Sign26CongruenceCuts.ringGap p (drop v) := by
    simpa only [Sign26CongruenceCuts.ringGap] using (sub_eq_zero.mp hge)''';b='''  have hgap : ι (v 22) = Sign26CongruenceCuts.ringGap p (drop v) :=
    reverseGap p (drop v) (v 22) hgold''';assert a in old and old.replace('import DiophantineConsistency.Sign26ForwardBridge','import DiophantineConsistency.Sign26ReverseGap',1).replace(a,b,1)==new
h=(P/'src/DiophantineConsistency/Sign26ReverseGap.lean').read_text();assert all(x in h for x in ['(v : Fin 27 → V) (gap : V)','InternalZero (Sign26CongruenceCuts.oldGap p) (Sign26CongruenceCuts.lift gap v)','ι gap = Sign26CongruenceCuts.ringGap p v','sub_eq_zero.mp h'])
up=D/'reviews/nine-sharing-sign26-zero-bridge-failure-frontier-independent/check.py';assert H(up)=='01c1a55e6aedd15028d6589d59dad53b508b6817223a83790dc02f98fce04d12';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'same conditional forward/backward statements; abstract reverse-gap helper factors failed proof; no Lean replay'},sort_keys=True,indent=2))
