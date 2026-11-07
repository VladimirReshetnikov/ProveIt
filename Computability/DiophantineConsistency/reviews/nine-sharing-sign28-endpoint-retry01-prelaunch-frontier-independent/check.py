#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-endpoint-retry01';OLD=D/'research/nine-sharing-sign28-endpoint-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'0a40521beb44e494003b5f2fce44c2de6542439209852e0a1f33e41008cf93b8','source-manifest.json':'f3fc6942abff60f424e467f4b0b467128b18b9fb505f5eb60c19839b7982c692','framework-survey.py':'20bceb0b7631d230eac91deb2778690edb90a6d72c4af61a07e2bc4edc97c9a6'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign28DirectNative','Sign28DirectStandard','Sign28DirectTranslated'];assert [r['module'].split('.')[-1] for r in m]==names
ss=[]
for r,n in zip(m,names):
 f=P/'src/DiophantineConsistency'/f'{n}.lean';s=f.read_text();ss.append(s);assert H(f)==r['source_sha256']
for i in (1,2):assert ss[i]==(OLD/'src/DiophantineConsistency'/f'{names[i]}.lean').read_text()
old=(OLD/'src/DiophantineConsistency/Sign28DirectNative.lean').read_text();new='attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta\n  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix\n  Sign28CurrentExpression.expression\n\n';assert old.replace('abbrev expression :=',new+'abbrev expression :=')==ss[0]
f=D/'reviews/nine-sharing-sign28-endpoint-failure-frontier-independent/check.py';assert H(f)=='afb8b1c756882d7a6363098aa33d833f2f8f698e9bc7230064175c46b85eda8c';subprocess.run([sys.executable,'-I','-S','-B',str(f)],check=True,capture_output=True,timeout=60)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':3,'scope':'same proposed native/standard/translated Fin28 endpoints; memory cause unknown'},sort_keys=True,indent=2))
