#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-source-seed-casts-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'dfa3809506d9c3b0562af28cee4796ac3ec23ed7a84c05b84b1b5b2cae9b9b0f','provider_survey.py':'d6123c3a0cc0d1ccb7e849d9103d703fdf276e055cd957fb074bdb89a28f243a','source-manifest.json':'d563d11975f149050d4ebb210a17bc6cd7ea4fbe60ceab6ccf88dc35e9ee657f'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33SourceSeedFourCasts','7c37e692fc2fc5c9f395658d2b211bc81ab3e4d76067e2fa2f971bd663527076',['Sign33CurrentSourceSeed','Norm38FourVariablePorts']),('Sign33CurrentSourceSeedCastFree','5ba4414f41f109effdfab3e572084ce45ad4be0f74fc5224f1479ee9d7de413e',['Sign33SourceSeedFourCasts','Norm38CurrentPort0','Norm38CurrentPort1','Norm38CurrentPort2','Norm38CurrentPort3'])];assert len(rows)==2
for row,(n,h,imports) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports] and s.count('#print axioms ')==1
a=(p/'src/DiophantineConsistency/Sign33SourceSeedFourCasts.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33CurrentSourceSeedCastFree.lean').read_text()
for x in ['(h0 :','(h1 :','(h2 :','(h3 :','Norm38FourVariablePorts.naturalPorts b k l h','casts_of_four CurrentWindowCarry2011.ports b k l h h0 h1 h2 h3','InternalZero ObjectCurrentEquation2011.naturalExpression u','Fin.cons (1 : V) w']:assert x in a
for x in ['(CurrentMasks2011.beta : V) (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)','CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ','Norm38CurrentPorts.port0 Norm38CurrentPorts.port1','Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hz','InternalZero ObjectCurrentEquation2011.naturalExpression u','Fin.cons (1 : V) w']:assert x in b
survey=(p/'provider_survey.py').read_text();assert '2d3716f0525be2264e28ad8b6715342a4fa29bf8de6130520d2c5dfc8a1fdbe7' in survey
for n in ['Norm38CurrentPort0','Norm38CurrentPort1','Norm38CurrentPort2','Norm38CurrentPort3']:assert n in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'concrete port specialization of source to 33 seed; no Lean replay'},indent=2,sort_keys=True))
