#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-seed-current-source-retry01';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'ec60302e602d74024aae952d676b545b5aad4aa8804e9e8e0249b51db9309f1b','provider_survey.py':'890e2f01f9c12cff49330838817c84c572f569313579202d6a12599b460b99e2','source-manifest.json':'1c67e01441d652f53d90fecc5af3081e948e65b22a508ea9262e5539814e0b82'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33SourceFourCasts','fff4bff1bb1240f9bb27cd2c0c7c42bdacd074135403d05a2667547b890a5b2b',['Sign33SeedSource','Norm38FourVariablePorts']),('Sign33CurrentSeedSourceRetry','ff092ba634c737556f816ed8b690be77b1934bcb33cbdf078f604a480dcc525e',['Sign33SourceFourCasts','Norm38CurrentPort0','Norm38CurrentPort1','Norm38CurrentPort2','Norm38CurrentPort3'])];assert len(rows)==2
for row,(n,h,imports) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==h==row['source_sha256'] and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert '(Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1' in s
w=(p/'src/DiophantineConsistency/Sign33SourceFourCasts.lean').read_text();c=(p/'src/DiophantineConsistency/Sign33CurrentSeedSourceRetry.lean').read_text();old=(d/'research/nine-sharing-sign33-seed-current-source-check/src/DiophantineConsistency/Sign33CurrentSeedSource.lean').read_text()
for i,x in enumerate('bklh'):assert f'(h{i} : ((CurrentWindowCarry2011.ports {i} : ℤ) : DiffRing V) = ι {x})' in w
assert 'Norm38FourVariablePorts.naturalPorts b k l h) v h0 h1 h2 h3 hz' in w and re.findall(r'Norm38CurrentPorts\.port(\d)',c)==list('0123') and '(CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ)' in c
for z in (c,old):assert '(hz : InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) v)' in z and 'InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)' in z
survey=(p/'provider_survey.py').read_text();assert "d['rows'][1]['module']=='Sign33CurrentSeedSource' and d['rows'][1]['compile']['exit']==-6" in survey and "d['rows'][5]['module']=='Norm38CurrentPortCasts' and d['rows'][5]['compile']['exit']==1" in survey and "for row in d['rows'][:count]:" in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'factored current seed-to-source retry source/provider review; no Lean replay'},indent=2,sort_keys=True))
