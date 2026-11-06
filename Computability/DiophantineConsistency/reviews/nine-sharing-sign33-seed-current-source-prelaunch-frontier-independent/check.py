#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-seed-current-source-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'e90f600d9d7c5dbc1a23b46973a1d7efcd802b6d1dc29ccf9d918b4820bc20b0','provider_survey.py':'feed5e3a65390fcdba700dfd494a0fda65846f5db7db04e406cd9877023c9b60','source-manifest.json':'4e3dd7f65aae2e161239a85b6bfdfde5a30634f61f46d771b860f3112e4df0d1'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33SeedSource','52d26b985ccebc8d055d3ce250cc6885b8346607e4bc0ac96c92eaa48ee050ef',['Sign33ResidualIff','Sign33AllCutsSource']),('Sign33CurrentSeedSource','77b0624fb62992bbeb9c8d1ad219e225ba33c7dc90b7f072bb33bc118debca6b',['Sign33SeedSource','Norm38CurrentPort0','Norm38CurrentPort1','Norm38CurrentPort2','Norm38CurrentPort3'])];assert len(rows)==2
for row,(n,h,imports) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==h==row['source_sha256'] and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert '(Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1' in s
first=(p/'src/DiophantineConsistency/Sign33SeedSource.lean').read_text();second=(p/'src/DiophantineConsistency/Sign33CurrentSeedSource.lean').read_text()
assert 'seed_zero_iff_all_cuts p ports v hp0 hp1 hp2 hp3).mp hz' in first and 'allcuts_imply_source_zero p ports v hp0 hp1 hp2 hp3 hc' in first
assert 'SharingSeed33.seed CurrentWindowCarry2011.ports' in second and 'ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports' in second and '(Norm38CurrentPorts.naturalPorts (V := V)) v' in second
assert re.findall(r'Norm38CurrentPorts\.port(\d)',second)==list('0123')
base=(d/'research/nine-sharing-norm38-current-ports-split-draft/src/DiophantineConsistency/Norm38CurrentPortBase.lean').read_text();assert '(CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ)' in base
for i in range(4):assert f'theorem port{i}' in (d/f'research/nine-sharing-norm38-current-ports-split-draft/src/DiophantineConsistency/Norm38CurrentPort{i}.lean').read_text()
survey=(p/'provider_survey.py').read_text();assert "d['rows'][5]['module']=='Norm38CurrentPortCasts' and d['rows'][5]['compile']['exit']==1" in survey and "for row in d['rows'][:count]:" in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'generic and current seed-zero to shifted source zero only; no Lean replay'},indent=2,sort_keys=True))
