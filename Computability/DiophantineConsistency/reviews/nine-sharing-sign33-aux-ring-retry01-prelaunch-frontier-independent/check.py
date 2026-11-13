import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-aux-ring-retry01';old=D/'research/nine-sharing-sign33-aux-ring-check'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'run.py':'3b12db4c61cbcb87aec11f6350e8f3dd504f30e2e4d50810794b6c0eb86f3431','provider_survey.py':'5647fa1bfb1ebca431e5c4ac15beeff475263fbb7ff426b1d0d9508c3e0fcd32','source-manifest.json':'aa5bb677ecfde6f5086fd52f6a86128844bb5c3286b132105b3cc31a474e4b0d','src/DiophantineConsistency/Sign33AuxRing.lean':'fd4e20bc73bf0ea3fce0efd8bcd85fe0f34930306ca0eca81c6e743355f0da5d'}
for k,h in pins.items():assert sha(p/k)==h,k
before=(old/'src/DiophantineConsistency/Sign33AuxRing.lean').read_text();after=(p/'src/DiophantineConsistency/Sign33AuxRing.lean').read_text();a='    linear_combination he';b='    nlinarith [he]';assert before.count(a)==1 and before.replace(a,b)==after
assert sha(old/'provider_survey.py')==sha(p/'provider_survey.py') and sha(old/'attempt01/state.json')=='04db4f4557dfa2b196268b1cd03125693d459fcfe09ccab56d2b2712ad027116' and sha(old/'attempt01/Sign33AuxRing-compile.txt')=='a13a5b8e1e270ec179ba4d7ade6542ce3a6594dbb6f379c1f638cb714ea0c0e6'
imports=json.loads((p/'source-manifest.json').read_text())['rows'][0]['imports'];assert imports==['DiophantineConsistency.Sign33AbsDiffSquare','Sign33OrderedRing'];s=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],timeout=60));assert s['status']=='PASS_POINT_PRODUCER_SURVEY' and all(k in s['selected'] for k in imports) and 'DiophantineConsistency/Sign33AuxRing.olean' not in s['links'];assert s['selected'][imports[0]]['sha256']=='f990f1d2f77896b6d52dab63e31e69a0af763c894c5a16d44dc7bb046bce3e65' and s['selected'][imports[1]]['sha256']=='04d0c914a6810e0e449d661e678a20422e500a6cc44e8467b50a2f30e3358c5a'
r=json.loads(subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],timeout=60));assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['stage_count']==1
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','pins':pins,'direct_producers':{k:s['selected'][k] for k in imports},'scope':'One tactic-only correction; no Lean sign theorem or source-zero bridge.'},indent=2,sort_keys=True))
