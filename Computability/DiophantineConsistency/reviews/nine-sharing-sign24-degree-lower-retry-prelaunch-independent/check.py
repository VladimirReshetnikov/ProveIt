#!/usr/bin/env python3
"""Review proposed leading residual and diagonal degree stages; do not run Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2]
packet=root/'research/nine-sharing-sign24-degree-lower-retry-check'
draft=root/'research/nine-sharing-sign24-degree-lower-retry-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=packet/'source-manifest.json'
assert sha(manifest)=='f75d068feeed2ddf21aff69b4602c706033f744c7948c61db03ec6d071aaae35'
rows=json.loads(manifest.read_text())['rows']; names=['Sign24LeadingN0','Sign24DiagonalDegree']
imports=[['DiophantineConsistency.Sign24CurrentExpressionDef'],['DiophantineConsistency.Sign24LeadingN0']]
texts=[]
for row,name,expected in zip(rows,names,imports):
 src=packet/'src/DiophantineConsistency'/(name+'.lean')
 assert row['module']=='DiophantineConsistency.'+name and sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==expected
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text())
 texts.append(src.read_text())
assert len(rows)==2
assert '((SharingSeed24Octic.remainingResiduals p).drop 6).head? = some n0' in texts[0]
assert 'if i = 0 then 1 else if i = 16 ∨ i = 17 then t else 0' in texts[0]
assert 'n0.evalRing (axis t) = -t^4 - 2*t^2 - 1' in texts[0]
assert 'if i = 15 ∨ i = 16 then X 0 else 0' in texts[1]
assert '(diagonal p).totalDegree ≤ p.totalDegree' in texts[1]
old=root/'research/nine-sharing-sign24-degree-lower-check'
assert (old/'src/DiophantineConsistency/Sign24DiagonalDegree.lean').read_text()==texts[1]
oldtext=(old/'src/DiophantineConsistency/Sign24LeadingN0.lean').read_text()
for i,val in [(20,'0'),(16,'t'),(17,'t'),(11,'0'),(12,'0')]:
 assert f'have h{i} : axis t ({i} : Fin 25) = {val} := by rfl' in texts[0]
assert oldtext.split('theorem n0_axis')[0]==texts[0].split('theorem n0_axis')[0]
oldrunner=(old/'run.py').read_text()
assert oldrunner.replace('/tmp/nine-sharing-sign24-degree-lower-20261109','/tmp/nine-sharing-sign24-degree-lower-retry-20261109').replace('472c89aa701f5945bd4e1e3c03754350d3a47f78e16a1c457f9f41ae6203aec6','f75d068feeed2ddf21aff69b4602c706033f744c7948c61db03ec6d071aaae35').replace('Bounded sign24 degree lower-bound steps','Bounded sign24 degree lower Fin-index retry').replace('PASS sign24 degree lower-bound steps','PASS sign24 degree lower Fin-index retry') == (packet/'run.py').read_text()
runner=packet/'run.py'; assert sha(runner)=='f4517edf0356737bc0a09294a20868f8be8eac8cf91bc574f6eb92f4cdc2c0fc'
r=runner.read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert "need(not OUT.exists(),'output exists')" in r and '5_000_000_000' in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(survey.stdout)['status']=='PASS'
preflight=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert preflight.returncode==0 and not preflight.stderr and json.loads(preflight.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'proposed N0 identification and diagonal degree bound; not an exact degree proof'},sort_keys=True,indent=2))
