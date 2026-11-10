#!/usr/bin/env python3
"""Review proposed leading-coefficient ingredients without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign21-leading-coeff-check';draft=research/'nine-sharing-sign21-leading-coeff-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='76b736c6cb3b0cc4ecc2b38f2626a9158b6a2a4cc362d0f00d4da12a65582f59'
rows=json.loads(m.read_text())['rows'];names=['Sign21LeadingRow','Sign21DiagonalDegree','Sign21AxisResidualDegree'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==(['DiophantineConsistency.Sign21CurrentExpressionDef'] if i==0 else ['DiophantineConsistency.Sign21LeadingRow'])
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
assert 'if i = 6 ∨ i = 17 ∨ i = 21 then 1 else 0' in texts[2]
assert '(he : e ∈ SharingSeed21Degree14.remainingResiduals p) (hne : e ≠ leading)' in texts[2]
assert '(e.evalRing axisPoly).totalDegree ≤ 6' in texts[2]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2
assert texts[2].split('rcases he with',1)[1].split('all_goals',1)[0].count('rfl')==11
assert 'drop 9).head? = some leading' in texts[0]
assert 'leading.evalRing (axis t) = -t^7 - 6*t^6 - 13*t^5 - 12*t^4 - 4*t^3' in texts[0]
assert all('maxHeartbeats' not in texts[i] for i in [0,1])
subprocess.run([sys.executable,'-I','-S','-B',str(draft/'axis-arithmetic.py')],check=True,capture_output=True,timeout=30)
runner=packet/'run.py';assert sha(runner)=='94ec42b267bd9240a0658a61154a57d7635e766fc2585657d6d8d145cc47ea8e';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign21-concrete-polynomial-bridge-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(survey.stdout)['status']=='PASS'
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'single-leading-row identity and weighted-degree ingredients only, no full lower bound or external binding'},sort_keys=True,indent=2))
