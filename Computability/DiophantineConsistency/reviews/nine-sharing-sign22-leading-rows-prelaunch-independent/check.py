#!/usr/bin/env python3
"""Review proposed leading-coefficient ingredients without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign22-leading-rows-check';draft=research/'nine-sharing-sign22-leading-rows-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='c8c68a826d40d61f3b93393e68ff917ee5ff1ef26ae5655373652b24efbb6d77'
rows=json.loads(m.read_text())['rows'];names=['Sign22LeadingRows','Sign22DiagonalDegree','Sign22AxisResidualDegree'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==(['DiophantineConsistency.Sign22CurrentExpressionDef'] if i==0 else ['DiophantineConsistency.Sign22LeadingRows'])
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
assert 'if i = 11 ∨ i = 12 ∨ i = 15 ∨ i = 16 then 1 else 0' in texts[2]
assert '(he : e ∈ SharingSeed22Dodecic.remainingResiduals p) (hn : e ≠ n0) (hd : e ≠ dc2)' in texts[2]
assert '(e.evalRing axisPoly).totalDegree ≤ 4' in texts[2]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2
assert texts[2].split('rcases he with',1)[1].split('all_goals',1)[0].count('rfl')==12
assert 'drop 4).head? = some n0' in texts[0] and 'drop 2).head? = some dc2' in texts[0]
assert 'dc2.evalRing (axis t) = -(4*t^2 + 8*t + 3) * (2*t^2 + 3*t + 1)^2' in texts[0]
assert all('maxHeartbeats' not in texts[i] for i in [0,1])
runner=packet/'run.py';assert sha(runner)=='6fdebc810bfb7ac50aa577f8f29c064885c5e4f8086bf2aca187393e91ebff98';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign22-concrete-polynomial-bridge-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(survey.stdout)['status']=='PASS'
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'two-leading-row identities and weighted-degree ingredients only, no full lower bound or external binding'},sort_keys=True,indent=2))
