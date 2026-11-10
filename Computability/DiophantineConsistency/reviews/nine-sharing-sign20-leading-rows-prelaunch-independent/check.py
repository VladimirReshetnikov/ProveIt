#!/usr/bin/env python3
"""Review proposed leading-coefficient ingredients without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign20-leading-rows-check';draft=research/'nine-sharing-sign20-leading-rows-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='691b4b33a35f368799af5ed89b81cf2314d3306519d393d5744e0796ecdb839d'
rows=json.loads(m.read_text())['rows'];names=['Sign20LeadingRows','Sign20DiagonalDegree','Sign20AxisResidualDegree'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==(['DiophantineConsistency.Sign20CurrentExpressionDef'] if i==0 else ['DiophantineConsistency.Sign20LeadingRows'])
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
assert 'if i = 1 ∨ i = 9 ∨ i = 11 ∨ i = 15 then 1 else 0' in texts[2]
assert '(hn : e ≠ n0 p) (hd : e ≠ dc2 p)' in texts[2]
assert '(e.evalRing axisPoly).totalDegree ≤ 6' in texts[2]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2
assert texts[2].split('rcases he with',1)[1].split('all_goals',1)[0].count('rfl')==10
assert 'drop 1).head? = some (dc2 p)' in texts[0] and 'drop 3).head? = some (n0 p)' in texts[0]
assert 'theorem dc2_axis {R : Type*} [CommRing R] (p : Fin 4 → ℤ)' in texts[0]
assert 'theorem n0_axis {R : Type*} [CommRing R] (p : Fin 4 → ℤ)' in texts[0]
assert all('maxHeartbeats' not in texts[i] for i in [0,1])
subprocess.run([sys.executable,'-I','-S','-B',str(draft/'axis-arithmetic.py')],check=True,capture_output=True,timeout=30)
runner=packet/'run.py';assert sha(runner)=='064e2b144d237b571580264cc5bd597dae379020854cca14e53c4af22ed8d592';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "elif local=='Sign20CurrentExpressionDef':" in r and "elif local in ('Sign20LeadingRows','Sign20DiagonalDegree'):" in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(survey.stdout)['status']=='PASS'
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'two port-dependent leading-row identities and weighted-degree ingredients only, no full lower bound or external binding'},sort_keys=True,indent=2))
