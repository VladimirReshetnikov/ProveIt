#!/usr/bin/env python3
"""Review proposed leading-coefficient ingredients without invoking Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign23-leading-coeff-check';draft=research/'nine-sharing-sign23-leading-coeff-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=packet/'source-manifest.json';assert sha(m)=='12d8dd6fb6545c45ed3d275cb3340628f1117c6f85da84c7b2acdc46745e106c'
rows=json.loads(m.read_text())['rows'];names=['Sign23LeadingRows','Sign23DiagonalDegree','Sign23AxisResidualDegree','Sign23SquareCoeffs'];assert [r['module'] for r in rows]==['DiophantineConsistency.'+n for n in names]
texts=[]
for i,(row,name) in enumerate(zip(rows,names)):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256']
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==row['imports']==(['DiophantineConsistency.Sign23CurrentExpressionDef'] if i==0 else ['DiophantineConsistency.Sign23LeadingRows'])
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text());texts.append(src.read_text())
assert 'if i = 16 ∨ i = 17 then 1 else 0' in texts[2]
assert '(he : e ∈ SharingSeed23Octic.remainingResiduals p) (hn : e ≠ n0) (hd : e ≠ dc2)' in texts[2]
assert '(e.evalRing axisPoly).totalDegree ≤ 2' in texts[2]
assert texts[2].count('set_option maxHeartbeats 4000000 in')==2
assert texts[2].split('rcases he with',1)[1].split('all_goals',1)[0].count('rfl')==13
assert 'drop 5).head? = some n0' in texts[0] and 'drop 3).head? = some dc2' in texts[0]
assert 'dc2.evalRing (axis t) = -t^4 - 6*t^3 - 12*t^2 - 10*t - 3' in texts[0]
assert 'theorem n0_square_coeff' in texts[3] and 'theorem dc2_square_coeff' in texts[3]
assert 'MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 8)' in texts[3] and 'ℤ) = 1' in texts[3]
assert all('maxHeartbeats' not in texts[i] for i in [0,1,3])
runner=packet/'run.py';assert sha(runner)=='9d9bb109ccce88e94a968e13362ed1a04d4a5c631ca270905112f5ddb1b27699';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r
assert "need(not OUT.exists(),'output exists')" in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign23-concrete-polynomial-bridge-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(survey.stdout)['status']=='PASS'
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'two-leading-row coefficient ingredients only, no full lower bound or external binding'},sort_keys=True,indent=2))
