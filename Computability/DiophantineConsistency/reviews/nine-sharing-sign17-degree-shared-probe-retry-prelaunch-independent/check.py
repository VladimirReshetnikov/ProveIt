#!/usr/bin/env python3
"""Review compositional shared degree probe and provider routes without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign17-degree-shared-probe-retry-check';draft=research/'nine-sharing-sign17-degree-shared-probe-retry-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();m=p/'source-manifest.json';assert sha(m)=='a90ffbef2adea2c8dd1c1b61589bd7b48aa3d74b769fe2284c0fb8a135b72fc3';rows=json.loads(m.read_text())['rows'];names=['Sign17SyntaxDegree','Sign17SharedDegree00'];assert [e['module'] for e in rows]==['DiophantineConsistency.'+n for n in names];texts=[]
for i,(e,n) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();texts.append(s);assert sha(src)==sha(draft/(n+'.lean'))==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.'+('Sign17CurrentExpressionDef' if i==0 else 'Sign17SyntaxDegree')] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
assert 'e.toPolynomial.totalDegree ≤ degree e' in texts[0]
for i,n in enumerate((1,2,2,1,1)):assert f'theorem shared{i:02}_degree (p : Fin 4 → ℤ) : degree (shared{i:02} p) ≤ {n}' in texts[1]
assert texts[1].count('set_option maxHeartbeats 4000000 in')==5 and 'attribute [local irreducible] shared00' in texts[1]
prior=research/'nine-sharing-sign17-degree-shared-probe-draft'
assert texts[0] == (prior/'Sign17SyntaxDegree.lean').read_text()
old=(prior/'Sign17SharedDegree00.lean').read_text()
a='  unfold shared03\n  simp only [degree]\n  omega\n'
b='  change 1 ≤ 1\n  decide\n'
assert old.count(a)==1 and old.replace(a,b)==texts[1]
failure=root/'reviews/nine-sharing-sign17-degree-shared-probe-failure-independent/check.py'
assert sha(failure)=='a9622ce1af6f7b8e95ae1380e3b98571e2e5e6af4da41963f3f15aac42d87927'
subprocess.run([sys.executable,'-I','-S','-B',str(failure)],check=True,capture_output=True,timeout=180)
runner=p/'run.py';assert sha(runner)=='d8598e5afdd77583685d0af15f020f6ad6854f5b2c82cd7c39e9500b3c6adaee';r=runner.read_text();assert "if local=='Sign17CurrentExpressionDef':" in r and "elif local in ('Sign17SyntaxDegree',):" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-expression-eval-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'five shared-node syntactic upper bound probes; no Lean result or full degree bound'},indent=2,sort_keys=True))
