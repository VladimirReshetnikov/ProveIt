#!/usr/bin/env python3
"""Review compositional shared degree probe and provider routes without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign17-degree-shared-probe-check';draft=research/'nine-sharing-sign17-degree-shared-probe-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();m=p/'source-manifest.json';assert sha(m)=='148cc51861671d288232f1fe377012b32ef97c93bbbe57dd827b2f5431a6ba71';rows=json.loads(m.read_text())['rows'];names=['Sign17SyntaxDegree','Sign17SharedDegree00'];assert [e['module'] for e in rows]==['DiophantineConsistency.'+n for n in names];texts=[]
for i,(e,n) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();texts.append(s);assert sha(src)==sha(draft/(n+'.lean'))==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.'+('Sign17CurrentExpressionDef' if i==0 else 'Sign17SyntaxDegree')] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
assert 'e.toPolynomial.totalDegree ≤ degree e' in texts[0]
for i,n in enumerate((1,2,2,1,1)):assert f'theorem shared{i:02}_degree (p : Fin 4 → ℤ) : degree (shared{i:02} p) ≤ {n}' in texts[1]
assert texts[1].count('set_option maxHeartbeats 4000000 in')==5 and 'attribute [local irreducible] shared00' in texts[1]
runner=p/'run.py';assert sha(runner)=='3649fd4dfd0b1de27ff9c8c748803c90261b95a778c80aae77b211923455d839';r=runner.read_text();assert "if local=='Sign17CurrentExpressionDef':" in r and "elif local in ('Sign17SyntaxDegree',):" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-expression-eval-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'five shared-node syntactic upper bound probes; no Lean result or full degree bound'},indent=2,sort_keys=True))
