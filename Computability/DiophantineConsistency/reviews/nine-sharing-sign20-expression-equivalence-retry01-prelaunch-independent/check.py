#!/usr/bin/env python3
"""Review all corrected post-preflight provider routes without invoking Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';old=research/'nine-sharing-sign20-expression-equivalence-check';packet=research/'nine-sharing-sign20-expression-equivalence-retry01-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ('source-manifest.json','evaluator-union-survey.py','union.json','src/DiophantineConsistency/Sign20ExpressionEquivalence.lean'):
 assert (old/name).read_bytes()==(packet/name).read_bytes()
s=(old/'run.py').read_text();r=(packet/'run.py').read_text()
for a,b,n in [('/tmp/nine-sharing-sign20-expression-equivalence-check-20261109','/tmp/nine-sharing-sign20-expression-equivalence-retry01-check-20261109',1),("for family in ('24','25'):","for family in ('20','21'):",2),("('Sign20CurrentExpressionEval','Sign25CurrentExpressionEval')","('Sign20CurrentExpressionEval','Sign21CurrentExpressionEval')",1),("family='24' if local=='Sign20CurrentExpressionEval' else '25'","family='20' if local=='Sign20CurrentExpressionEval' else '21'",1)]:
 assert s.count(a)==n;s=s.replace(a,b)
assert s==r and r.count("for family in ('20','21'):")==2
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r and "need(not OUT.exists(),'output exists')" in r
u=json.loads((packet/'union.json').read_text());assert set(u)=={'20','21'}
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-expression-equivalence-failure-independent/check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(packet/'run.py'),'scope':'corrected both injection loops and direct evaluator route; no Lean result'},sort_keys=True,indent=2))
