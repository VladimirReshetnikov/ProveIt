#!/usr/bin/env python3
"""Review source and evaluator union, including both post-preflight routes."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign17-expression-equivalence-check';draft=research/'nine-sharing-sign17-expression-equivalence-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=packet/'src/DiophantineConsistency/Sign17ExpressionEquivalence.lean';entry,=json.loads((packet/'source-manifest.json').read_text())['rows'];assert entry['module']=='DiophantineConsistency.Sign17ExpressionEquivalence' and sha(src)==sha(draft/'Sign17ExpressionEquivalence.lean')==entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==entry['imports']==['DiophantineConsistency.Sign17CurrentExpressionEval','DiophantineConsistency.Sign18CurrentExpressionEval','DiophantineConsistency.Sign17CurrentSeedIff']
s=src.read_text();assert '∃ w : Fin 17 → V, InternalZero Sign17CurrentExpression.expression w' in s and '∃ w : Fin 18 → V, InternalZero Sign18CurrentExpression.expression w' in s
assert 'Sign17CurrentSeedIff.exists_same_input (1 : V)' in s and all(x in s for x in ('Sign17CurrentExpression.eval_expression','Sign18CurrentExpression.eval_expression','Fin.cons_self_tail v','Fin.tail v'))
runner=packet/'run.py';assert sha(runner)=='74c234599fd072c20676d21db31ee2768e0604942c7122a01f51a94de9cea0c0';r=runner.read_text();assert r.count("for family in ('17','18'):")==2
assert "elif local in ('Sign17CurrentExpressionEval','Sign18CurrentExpressionEval'):" in r and "family='17' if local=='Sign17CurrentExpressionEval' else '18'" in r and "if local=='Sign17CurrentSeedIff':" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
assert set(json.loads((packet/'union.json').read_text()))=={'17','18'}
for review in ('nine-sharing-sign17-current-iff-retry01-terminal-independent','nine-sharing-sign17-expression-eval-terminal-independent','nine-sharing-sign18-expression-eval-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'Fin17/Fin18 current-port model zero iff source and provider routes; no Lean result or endpoint'},indent=2,sort_keys=True))
