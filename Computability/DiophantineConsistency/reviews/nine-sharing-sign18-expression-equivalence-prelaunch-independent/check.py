#!/usr/bin/env python3
"""Review source and evaluator union, including both post-preflight routes."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign18-expression-equivalence-check';draft=research/'nine-sharing-sign18-expression-equivalence-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=packet/'src/DiophantineConsistency/Sign18ExpressionEquivalence.lean';entry,=json.loads((packet/'source-manifest.json').read_text())['rows'];assert entry['module']=='DiophantineConsistency.Sign18ExpressionEquivalence' and sha(src)==sha(draft/'Sign18ExpressionEquivalence.lean')==entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==entry['imports']==['DiophantineConsistency.Sign18CurrentExpressionEval','DiophantineConsistency.Sign19CurrentExpressionEval','DiophantineConsistency.Sign18CurrentSeedIff']
s=src.read_text();assert '∃ w : Fin 18 → V, InternalZero Sign18CurrentExpression.expression w' in s and '∃ w : Fin 19 → V, InternalZero Sign19CurrentExpression.expression w' in s
assert 'Sign18CurrentSeedIff.exists_same_input (1 : V)' in s and all(x in s for x in ('Sign18CurrentExpression.eval_expression','Sign19CurrentExpression.eval_expression','Fin.cons_self_tail v','Fin.tail v'))
runner=packet/'run.py';assert sha(runner)=='eff1139d30fce6ae0793cf59d95290be7c1ae33d40519dadd4a5d10d3405393f';r=runner.read_text();assert r.count("for family in ('18','19'):")==2
assert "elif local in ('Sign18CurrentExpressionEval','Sign19CurrentExpressionEval'):" in r and "family='18' if local=='Sign18CurrentExpressionEval' else '19'" in r and "if local=='Sign18CurrentSeedIff':" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
assert set(json.loads((packet/'union.json').read_text()))=={'18','19'}
for review in ('nine-sharing-sign18-current-iff-terminal-independent','nine-sharing-sign18-expression-eval-terminal-independent','nine-sharing-sign19-expression-eval-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'Fin18/Fin19 current-port model zero iff source and provider routes; no Lean result or endpoint'},indent=2,sort_keys=True))
