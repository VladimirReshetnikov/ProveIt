#!/usr/bin/env python3
"""Review source and evaluator union, including both post-preflight routes."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign19-expression-equivalence-check';draft=research/'nine-sharing-sign19-expression-equivalence-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=packet/'src/DiophantineConsistency/Sign19ExpressionEquivalence.lean';entry,=json.loads((packet/'source-manifest.json').read_text())['rows'];assert entry['module']=='DiophantineConsistency.Sign19ExpressionEquivalence' and sha(src)==sha(draft/'Sign19ExpressionEquivalence.lean')==entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==entry['imports']==['DiophantineConsistency.Sign19CurrentExpressionEval','DiophantineConsistency.Sign20CurrentExpressionEval','DiophantineConsistency.Sign19CurrentSeedIff']
s=src.read_text();assert '∃ w : Fin 19 → V, InternalZero Sign19CurrentExpression.expression w' in s and '∃ w : Fin 20 → V, InternalZero Sign20CurrentExpression.expression w' in s
assert 'Sign19CurrentSeedIff.exists_same_input (1 : V)' in s and all(x in s for x in ('Sign19CurrentExpression.eval_expression','Sign20CurrentExpression.eval_expression','Fin.cons_self_tail v','Fin.tail v'))
runner=packet/'run.py';assert sha(runner)=='fb172815ed408250a6688c79595fa20a55f267df621d61bbd4998bf6a223eacb';r=runner.read_text();assert r.count("for family in ('19','20'):")==2
assert "elif local in ('Sign19CurrentExpressionEval','Sign20CurrentExpressionEval'):" in r and "family='19' if local=='Sign19CurrentExpressionEval' else '20'" in r and "if local=='Sign19CurrentSeedIff':" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
assert set(json.loads((packet/'union.json').read_text()))=={'19','20'}
for review in ('nine-sharing-sign19-current-iff-terminal-independent','nine-sharing-sign19-expression-eval-terminal-independent','nine-sharing-sign20-expression-eval-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'Fin19/Fin20 current-port model zero iff source and provider routes; no Lean result or endpoint'},indent=2,sort_keys=True))
