#!/usr/bin/env python3
"""Prepare the missing-import retry without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-dag-expression-check'
check = here.parent / 'current14-carrier65-dag-expression-retry-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65DAGExpression.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65DAGExpression',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
old = (previous / 'run.py').read_text()
old = old.replace("OUT=Path('/tmp/current14-carrier65-dag-expression-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-dag-expression-retry-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-dag-expression-draft/Current14Carrier65DAGExpression.lean'",
                  "draft=D/'research/current14-carrier65-dag-expression-retry-draft/Current14Carrier65DAGExpression.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
state = previous / 'attempt01/state.json'
outer = previous / 'attempt01/outer-result.json'
audit = d / 'reviews/current14-carrier65-dag-expression-failure-independent/check.py'
live = Path('/tmp/current14-carrier65-dag-expression-20261110')
weighted = Path('/tmp/current14-carrier65-dag-value-congr-diagnostic-20261110/lib/DiophantineConsistency/WeightedExpressionDegree.olean')
extra = f'''failed_state=D/'research/current14-carrier65-dag-expression-check/attempt01/state.json'
failed_outer=failed_state.parent/'outer-result.json'
failed_audit=D/'reviews/current14-carrier65-dag-expression-failure-independent/check.py'
need(sha(failed_state)=='{sha(state)}' and json.loads(failed_state.read_text())['status']=='FAILED','expression parent failed')
need(sha(failed_outer)=='{sha(outer)}' and json.loads(failed_outer.read_text())['outer_exit_code']==1,'expression parent outer')
need(sha(failed_audit)=='{sha(audit)}','expression failure audit')
need(sha(Path({str(live / 'Current14Carrier65DAGExpression-compile.txt')!r}))=='{sha(live / 'Current14Carrier65DAGExpression-compile.txt')}','expression failure log')
need(not Path({str(live / 'lib/DiophantineConsistency/Current14Carrier65DAGExpression.olean')!r}).exists(),'expression parent object absent')
weighted_pin={{'realpath':{str(weighted.resolve())!r},'sha256':{sha(weighted)!r}}}
weighted=BASE/'lib/DiophantineConsistency/WeightedExpressionDegree.olean'
need(weighted.is_file() and str(weighted.resolve())==weighted_pin['realpath'] and sha(weighted)==weighted_pin['sha256'],'weighted expression point pin')
'''
needle = "draft=D/'research/current14-carrier65-dag-expression-retry-draft/Current14Carrier65DAGExpression.lean'"
assert needle in old
old = old.replace(needle, extra + needle)
old = old.replace("m=='DiophantineConsistency.CurrentEquationSyntax2011' or", "m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.WeightedExpressionDegree') or")
needle = "if mod=='DiophantineConsistency.CurrentEquationSyntax2011':expected=syntax_pin['sha256'];path=Path(syntax_pin['realpath'])"
assert needle in old
old = old.replace(needle, needle + "\n   elif mod=='DiophantineConsistency.WeightedExpressionDegree':expected=weighted_pin['sha256'];path=Path(weighted_pin['realpath'])")
(check / 'run.py').write_text(old)
print('Prepared expression import retry; no Lean invoked.')
