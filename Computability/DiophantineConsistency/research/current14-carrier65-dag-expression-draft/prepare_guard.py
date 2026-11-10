#!/usr/bin/env python3
"""Prepare expression-composition guard without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
check = here.parent / 'current14-carrier65-dag-expression-check'
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
template = here.parent / 'current14-seed-readable-prefix-staged-check/run.py'
provider = Path('/tmp/current14-carrier65-dag-value-congr-diagnostic-20261110')
state = here.parent / 'current14-carrier65-dag-value-congr-diagnostic-check/attempt01/state.json'
outer = state.parent / 'outer-result.json'
audit = d / 'reviews/current14-carrier65-dag-value-congr-diagnostic-terminal-independent/check.py'
parent_state = here.parent / 'current14-carrier65-dag-check/attempt01/state.json'
parent_outer = parent_state.parent / 'outer-result.json'
parent_audit = d / 'reviews/current14-carrier65-dag-failure-independent/check.py'
syntax = provider / 'lib/DiophantineConsistency/CurrentEquationSyntax2011.olean'
syntax_pin = {'realpath': str(syntax.resolve()), 'sha256': sha(syntax)}
old = template.read_text()
old = old.replace('/tmp/nine-sharing-sign17-readable-current14-endpoint-20261110', str(provider))
old = old.replace("OUT=Path('/tmp/current14-seed-readable-prefix-staged-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-dag-expression-20261110')")
start = old.index("STATE=D/'research/nine-sharing-sign17-readable-current14-endpoint-check/attempt01/state.json'")
end = old.index('\nroots=', start)
old = old[:start] + ("STATE=D/'research/current14-carrier65-dag-value-congr-diagnostic-check/attempt01/state.json';"
                     "OUTER=STATE.parent/'outer-result.json';"
                     "AUDIT=D/'reviews/current14-carrier65-dag-value-congr-diagnostic-terminal-independent/check.py'") + old[end:]
old = re.sub(r"need\(sha\(STATE\)=='[0-9a-f]+'", f"need(sha(STATE)=='{sha(state)}'", old)
old = re.sub(r"need\(sha\(OUTER\)=='[0-9a-f]+'", f"need(sha(OUTER)=='{sha(outer)}'", old)
old = re.sub(r"need\(sha\(AUDIT\)=='[0-9a-f]+'", f"need(sha(AUDIT)=='{sha(audit)}'", old)
old = old.replace("base['rows'][-1]['module']=='Sign17ReadableCurrent14Endpoint'", "base['rows'][-1]['module']=='Current14Carrier65DAGValue'")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("need(len(entries)==3,'stage count')", "need(len(entries)==1,'stage count')")
start = old.index("witness=D/'research/nine-sharing-sign17-k-ranking-witness/witness.json'")
end = old.index('provider_names={r[\'module\']:r for r in base[\'rows\']}', start)
extra = f'''draft=D/'research/current14-carrier65-dag-expression-draft/Current14Carrier65DAGExpression.lean'
need(sha(draft)=='{sha(here / src.name)}','expression source pin')
need(sha(P/'src/DiophantineConsistency/Current14Carrier65DAGExpression.lean')==sha(draft),'expression source copy')
parent_state=D/'research/current14-carrier65-dag-check/attempt01/state.json'
parent_outer=parent_state.parent/'outer-result.json'
parent_audit=D/'reviews/current14-carrier65-dag-failure-independent/check.py'
need(sha(parent_state)=='{sha(parent_state)}' and json.loads(parent_state.read_text())['status']=='FAILED','original failed parent')
need(sha(parent_outer)=='{sha(parent_outer)}' and json.loads(parent_outer.read_text())['outer_exit_code']==1,'original failed parent outer')
need(sha(parent_audit)=='{sha(parent_audit)}','original failure audit')
syntax_pin={syntax_pin!r}
syntax=BASE/'lib/DiophantineConsistency/CurrentEquationSyntax2011.olean'
need(syntax.is_file() and str(syntax.resolve())==syntax_pin['realpath'] and sha(syntax)==syntax_pin['sha256'],'historical expression syntax point pin')
'''
old = old[:start] + extra + old[end:]
old = old.replace("m.startswith('DiophantineConsistency.') and (m.split('.')[-1] in provider_names or m.split('.')[-1] in names[:names.index(n)])",
                  "m=='DiophantineConsistency.CurrentEquationSyntax2011' or m.split('.')[-1] in provider_names or m.split('.')[-1] in names[:names.index(n)]")
needle = "if depname in provider_names:expected=provider_names[depname]['object_sha256'];path=BASE/'lib/DiophantineConsistency'/(depname+'.olean')"
replacement = "if mod=='DiophantineConsistency.CurrentEquationSyntax2011':expected=syntax_pin['sha256'];path=Path(syntax_pin['realpath'])\n   elif depname in provider_names:expected=provider_names[depname]['object_sha256'];path=BASE/'lib/DiophantineConsistency'/(depname+'.olean')"
assert needle in old
old = old.replace(needle, replacement)
old = old.replace('PASS quoted arithmetic prefix current14 iPRA endpoint', 'PASS current14 65-gate circuit expression composition')
old = old.replace('Audited single-context provider and direct source/object/guard observations; no Lean, complete transitive trace, global order or rank proof.',
                  'Audited semantic provider and expression point object; no Lean theorem or complete transitive import trace.')
(check / 'run.py').write_text(old)
print('Prepared expression composition guard; no Lean invoked.')
