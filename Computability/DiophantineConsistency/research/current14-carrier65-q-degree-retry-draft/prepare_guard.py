#!/usr/bin/env python3
"""Prepare Q-degree cast retry without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-q-degree-check'
check = here.parent / 'current14-carrier65-q-degree-retry-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65QDegree.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65QDegree',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
old = (previous / 'run.py').read_text()
old = old.replace("OUT=Path('/tmp/current14-carrier65-q-degree-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-q-degree-retry-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-q-degree-draft/Current14Carrier65QDegree.lean'",
                  "draft=D/'research/current14-carrier65-q-degree-retry-draft/Current14Carrier65QDegree.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
state = previous / 'attempt01/state.json'
outer = previous / 'attempt01/outer-result.json'
audit = d / 'reviews/current14-carrier65-q-degree-failure-independent/check.py'
live = Path('/tmp/current14-carrier65-q-degree-20261110')
extra = f'''failed_state=D/'research/current14-carrier65-q-degree-check/attempt01/state.json'
failed_outer=failed_state.parent/'outer-result.json'
failed_audit=D/'reviews/current14-carrier65-q-degree-failure-independent/check.py'
need(sha(failed_state)=='{sha(state)}' and json.loads(failed_state.read_text())['status']=='FAILED','Q degree parent failure')
need(sha(failed_outer)=='{sha(outer)}' and json.loads(failed_outer.read_text())['outer_exit_code']==1,'Q degree parent outer')
need(sha(failed_audit)=='{sha(audit)}','Q degree failure audit')
need(sha(Path({str(live / 'Current14Carrier65QDegree-compile.txt')!r}))=='{sha(live / 'Current14Carrier65QDegree-compile.txt')}','Q degree failure log')
need(not Path({str(live / 'lib/DiophantineConsistency/Current14Carrier65QDegree.olean')!r}).exists(),'Q degree parent object absent')
'''
needle = "draft=D/'research/current14-carrier65-q-degree-retry-draft/Current14Carrier65QDegree.lean'"
assert needle in old
old = old.replace(needle, extra + needle)
(check / 'run.py').write_text(old)
print('Prepared Q-degree cast retry; no Lean invoked.')
