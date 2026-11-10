#!/usr/bin/env python3
"""Prepare diagonal eval-rewrite retry without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-diagonal-degree-retry-check'
check = here.parent / 'current14-carrier65-diagonal-degree-retry02-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65DiagonalDegree.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65DiagonalDegree',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
old = (previous / 'run.py').read_text()
old = old.replace("OUT=Path('/tmp/current14-carrier65-diagonal-degree-retry-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-diagonal-degree-retry02-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-diagonal-degree-retry-draft/Current14Carrier65DiagonalDegree.lean'",
                  "draft=D/'research/current14-carrier65-diagonal-degree-retry02-draft/Current14Carrier65DiagonalDegree.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
state = previous / 'attempt01/state.json'
outer = previous / 'attempt01/outer-result.json'
audit = d / 'reviews/current14-carrier65-diagonal-degree-retry-failure-independent/check.py'
live = Path('/tmp/current14-carrier65-diagonal-degree-retry-20261110')
extra = f'''retry_state=D/'research/current14-carrier65-diagonal-degree-retry-check/attempt01/state.json'
retry_outer=retry_state.parent/'outer-result.json'
retry_audit=D/'reviews/current14-carrier65-diagonal-degree-retry-failure-independent/check.py'
need(sha(retry_state)=='{sha(state)}' and json.loads(retry_state.read_text())['status']=='FAILED','diagonal degree retry failure')
need(sha(retry_outer)=='{sha(outer)}' and json.loads(retry_outer.read_text())['outer_exit_code']==1,'diagonal degree retry outer')
need(sha(retry_audit)=='{sha(audit)}','diagonal degree retry failure audit')
need(sha(Path({str(live / 'Current14Carrier65DiagonalDegree-compile.txt')!r}))=='{sha(live / 'Current14Carrier65DiagonalDegree-compile.txt')}','diagonal degree retry failure log')
need(not Path({str(live / 'lib/DiophantineConsistency/Current14Carrier65DiagonalDegree.olean')!r}).exists(),'diagonal degree retry object absent')
'''
needle = "draft=D/'research/current14-carrier65-diagonal-degree-retry02-draft/Current14Carrier65DiagonalDegree.lean'"
assert needle in old
old = old.replace(needle, extra + needle)
(check / 'run.py').write_text(old)
print('Prepared diagonal eval-rewrite retry; no Lean invoked.')
