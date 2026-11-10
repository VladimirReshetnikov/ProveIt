#!/usr/bin/env python3
"""Prepare the definitional Q-input syntax retry without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-other-weights-check'
check = here.parent / 'current14-carrier65-other-weights-retry-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65OtherWeights.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65OtherWeights',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
old = (previous / 'run.py').read_text()
old = old.replace("OUT=Path('/tmp/current14-carrier65-other-weights-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-other-weights-retry-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-other-weights-draft/Current14Carrier65OtherWeights.lean'",
                  "draft=D/'research/current14-carrier65-other-weights-retry-draft/Current14Carrier65OtherWeights.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
state = previous / 'attempt01/state.json'
outer = previous / 'attempt01/outer-result.json'
audit = d / 'reviews/current14-carrier65-other-weights-failure-independent/check.py'
live = Path('/tmp/current14-carrier65-other-weights-20261110')
extra = f'''failed_state=D/'research/current14-carrier65-other-weights-check/attempt01/state.json'
failed_outer=failed_state.parent/'outer-result.json'
failed_audit=D/'reviews/current14-carrier65-other-weights-failure-independent/check.py'
need(sha(failed_state)=='{sha(state)}' and json.loads(failed_state.read_text())['status']=='FAILED','non-Q weights parent failure')
need(sha(failed_outer)=='{sha(outer)}' and json.loads(failed_outer.read_text())['outer_exit_code']==1,'non-Q weights parent outer')
need(sha(failed_audit)=='{sha(audit)}','non-Q weights failure audit')
need(sha(Path({str(live / 'Current14Carrier65OtherWeights-compile.txt')!r}))=='{sha(live / 'Current14Carrier65OtherWeights-compile.txt')}','non-Q weights failure log')
need(not Path({str(live / 'lib/DiophantineConsistency/Current14Carrier65OtherWeights.olean')!r}).exists(),'non-Q weights parent object absent')
'''
needle = "draft=D/'research/current14-carrier65-other-weights-retry-draft/Current14Carrier65OtherWeights.lean'"
assert needle in old
old = old.replace(needle, extra + needle)
(check / 'run.py').write_text(old)
print('Prepared non-Q staged U retry; no Lean invoked.')
