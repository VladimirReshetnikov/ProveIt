#!/usr/bin/env python3
"""Prepare diagonal binding ingredient without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-q-fields-check'
check = here.parent / 'current14-carrier65-diagonal-binding-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65DiagonalBinding.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65DiagonalBinding',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
provider = Path('/tmp/current14-carrier65-diagonal-base-retry-20261110')
state = here.parent / 'current14-carrier65-diagonal-base-retry-check/attempt01/state.json'
outer = state.parent / 'outer-result.json'
audit = d / 'reviews/current14-carrier65-diagonal-base-retry-terminal-independent/check.py'
failed = here.parent / 'current14-carrier65-diagonal-base-check/attempt01/state.json'
failed_outer = failed.parent / 'outer-result.json'
failed_audit = d / 'reviews/current14-carrier65-diagonal-base-failure-independent/check.py'
old = (previous / 'run.py').read_text()
old = old.replace("BASE=Path('/tmp/current14-carrier65-q-inputs-retry-20261110')", f"BASE=Path({str(provider)!r})")
old = old.replace("OUT=Path('/tmp/current14-carrier65-q-fields-20261110')", "OUT=Path('/tmp/current14-carrier65-diagonal-binding-20261110')")
start = old.index("STATE=D/'research/current14-carrier65-q-inputs-retry-check/attempt01/state.json'")
end = old.index('\nroots=', start)
old = old[:start] + ("STATE=D/'research/current14-carrier65-diagonal-base-retry-check/attempt01/state.json';"
                     "OUTER=STATE.parent/'outer-result.json';"
                     "AUDIT=D/'reviews/current14-carrier65-diagonal-base-retry-terminal-independent/check.py'") + old[end:]
old = re.sub(r"need\(sha\(STATE\)=='[0-9a-f]+'", f"need(sha(STATE)=='{sha(state)}'", old)
old = re.sub(r"need\(sha\(OUTER\)=='[0-9a-f]+'", f"need(sha(OUTER)=='{sha(outer)}'", old)
old = re.sub(r"need\(sha\(AUDIT\)=='[0-9a-f]+'", f"need(sha(AUDIT)=='{sha(audit)}'", old)
old = old.replace("base['rows'][-1]['module']=='Current14Carrier65QInputs'", "base['rows'][-1]['module']=='Current14Carrier65DiagonalBase'")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-q-fields-draft/Current14Carrier65QFields.lean'",
                  "draft=D/'research/current14-carrier65-diagonal-binding-draft/Current14Carrier65DiagonalBinding.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
old = old.replace("P/'src/DiophantineConsistency/Current14Carrier65QFields.lean'", "P/'src/DiophantineConsistency/Current14Carrier65DiagonalBinding.lean'")
extra = f'''base_failure=D/'research/current14-carrier65-diagonal-base-check/attempt01/state.json'
base_failure_outer=base_failure.parent/'outer-result.json'
base_failure_audit=D/'reviews/current14-carrier65-diagonal-base-failure-independent/check.py'
need(sha(base_failure)=='{sha(failed)}' and json.loads(base_failure.read_text())['status']=='FAILED','diagonal base prior failure')
need(sha(base_failure_outer)=='{sha(failed_outer)}' and json.loads(base_failure_outer.read_text())['outer_exit_code']==1,'diagonal base prior outer')
need(sha(base_failure_audit)=='{sha(failed_audit)}','diagonal base failure audit')
'''
needle = "draft=D/'research/current14-carrier65-diagonal-binding-draft/Current14Carrier65DiagonalBinding.lean'"
assert needle in old
old = old.replace(needle, extra + needle)
old = old.replace('PASS current14 Q field bindings and input bounds', 'PASS actual diagonal base binding')
(check / 'run.py').write_text(old)
print('Prepared diagonal binding ingredient; no Lean invoked.')
