#!/usr/bin/env python3
"""Prepare diagonal core-binding retry without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-diagonal-core-binding-check'
check = here.parent / 'current14-carrier65-diagonal-core-binding-retry-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = json.loads((previous / 'source-manifest.json').read_text())['rows']
for i,row in enumerate(rows):
    oldsrc = previous / 'src/DiophantineConsistency' / (row['module'].split('.')[-1] + '.lean')
    src = srcdir / oldsrc.name
    shutil.copyfile(here / src.name if i == 1 else oldsrc, src)
    row['source'] = str(src.relative_to(repo)); row['source_sha256'] = sha(src)
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
old = (previous / 'run.py').read_text()
old = old.replace("OUT=Path('/tmp/current14-carrier65-diagonal-core-binding-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-diagonal-core-binding-retry-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
orig = here.parent / 'current14-carrier65-diagonal-core-binding-draft/Current14Carrier65DiagonalCoreBinding.lean'
new = here / 'Current14Carrier65DiagonalCoreBinding.lean'
old = old.replace(repr(str(orig)), repr(str(new))).replace(sha(orig), sha(new))
state = previous / 'attempt01/state.json'; outer = state.parent / 'outer-result.json'
audit = d / 'reviews/current14-carrier65-diagonal-core-binding-failure-independent/check.py'
live = Path('/tmp/current14-carrier65-diagonal-core-binding-20261110')
extra = f'''failed_state=D/'research/current14-carrier65-diagonal-core-binding-check/attempt01/state.json'
failed_outer=failed_state.parent/'outer-result.json'
failed_audit=D/'reviews/current14-carrier65-diagonal-core-binding-failure-independent/check.py'
need(sha(failed_state)=='{sha(state)}' and json.loads(failed_state.read_text())['status']=='FAILED','diagonal core binding parent failure')
need(sha(failed_outer)=='{sha(outer)}' and json.loads(failed_outer.read_text())['outer_exit_code']==1,'diagonal core binding parent outer')
need(sha(failed_audit)=='{sha(audit)}','diagonal core binding failure audit')
need(sha(Path({str(live / 'Current14Carrier65DiagonalCoreBinding-compile.txt')!r}))=='{sha(live / 'Current14Carrier65DiagonalCoreBinding-compile.txt')}','diagonal core binding failure log')
need(not Path({str(live / 'lib/DiophantineConsistency/Current14Carrier65DiagonalCoreBinding.olean')!r}).exists(),'diagonal core binding parent object absent')
'''
needle = 'replay_source='
assert needle in old
old = old.replace(needle, extra + needle, 1)
(check / 'run.py').write_text(old)
print('Prepared diagonal core-binding retry; no Lean invoked.')
