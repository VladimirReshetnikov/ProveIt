#!/usr/bin/env python3
"""Prepare actual diagonal W coefficient client without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-diagonal-core-check'
check = here.parent / 'current14-carrier65-diagonal-w-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65DiagonalW.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65DiagonalW',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
provider = Path('/tmp/current14-carrier65-diagonal-binding-20261110')
state = here.parent / 'current14-carrier65-diagonal-binding-check/attempt01/state.json'
outer = state.parent / 'outer-result.json'
audit = d / 'reviews/current14-carrier65-diagonal-binding-terminal-independent/check.py'
old = (previous / 'run.py').read_text()
old = old.replace("BASE=Path('/tmp/current14-carrier65-diagonal-base-retry-20261110')", f"BASE=Path({str(provider)!r})")
old = old.replace("OUT=Path('/tmp/current14-carrier65-diagonal-core-20261110')", "OUT=Path('/tmp/current14-carrier65-diagonal-w-20261110')")
start = old.index("STATE=D/'research/current14-carrier65-diagonal-base-retry-check/attempt01/state.json'")
end = old.index('\nroots=', start)
old = old[:start] + ("STATE=D/'research/current14-carrier65-diagonal-binding-check/attempt01/state.json';"
                     "OUTER=STATE.parent/'outer-result.json';"
                     "AUDIT=D/'reviews/current14-carrier65-diagonal-binding-terminal-independent/check.py'") + old[end:]
old = re.sub(r"need\(sha\(STATE\)=='[0-9a-f]+'", f"need(sha(STATE)=='{sha(state)}'", old)
old = re.sub(r"need\(sha\(OUTER\)=='[0-9a-f]+'", f"need(sha(OUTER)=='{sha(outer)}'", old)
old = re.sub(r"need\(sha\(AUDIT\)=='[0-9a-f]+'", f"need(sha(AUDIT)=='{sha(audit)}'", old)
old = old.replace("base['rows'][-1]['module']=='Current14Carrier65DiagonalBase'", "base['rows'][-1]['module']=='Current14Carrier65DiagonalBinding'")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-diagonal-core-draft/Current14Carrier65DiagonalCore.lean'",
                  "draft=D/'research/current14-carrier65-diagonal-w-draft/Current14Carrier65DiagonalW.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
old = old.replace("P/'src/DiophantineConsistency/Current14Carrier65DiagonalCore.lean'", "P/'src/DiophantineConsistency/Current14Carrier65DiagonalW.lean'")
old = old.replace('PASS generic diagonal core degrees', 'PASS actual diagonal W degree and coefficient')
(check / 'run.py').write_text(old)
print('Prepared diagonal W coefficient; no Lean invoked.')
