#!/usr/bin/env python3
"""Prepare the Q input-syntax ingredient guard without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-q-degree-check'
check = here.parent / 'current14-carrier65-q-inputs-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65QInputs.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65QInputs',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
old = (previous / 'run.py').read_text()
old = old.replace("OUT=Path('/tmp/current14-carrier65-q-degree-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-q-inputs-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-q-degree-draft/Current14Carrier65QDegree.lean'",
                  "draft=D/'research/current14-carrier65-q-inputs-draft/Current14Carrier65QInputs.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
old = old.replace("P/'src/DiophantineConsistency/Current14Carrier65QDegree.lean'", "P/'src/DiophantineConsistency/Current14Carrier65QInputs.lean'")
old = old.replace('PASS generic current14 Q degree ingredient', 'PASS current14 Q input syntax bounds')
(check / 'run.py').write_text(old)
print('Prepared Q input syntax bounds; no Lean invoked.')
