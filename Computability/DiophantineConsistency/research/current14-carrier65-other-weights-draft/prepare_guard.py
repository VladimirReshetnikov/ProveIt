#!/usr/bin/env python3
"""Prepare non-Q syntax-weight guard without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-q-fields-check'
check = here.parent / 'current14-carrier65-other-weights-check'
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
old = old.replace("OUT=Path('/tmp/current14-carrier65-q-fields-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-other-weights-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-q-fields-draft/Current14Carrier65QFields.lean'",
                  "draft=D/'research/current14-carrier65-other-weights-draft/Current14Carrier65OtherWeights.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
old = old.replace("P/'src/DiophantineConsistency/Current14Carrier65QFields.lean'", "P/'src/DiophantineConsistency/Current14Carrier65OtherWeights.lean'")
old = old.replace('PASS current14 Q field bindings and input bounds', 'PASS current14 other factor syntax weights')
(check / 'run.py').write_text(old)
print('Prepared non-Q syntax weights; no Lean invoked.')
