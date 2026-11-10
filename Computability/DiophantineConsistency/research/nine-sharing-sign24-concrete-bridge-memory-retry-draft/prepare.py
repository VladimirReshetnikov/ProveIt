#!/usr/bin/env python3
"""Copy the reviewed sign24 bridge guard with one scoped Lean limit change."""
import hashlib
import json
import shutil
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
draft = Path(__file__).resolve().parent
old = draft.parent/'nine-sharing-sign24-concrete-polynomial-bridge-check'
new = draft.parent/'nine-sharing-sign24-concrete-bridge-memory-retry-check'
assert not new.exists(), 'refusing to overwrite retry'
new.mkdir()
for name in ('provider-union-survey.py', 'union.json', 'source-manifest.json'):
    shutil.copyfile(old/name, new/name)
shutil.copytree(old/'src', new/'src')
runner = (old/'run.py').read_text()
old_output = '/tmp/nine-sharing-sign24-concrete-polynomial-bridge-check-20261109'
assert runner.count(old_output) == 1 and runner.count("'-M2800'") == 1
runner = runner.replace(old_output, '/tmp/nine-sharing-sign24-concrete-bridge-memory-retry-20261109')
runner = runner.replace("'-M2800'", "'-M3600'")
runner = runner.replace('Bounded sign25 concrete polynomial bridge diagnostic',
                        'Bounded sign24 concrete bridge memory retry')
(new/'run.py').write_text(runner)
(new/'README.md').write_text('''# Sign24 concrete bridge scoped memory retry\n\nThis source-only retry uses the identical source, manifest and provider union as\nthe previously failed sign24 bridge, with Lean interpreter limit increased from\n`-M2800` to `-M3600`. The existing 4 GiB sampled RSS cap, 10 GiB host-memory\nfloor, 120-second timeout, disk precheck and provider guards are unchanged.\nNo theorem is claimed pending Lean and independent terminal audit.\n''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),
                  'manifest_sha256':hashlib.sha256((new/'source-manifest.json').read_bytes()).hexdigest()},sort_keys=True))
