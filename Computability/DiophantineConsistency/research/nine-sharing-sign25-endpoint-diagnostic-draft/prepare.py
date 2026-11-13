#!/usr/bin/env python3
"""Derive a separate-output diagnostic guard from the reviewed endpoint guard."""
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
draft = Path(__file__).resolve().parent
research = draft.parent
check = research / 'nine-sharing-sign25-endpoint-diagnostic-check'
original = research / 'nine-sharing-sign25-endpoint-check'
assert not check.exists(), 'refusing to overwrite diagnostic packet'
check.mkdir()
(check / 'src/DiophantineConsistency').mkdir(parents=True)
shutil.copyfile(original / 'framework-survey.py', check / 'framework-survey.py')
names = ['Sign25DiagImport', 'Sign25DiagExpression', 'Sign25DiagBridge', 'Sign25DiagAxioms']
rows = []
for name in names:
    src = draft / (name + '.lean')
    dest = check / 'src/DiophantineConsistency' / src.name
    shutil.copyfile(src, dest)
    data = src.read_bytes()
    imports = re.findall(r'^import ([A-Za-z0-9_.]+)$', data.decode(), re.M)
    rows.append({'module': 'DiophantineConsistency.' + name,
                 'source': str(src.relative_to(research.parents[2])),
                 'source_sha256': hashlib.sha256(data).hexdigest(),
                 'imports': imports})
manifest = (json.dumps({'rows': rows}, indent=2) + '\n').encode()
(check / 'source-manifest.json').write_bytes(manifest)
runner = (original / 'run.py').read_text()
old_pin = 'c5de8b265cfbb4fbc75bd903f67e411dff8798d8144fd4d5fdfbafff79e10dd8'
assert runner.count(old_pin) == 1
runner = runner.replace(old_pin, hashlib.sha256(manifest).hexdigest())
old_out = '/tmp/nine-sharing-sign25-endpoint-check-20261106'
assert runner.count(old_out) == 1
runner = runner.replace(old_out, '/tmp/nine-sharing-sign25-endpoint-diagnostic-20261109')
old_names = "'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard','Sign25DirectTranslated'"
assert runner.count(old_names) == 1
runner = runner.replace(old_names, ','.join(repr(n) for n in names))
old_previous = "'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard'"
assert runner.count(old_previous) == 1
runner = runner.replace(old_previous, ','.join(repr(n) for n in names[:-1]))
runner = runner.replace('Bounded sign26 direct endpoint diagnostic', 'Bounded sign25 split-stage bridge diagnostic')
runner = runner.replace('PASS sign25 direct endpoint diagnostic', 'PASS sign25 split-stage bridge diagnostic')
(check / 'run.py').write_text(runner)
(check / 'README.md').write_text('''# Sign25 split endpoint diagnostic guarded client\n\nFour source-only stages separately test the bridge import, expression alias,\nbridge theorem and axiom report after the original first-stage memory failure.\nThe runner is adapted from the pinned endpoint runner with the same resource\nlimits and independent output directory; the diagnostic changes import\nboundaries and therefore does not by itself isolate the exact original cause.\nNo endpoint is claimed. Author no-Lean preflight and independent review are\nrequired, and Lean may run only on an assigned slot.\n''')
print(json.dumps({'manifest_sha256': hashlib.sha256(manifest).hexdigest(),
                  'runner_sha256': hashlib.sha256(runner.encode()).hexdigest(),
                  'stages': names}, sort_keys=True))
