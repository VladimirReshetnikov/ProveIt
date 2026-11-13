#!/usr/bin/env python3
"""Audit the AQ22 display wording change against the prior display audit."""
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

here = Path(__file__).resolve().parent
root = here.parents[1]
rel = 'Computability/DiophantineConsistency/research/adaptive-square-sums22-degree10/'
task = root / 'research/adaptive-square-sums22-degree10'
old = root / 'reviews/equation10-22-independent-audit/receipt.json'
files = [task / x for x in ('build_display.py', 'equation10-22.tex', 'equation10-22.pdf', 'candidate.json')]
files += [root / 'equation.tex', old, Path(__file__).resolve()]
h = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
snapshot = {str(p.resolve()): h(p) for p in files}
historical = json.loads(old.read_text())
assert historical['status'] == 'PASS_INDEPENDENT_AQ22_DISPLAY'
assert h(task / 'candidate.json') == '1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'

before = b'substitution identities. A Lean witness-transport theorem and an internal\nintuitionistic PRA equivalence for this candidate have not been proved. No'
after = b'substitution identities. A historical author-only Lean run established the\nwitness transport and an internal intuitionistic PRA equivalence to a\ntranslated consistency sentence. A paired replay remains pending. No'
for name in ('build_display.py', 'equation10-22.tex'):
    base = subprocess.run(['git', 'show', '7158586014:' + rel + name], cwd=root,
                          check=True, capture_output=True).stdout
    matches = [v for k, v in historical['inputs_sha256'].items() if k.endswith('/' + name)]
    assert len(matches) == 1 and hashlib.sha256(base).hexdigest() == matches[0]
    assert base.count(before) == 1
    assert (task / name).read_bytes() == base.replace(before, after, 1)

pdfhashes = []
with tempfile.TemporaryDirectory(prefix='aq22-wording-review-') as tmp:
    for run in ('first', 'second'):
        dest = Path(tmp) / run / 'research/adaptive-square-sums22-degree10'
        dest.mkdir(parents=True)
        for name in ('build_display.py', 'candidate.json'):
            shutil.copy2(task / name, dest / name)
        shutil.copy2(root / 'equation.tex', dest.parents[1] / 'equation.tex')
        p = subprocess.run([sys.executable, str(dest / 'build_display.py')], cwd=dest,
                           capture_output=True, text=True, timeout=180)
        assert p.returncode == 0, (p.returncode, p.stdout, p.stderr)
        assert 'two warning-free identical PDF builds' in p.stdout
        assert (dest / 'equation10-22.tex').read_bytes() == (task / 'equation10-22.tex').read_bytes()
        pdfhashes.append(h(dest / 'equation10-22.pdf'))
assert pdfhashes == [h(task / 'equation10-22.pdf')] * 2
assert {str(p.resolve()): h(p) for p in files} == snapshot
receipt = {'status': 'PASS_AQ22_WORDING_AUDIT', 'inputs_sha256': snapshot,
           'comparison': 'exact one-paragraph replacement in baseline generator and TeX',
           'candidate_sha256': h(task / 'candidate.json'),
           'generator_runs': 2, 'generator_builds_per_run': 2,
           'generator_pdf_sha256': pdfhashes,
           'scope': 'Historical author-only artifact evidence; no matched replay or formal PDF-to-Lean identification.'}
out = here / 'receipt.json'
assert not out.exists()
out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print('PASS_AQ22_WORDING_AUDIT', h(out), pdfhashes[0])
