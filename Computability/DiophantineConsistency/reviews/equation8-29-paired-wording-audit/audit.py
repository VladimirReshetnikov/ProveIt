#!/usr/bin/env python3
"""Audit a wording-only revision against a fixed previously audited display."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

D = Path(__file__).resolve().parent
ROOT = D.parents[1]
REPO = ROOT.parents[1]
BASE = 'd341f5e234'
OLD = 'has not passed the guarded replay'
NEW = 'has not passed a paired guarded replay'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def old_bytes(path):
    name = str(path.relative_to(REPO))
    return subprocess.check_output(['git', 'show', f'{BASE}:{name}'], cwd=REPO)

def command(args, **kwargs):
    return subprocess.run(args, check=True, capture_output=True, text=True, **kwargs)

tex = ROOT / 'equation8-29.tex'
pdf = ROOT / 'equation8-29.pdf'
generator = ROOT / 'research/adaptive-square-sums29-degree8/generate_equation8_29.py'
for path in (tex, generator):
    before = old_bytes(path).decode()
    after = path.read_text()
    assert before.count(OLD) == after.count(NEW) == 1
    assert after == before.replace(OLD, NEW, 1), ('unexpected change', str(path))

baseline_pdf = old_bytes(pdf)
assert hashlib.sha256(baseline_pdf).hexdigest() == 'ecab3829b0f1c677945da5e6d3efdc099949766ce92be9a0e45c356e809056e7'
assert H(pdf) == '29c467794dd2fffea7a19e9a1611b7b99bc69f658aa270fab4091cd239ad8a31'
with tempfile.TemporaryDirectory(prefix='eq29-paired-wording-audit-') as td:
    base = Path(td)
    old_pdf = base / 'baseline.pdf'
    old_pdf.write_bytes(baseline_pdf)
    hashes = []
    for i in range(2):
        out = base / f'build{i}'
        out.mkdir()
        command(['pdflatex', '-halt-on-error', '-interaction=batchmode',
                 '-output-directory', str(out), str(tex)], cwd=ROOT)
        log = (out / 'equation8-29.log').read_text(errors='replace')
        assert not re.search(r'Overfull|Underfull|Font shape .* undefined', log)
        hashes.append(H(out / 'equation8-29.pdf'))
    assert hashes == [H(pdf), H(pdf)]
    info = command(['pdfinfo', str(pdf)]).stdout
    assert re.search(r'^Pages:\s+2\s*$', info, re.M)
    def page(p, n):
        return command(['pdftotext', '-layout', '-f', str(n), '-l', str(n), str(p), '-']).stdout
    old1, new1 = page(old_pdf, 1), page(pdf, 1)
    marker = 'The fixed integer'
    assert old1.count(marker) == new1.count(marker) == 1
    # PDF text extraction may shift horizontal alignment by one space when
    # the footer reflows; compare all preceding extracted non-whitespace.
    assert re.sub(r'\s+', '', old1.split(marker)[0]) == re.sub(r'\s+', '', new1.split(marker)[0])
    assert 'paired guarded replay' in ' '.join(new1.split())
    assert page(old_pdf, 2) == page(pdf, 2)

receipt = {
    'status': 'PASS_WORDING_ONLY_AUDIT',
    'baseline_commit': BASE,
    'baseline_pdf_sha256': hashlib.sha256(baseline_pdf).hexdigest(),
    'current_pdf_sha256': H(pdf),
    'tex_sha256': H(tex),
    'generator_sha256': H(generator),
    'audit_script_sha256': H(Path(__file__)),
    'fresh_build_pdf_sha256': hashes,
    'pdf_pages': 2,
    'scope': 'Only the disclosure wording changed in the TeX and generator. '
             'Formula and circuit text are unchanged; this audit does not verify Lean proofs or provider provenance.',
}
out = D / 'receipt.json'
if out.exists():
    raise RuntimeError('refusing to overwrite existing receipt')
out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(receipt['status'], H(out))
