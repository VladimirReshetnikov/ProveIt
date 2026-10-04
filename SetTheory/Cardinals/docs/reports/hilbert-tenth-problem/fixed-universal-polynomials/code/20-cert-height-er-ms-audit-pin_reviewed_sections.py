from pathlib import Path
from hashlib import sha256
import json

root = Path('/workspace/shared')
out = root / 'report46-even-rank-manuscript-audit-20261004'
report46 = root / 'certificate-height-report46-release-20261004/Research_Report46.tex'
raw = report46.read_bytes()

def extract(start, stop):
    a = start.encode('utf-8')
    b = stop.encode('utf-8')
    if raw.count(a) != 1 or raw.count(b) != 1:
        raise RuntimeError('Review markers are not unique')
    begin = raw.index(a)
    end = raw.index(b, begin)
    if end <= begin:
        raise RuntimeError('Reversed review section')
    return raw[begin:end]

markers = {
    'sections8-10.tex': (r'\section{Small-norm descent for the free83 interface}', r'\section{Verification, reproducibility, and limitations}'),
    'theorem-free83.tex': (r'\begin{theorem}[Even-rank nonextension to free83]', r'\section{The fixed counterfamily and the literal interfaces}'),
    'section7-dependencies.tex': (r'\begin{lemma}[Integer-coordinate Pell classification]', r'\begin{proposition}[Complete auxiliary classification]'),
    'section2-outer-interface.tex': (r'\section{The fixed counterfamily and the literal interfaces}', r'\subsection{The square/product82 auxiliary block}'),
}
receipts = {}
for name, (start, stop) in markers.items():
    part = extract(start, stop)
    (out / name).write_bytes(part)
    receipts[name] = {'sha256': sha256(part).hexdigest(), 'bytes': len(part), 'start_inclusive': start, 'stop_exclusive': stop}

report45 = root / 'square-product82-report45-release-20261004'
manifest = json.loads((report45 / 'MANIFEST.json').read_text())
source_names = [
    'Research_Report45.tex',
    'packets/square-product82-counterfamily-recovered-20261004/COUNTERFAMILY.md',
    'packets/square-product82-counterfamily-recovered-20261004/source/complete82_auxiliary_square_product_chart.json',
]
source_hashes = {}
for name in source_names:
    digest = sha256((report45 / name).read_bytes()).hexdigest()
    if digest != manifest['sha256'][name]:
        raise RuntimeError('Report45 manifest mismatch: ' + name)
    source_hashes[name] = digest

receipt = {
    'review_scope': 'Report46 free83 theorem, Sections 8-10, their Section7 Pell dependencies, Section2 interface; Report45 source-level tuple invariants',
    'status': 'PASS',
    'report46_whole_tex_observed_sha256_not_final_release_pin': sha256(raw).hexdigest(),
    'section_snapshots': receipts,
    'report45_manifest_matched_sources': source_hashes,
    'upstream_code_executed': False,
    'saved_schedules_executed': False,
    'note': 'This fresh script only extracts bytes and checks hashes. Mathematical conclusions come from the independent proof review in AUDIT.md, not this script.'
}
(out / 'REVIEW_PINS.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
