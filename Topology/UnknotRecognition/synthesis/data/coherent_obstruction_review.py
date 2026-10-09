"""Check publication hashes, displayed coordinates and retained validation."""
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT/'synthesis/data'
record = json.loads((DATA/'coherent-obstruction-certificate.json').read_text())
counts = {}
for name in ('audit','replay'):
    result = json.loads((DATA/f'coherent-obstruction-{name}.json').read_text())
    for path,digest in result['source_sha256'].items():
        assert sha256((ROOT/'fast'/path).read_bytes()).hexdigest() == digest, path
    assert sha256((DATA/'coherent-obstruction-certificate.json').read_bytes()).hexdigest() == result['record_sha256']
    counts[name] = len(result['source_sha256'])

article = (ROOT/'synthesis/coherent_obstruction.tex').read_text()
table = [line for line in article.splitlines() if re.match(r'^\d & ',line)]
assert len(table) == 8
for t,line in enumerate(table):
    rows = [[int(x) for x in entry.split(',')] for entry in re.findall(r'\(([^()]*)\)',line)]
    assert rows == [record['family_certificate']['heights'][t],
                    record['family_certificate']['coordinates'][t],record['disc_coordinates'][t]]

tests = (DATA/'coherent-obstruction-tests.txt').read_text()
assert 'Ran 1238 tests in 230.697s\n\nOK' in tests
log = (ROOT/'synthesis/report.log').read_text()
assert not re.search(r'undefined|Label\(s\) may have changed',log)
warnings = re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
assert warnings == [f'{x}pt too wide' for x in ('12.64871','13.49065','9.04614','35.14671')]
assert 'Output written on report.pdf (480 pages,' in log
(DATA/'coherent-obstruction-latex.txt').write_text('\n'.join(line.rstrip() for line in log.splitlines()).rstrip()+'\n')
paths = ['synthesis/report.pdf','synthesis/coherent_obstruction.tex',
         'synthesis/coherent_obstruction_results.tex',
         'synthesis/data/coherent-obstruction-certificate.json',
         'synthesis/data/coherent-obstruction-audit.json',
         'synthesis/data/coherent-obstruction-replay.json',
         'synthesis/data/coherent-obstruction-tests.txt',
         'synthesis/data/coherent-obstruction-latex.txt',
         'synthesis/data/coherent_obstruction_review.py']
result = dict(runtime_revision='f253c67f1',source_pins_checked=counts,
              displayed_coordinate_rows_checked=8,maintained_tests=1238,
              independent_random_move_comparisons=240,pdf_pages=480,
              section=121,section_pages=[474,475,476,477],
              preexisting_overfull_warnings=warnings,
              sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in paths})
(DATA/'coherent-obstruction-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='sha256'}))
