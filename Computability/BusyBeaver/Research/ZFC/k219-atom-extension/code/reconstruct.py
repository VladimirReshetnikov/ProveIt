"""Reconstruct one literal full source from a retained equality-discovery macro."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import library as lib

ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT.parents[4]
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--cost', type=int, choices=(4, 5), required=True)
ap.add_argument('--id', type=int, required=True)
ap.add_argument('--output', type=Path, required=True)
a = ap.parse_args()
analysis = ROOT / f'results/cost{a.cost}/analysis.json.gz'
record = json.loads(gzip.decompress(analysis.read_bytes()))
selected = next(x for x in record['results'] if x['id'] == a.id)
source = ROOT.parent / 'candidate-k219/sites219.json'
macro_source = REPO / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-machine-new_equality_macro.json'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(source) == '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
assert sha(macro_source) == '934e037b204790fe852a1a8076777b6ed980e5ec6f09c49193ad438e07c71630'
old = lib.frozen(json.loads(macro_source.read_text()))
macro = lib.frozen(selected['macro'])
tree, count = lib.replacement(lib.parse(json.loads(source.read_text())), old, macro)
assert count == selected['literal_replacements'] == 4
assert lib.metrics(tree) == selected['metrics']
encoded = (json.dumps(lib.leaves(tree), separators=(',', ':')) + '\n').encode()
if 'source_sha256' in selected:
    assert hashlib.sha256(encoded).hexdigest() == selected['source_sha256']
a.output.mkdir(parents=True, exist_ok=False)
(a.output / 'sites.json').write_bytes(encoded)
(a.output / 'macro.json').write_text(json.dumps(macro, indent=2) + '\n')
receipt = {'status': 'LITERAL_RECONSTRUCTION_PASS', 'cost': a.cost, 'id': a.id,
           'analysis_sha256': sha(analysis), 'reconstructor_sha256': sha(Path(__file__)),
           'source_sha256': sha(a.output / 'sites.json'), 'metrics': selected['metrics'],
           'literal_replacements': count,
           'scope': 'Literal source and DAG count only; no new finite execution, all-natural proof or binary-machine claim.'}
(a.output / 'reconstruction.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
