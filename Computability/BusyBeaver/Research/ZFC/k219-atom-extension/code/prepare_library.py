from pathlib import Path
import argparse
import hashlib
import json
import library as lib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REPO = ROOT.parents[4]
ap = argparse.ArgumentParser(description='Build exact accepted-subtree atom inputs in a fresh directory.')
ap.add_argument('--output', type=Path, required=True)
args = ap.parse_args()
P = args.output.resolve()
P.mkdir(parents=True, exist_ok=False)
SOURCE = REPO / 'Computability/BusyBeaver/Research/ZFC/candidate-k219/sites219.json'
MACRO = REPO / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-machine-new_equality_macro.json'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SOURCE) == '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
tree = lib.parse(json.loads(SOURCE.read_text()))
old = lib.frozen(json.loads(MACRO.read_text()))
assert lib.metrics(tree)['dag_nodes'] == 206
allowed = lambda t: all(op in ('CB', 'CC') or (op in ('CI', 'CD') and r in (5, 6)) for _, op, r in lib.leaves(t))
atoms = sorted((t for t in lib.subtrees(tree) if t != old and allowed(t)), key=lambda t: (len(lib.leaves(t)), json.dumps(t)))
assert len(atoms) == 19 and old not in atoms
original = list(map(lib.frozen, json.loads((ROOT / 'inputs/original-atoms.json').read_text())))
raw = list(map(int, (ROOT / 'inputs/original-atoms.in').read_text().split()))
assert raw[:2] == [9, 14] and len(raw) == 1402
controls = []
for i, atom in enumerate(original):
    actual = lib.signature(atom)
    expected = raw[2 + 100 * i:2 + 100 * (i + 1)]
    assert actual == expected, (i, [(j, a, b) for j, (a, b) in enumerate(zip(actual, expected)) if a != b])
    controls.append({'index': i, 'in_new_library': atom in atoms, 'signatures_equal': True})
assert set(original) <= set(atoms)
signatures = [lib.signature(t) for t in atoms]
(P / 'atoms.json').write_text(json.dumps(atoms, indent=2) + '\n')
(P / 'atoms.in').write_text('9 19\n' + '\n'.join(' '.join(map(str, row)) for row in signatures) + '\n')
record = {'status': 'INDEPENDENT_ATOM_LIBRARY_CONTROL_PASS', 'source': {'path': str(SOURCE), 'sha256': sha(SOURCE)},
          'excluded_equality': {'path': str(MACRO), 'sha256': sha(MACRO)}, 'atoms': 19, 'original_atoms': 14,
          'additional_atoms': [t for t in atoms if t not in original], 'control_entries': 1400,
          'controls': controls, 'atoms_sha256': sha(P / 'atoms.json'), 'signatures_sha256': sha(P / 'atoms.in'),
          'interpreter_sha256': sha(HERE / 'library.py'), 'preparation_sha256': sha(Path(__file__)),
          'signature_scope': 'Both registers in0..9; overflow or repeated open graph configuration is unknown. Open Normal/Break/Continue exits preserve final register pair. No all-natural correctness claim.'}
(P / 'library-review.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
