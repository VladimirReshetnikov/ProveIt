#!/usr/bin/env python3
"""Replay the generator's partition/writer stage against the pinned 18-file fixture."""
from pathlib import Path
import argparse
import ast
import hashlib
import importlib.util
import json
import re
import sys

HERE = Path(__file__).resolve().parent
PACKET = HERE.parents[1]
sys.dont_write_bytecode = True
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--source', type=Path, default=PACKET / 'source')
p.add_argument('--out', type=Path, required=True)
a = p.parse_args()
source, out = a.source.resolve(), a.out.resolve()
assert not out.exists(), 'Use a fresh output directory'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


bindings = json.loads((HERE / 'sources.json').read_text())
original_file = HERE / 'partition_source215_lean.original.py'
modified_file = HERE / 'partition_source215_lean.py'
assert sha(original_file) == bindings['original_sha256']
assert sha(modified_file) == bindings['modified_sha256']
assert sha(HERE / 'generator-postpass.patch') == bindings['patch_sha256']
original_text, modified_text = original_file.read_text(), modified_file.read_text()


def partition_function(text):
    node = next(n for n in ast.parse(text).body
                if isinstance(n, ast.FunctionDef) and n.name == 'partition_source')
    return ast.get_source_segment(text, node)


assert partition_function(original_text) == partition_function(modified_text)
original = load('original_partition_source215', original_file)
modified = load('modified_partition_source215', modified_file)
relative_root = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
names = ['KSource215Data.lean'] + [f'KSource215FwdCheck{i:02d}.lean' for i in range(16)] + ['KSource215.lean']
manifest = {row['path']: row['sha256'] for row in json.loads((PACKET / 'base_sources.json').read_text())}
expected = {}
for name in names:
    file = source / relative_root / name
    assert sha(file) == manifest[str(relative_root / name)]
    expected[name] = file.read_text()

end = '\nend SetTheory.BusyBeaver.ZFC.KSource215\n'
data = expected['KSource215Data.lean']
assert data.endswith(end)
facade = expected['KSource215.lean']
facade = facade[facade.index('theorem fwd_start :'):]
declarations = []
for i in range(16):
    matches = re.findall(rf'(?m)^theorem fwd_ok{i} : [^\n]+\n', expected[f'KSource215FwdCheck{i:02d}.lean'])
    assert len(matches) == 1
    declarations.append(matches[0] + '\n')
fixture = data[:-len(end)] + facade.replace('theorem fwd_all :', ''.join(declarations) + 'theorem fwd_all :', 1)
assert fixture.encode() == (HERE / 'fixture_monolithic.lean').read_bytes()
assert original.partition_source(fixture) == expected
assert modified.partition_source(fixture) == expected

out.mkdir(parents=True)
emitted = out / 'emitted'; emitted.mkdir()
modified.write_partition(emitted / 'KSource215.lean', fixture)
changes = {row['repository_path'].rsplit('/', 1)[1]: row
           for row in json.loads((PACKET / 'batching/sources.json').read_text())}
assert sorted(path.name for path in emitted.iterdir()) == sorted(names)
rows = []
for name in names:
    actual = emitted / name
    if name in changes:
        target = PACKET / 'batching' / changes[name]['overlay_file']
        assert sha(target) == changes[name]['batched_sha256']
    else:
        target = source / relative_root / name
    assert actual.read_bytes() == target.read_bytes(), name
    rows.append({'file': name, 'proof_only_batching_change': name in changes,
                 'emitted_sha256': sha(actual), 'expected_sha256': sha(target)})
receipt = {
    'status': 'PASS', 'source_pin': bindings['source_pin'],
    'fixture_sha256': sha(HERE / 'fixture_monolithic.lean'),
    'generator_bindings': bindings, 'partition_function_byte_identical': True,
    'emitted_files': len(rows), 'byte_identical_to_original': 14,
    'byte_identical_to_checked_batch_overlays': 4, 'files': rows,
    'scope': ('The original partition and modified writer were replayed on an exact '
              'fixture reconstructed from pinned source files. Full certificate '
              'inference was not rerun, and no additional Lean compilation was needed '
              'because all 18 emitted sources match already-checked sources.'),
}
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
