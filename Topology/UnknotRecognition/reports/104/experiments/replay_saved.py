"""Replay a saved proof without importing any producer/normalizer/atlas module."""
import importlib.util
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('isolated_verifier',root/'src/private_cocore/verify.py')
module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
data=json.loads((root/'data/certificate-example.json').read_text())
real=[{int(h):w for h,w in row.items()} for row in data['real']]
passive=[{int(h):w for h,w in row.items()} for row in data['passive']]
assert module.verify_certificate(real,data['n_columns'],passive,data['certificate'],require_complete=True)
print('Saved certificate PASS; producer modules not imported.')
