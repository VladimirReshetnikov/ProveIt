#!/usr/bin/env python3
"""Check the pinned whole-file Git hash and the copied updater AST."""
import argparse
import ast
import hashlib
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--checkout', type=Path, required=True, help='ProveIt repository root')
args = parser.parse_args()
path = args.checkout / 'Topology/UnknotRecognition/fast/fastunknot/primitive_projection.py'
raw = path.read_bytes()
blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
expected = '0aff98067b485d285a9c8026fcac56ae9934edc0'
if blob != expected:
    raise SystemExit(f'Source differs from inspected blob: {blob}; review before integrating.')
reference = Path(__file__).resolve().parents[1] / 'src/anchored_unknot/reference_update.py'
def function(text):
    module = ast.parse(text)
    return next(node for node in module.body if isinstance(node, ast.FunctionDef) and node.name == 'apply_projection')
if ast.dump(function(raw.decode()), include_attributes=False) != ast.dump(function(reference.read_text()), include_attributes=False):
    raise SystemExit('Updater AST mismatch')
print(f'PASS: source blob {blob} and updater AST match')
