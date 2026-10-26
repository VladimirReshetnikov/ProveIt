#!/usr/bin/env python3
"""Compare the Gap fixture's circuit-definition bytes with the pinned source.
This is a source-integrity check, not a replacement for Lean proof checking.
"""
from pathlib import Path
import argparse
import hashlib
import json
ap = argparse.ArgumentParser()
ap.add_argument('repository',type=Path)
args = ap.parse_args()
root = Path(__file__).resolve().parent.parent
meta = json.loads((root/'evidence/gap_fixture_source.json').read_text())
source = (args.repository/meta['source']).read_bytes()
fixture = (root/'lean'/meta['fixture_file']).read_bytes()
if hashlib.sha256(source).hexdigest() != meta['source_file_sha256']:
    raise SystemExit('Source hash differs from pinned source.')
i = meta['definition_byte_offset']; size = meta['definition_bytes']
j = meta['fixture_definition_offset']
extracted = source[i:i+size]
if hashlib.sha256(extracted).hexdigest() != meta['definition_sha256']:
    raise SystemExit('Source definition hash differs.')
if extracted != fixture[j:j+size]:
    raise SystemExit('Fixture definition differs from the pinned source bytes.')
print(f'PASS: {size} exact naturalNodes definition bytes match the pinned source.')
