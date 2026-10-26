#!/usr/bin/env python3
"""Verify the delivered files, without running archive-supplied prior code."""
from pathlib import Path
import hashlib,sys
root=Path(__file__).resolve().parents[1]
failures=[]
for line in (root/'SHA256SUMS').read_text().splitlines():
    expected,relative=line.split('  ',1)
    path=root/relative
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=expected:
        failures.append(relative)
if failures:
    print('FAIL:',*failures,sep='\n');sys.exit(1)
print('All delivered artifact hashes match.')
