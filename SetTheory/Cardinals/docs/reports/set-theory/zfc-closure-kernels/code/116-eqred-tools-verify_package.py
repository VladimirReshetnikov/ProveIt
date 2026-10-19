#!/usr/bin/env python3
"""Verify all distributed payload bytes before replay."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
lines=(root/'SHA256SUMS').read_text().splitlines();seen=set()
for line in lines:
 expected,name=line.split('  ',1);p=root/name
 if name in seen or not p.is_file() or '..'in Path(name).parts:raise RuntimeError('invalid manifest path: '+name)
 seen.add(name)
 if hashlib.sha256(p.read_bytes()).hexdigest()!=expected:raise RuntimeError('hash mismatch: '+name)
actual={str(p.relative_to(root))for p in root.rglob('*')if p.is_file() and p.name!='SHA256SUMS' and '__pycache__'not in p.parts and p.suffix not in ('.aux','.log','.out','.toc')}
# Rebuilding LaTeX may create source.pdf in addition to the delivered report.pdf.
actual.discard('source.pdf')
if seen!=actual:raise RuntimeError('manifest coverage differs: '+repr(sorted(seen^actual)))
print(json.dumps({'valid':True,'files_verified':len(seen),'algorithm':'SHA-256'},indent=2))
