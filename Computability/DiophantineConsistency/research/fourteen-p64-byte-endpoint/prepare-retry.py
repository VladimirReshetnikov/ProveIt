#!/usr/bin/env python3
"""Prepare a guarded selected-provider union for the P64 byte client."""
import hashlib
import json
import os
import subprocess
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
P64 = Path('/tmp/p64-independent-captured-replay/lib')
BYTE_ROOT = Path('/tmp/compact44-four-port-byte-assembly2-bdss6bu0')
MANIFEST = RESEARCH / 'ordinary12-ipra-bridge/compact44-four-port-byte-assembly2/observations/prepare-attempt01/manifest.json'
OUT = Path('/tmp/p64-byte-endpoint-join02')
MANIFEST_SHA = '14edb04f5ec3bf572cf8a1cf07c35a80d0ac0b5726c3e4affac6797d57d82c42'
ENDPOINT_SHA = '9416a700b41ca923ad20ad90ef27fc275d99dae7cc59ad3e91d82bf720b8b59d'
BYTE_SHA = '0f921668ce8407f4a28346a85e2023d131fc4421e00c790048ac2d813f8e3a85'
SOURCE_SHA = '7fec84e36daf125568ed00f3b26bbd06095878288a7de0f81ca678802ba4844a'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

if OUT.exists():
    raise SystemExit('refusing existing output directory')
assert sha(MANIFEST) == MANIFEST_SHA
assert sha(HERE / 'P64ByteEndpoint.lean') == SOURCE_SHA
assert sha(P64 / 'DiophantineConsistency/Compact44/IPRAPositive64.olean') == ENDPOINT_SHA
assert sha(BYTE_ROOT / 'CompactFourPortByteAssembly2.olean') == BYTE_SHA
m = json.loads(MANIFEST.read_text())
files = m['files']
assert len(files) == 631
shared, new, guards = [], [], {}
for rel, item in files.items():
    bp = BYTE_ROOT / 'lib' / rel
    assert bp.is_file() and sha(bp) == item['sha256'], rel
    guards[str(bp)] = item['sha256']
    ap = P64 / rel
    if ap.is_file():
        assert sha(ap) == item['sha256'], 'provider conflict: ' + rel
        shared.append(rel)
        guards[str(ap)] = item['sha256']
    else:
        new.append(rel)
for rel in files:
    if not rel.endswith('.olean'):
        continue
    stem = rel[:-len('.olean')]
    for ext in ('.ilean', '.ir', '.olean.private', '.olean.server', '.ilean.hash',
                '.ir.hash', '.olean.hash', '.olean.private.hash', '.olean.server.hash'):
        candidate = stem + ext
        assert candidate in files or not (P64 / candidate).is_file(), 'foreign companion: ' + candidate
assert len(shared) == 609 and len(new) == 22
OUT.mkdir()
(OUT / 'lib').mkdir()
subprocess.run(['cp', '-as', str(P64) + '/.', str(OUT / 'lib')], check=True)
for rel in new:
    target = OUT / 'lib' / rel
    assert not os.path.lexists(target), rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.symlink_to((BYTE_ROOT / 'lib' / rel).resolve(strict=True))
target = OUT / 'lib/CompactFourPortByteAssembly2.olean'
if os.path.lexists(target):
    assert target.is_file() and sha(target) == BYTE_SHA, 'byte assembly overlap mismatch'
else:
    target.symlink_to((BYTE_ROOT / 'CompactFourPortByteAssembly2.olean').resolve(strict=True))
guards[str(P64 / 'DiophantineConsistency/Compact44/IPRAPositive64.olean')] = ENDPOINT_SHA
guards[str(BYTE_ROOT / 'CompactFourPortByteAssembly2.olean')] = BYTE_SHA
plan = {'byte_manifest_sha256': MANIFEST_SHA, 'source_sha256': SOURCE_SHA,
        'endpoint_sha256': ENDPOINT_SHA, 'byte_assembly_sha256': BYTE_SHA,
        'selected': len(files), 'shared': len(shared), 'new': len(new),
        'shared_names': shared, 'new_names': new, 'guards': guards,
        'foreign_companions': 0, 'scope': 'selected provider union; full ancestry inherited'}
(OUT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
print(json.dumps({'status': 'PASS', 'selected': len(files), 'shared': len(shared),
                  'new': len(new), 'foreign_companions': 0}, sort_keys=True))
