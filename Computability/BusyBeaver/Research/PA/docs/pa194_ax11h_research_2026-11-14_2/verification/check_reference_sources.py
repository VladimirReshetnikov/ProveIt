#!/usr/bin/env python3
"""Check saved source bytes against the pinned source-identity manifests.

This is an input-integrity audit, not a Lean build or a mathematical proof checker.
No checkout or network access is required.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]

def read(path):
    return json.loads(path.read_text())

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def verify(path, git=None, sha256=None, size=None):
    data = path.read_bytes()
    if git is not None:
        assert blob(data) == git, str(path)
    if sha256 is not None:
        assert hashlib.sha256(data).hexdigest() == sha256, str(path)
    if size is not None:
        assert len(data) == size, str(path)

def main(output):
    assert __debug__ and not sys.flags.optimize, 'Run without Python -O.'
    counts = {}
    base = ROOT / 'research/calibration_forward'
    entries = read(base / 'source_manifest.json')['sources']
    for e in entries:
        local = e['path'].split('/jamesyc-upstream/pa196/', 1)[1]
        verify(base / 'source' / local, git=e['sha'])
    counts['calibration_forward'] = len(entries)
    base = ROOT / 'research/calibration_terms'
    entries = read(base / 'source_manifest.json')
    for local, e in entries.items():
        verify(base / 'source' / local, git=e['git_blob'], size=e['bytes'])
    counts['calibration_terms'] = len(entries)
    for name in ('reverse_soundness', 'q_exchange'):
        base = ROOT / 'references' / name
        entries = read(base / 'manifest.json')['files']
        for e in entries:
            verify(base / e['local_path'], git=e.get('git_blob_sha1'), sha256=e['sha256'])
        counts[name] = len(entries)
    base = ROOT / 'research/foundation_calibration/references'
    entries = read(base / 'manifest.json')['files']
    for e in entries:
        verify(base / e['local'], sha256=e['sha256'])
    counts['foundation_adapter_references'] = len(entries)
    base = ROOT / 'research/foundation_calibration/current_endpoint'
    for manifest, folder, name in [('manifest.json', 'source', 'current_foundation'),
                                   ('historical_manifest.json', 'historical', 'historical_foundation')]:
        entries = read(base / manifest)['source']
        for local, git in entries.items():
            verify(base / folder / local, git=git)
        counts[name] = len(entries)
    base = base / 'native_endpoint'
    entries = read(base / 'manifest.json')['files']
    for e in entries:
        verify(base / e['local'], git=e['git_blob_sha1'], sha256=e['sha256'])
    counts['native_endpoint'] = len(entries)
    base = ROOT / 'research/foundation_calibration'
    frozen = read(base / 'artifact_manifest.json')['files']
    for e in frozen:
        verify(base / e['path'], sha256=e['sha256'], size=e['bytes'])
    result = {'status': 'PASS',
              'scope': 'Pinned saved-source byte identities and frozen Foundation artifacts; not a proof-assistant replay',
              'repository_commit': '1c9524d8bf2e0a27b9a16ff622359927f536e663',
              'foundation_commit': '32e1a0956a8622fad067328ca1959729a7634428',
              'source_groups': counts, 'source_instances': sum(counts.values()),
              'frozen_foundation_artifacts': len(frozen), 'kernel_checked': False}
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    main(p.parse_args().output)
