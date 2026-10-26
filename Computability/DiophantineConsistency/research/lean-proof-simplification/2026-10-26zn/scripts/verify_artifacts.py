#!/usr/bin/env python3
"""Verify the packet bytes, metrics, original snapshots, and four exact patches."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, tempfile

PACKET = Path(__file__).resolve().parents[1]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional receipt path outside the immutable packet')
    parser.add_argument('--skip-checksums', action='store_true', help='For archive assembly only')
    args = parser.parse_args()
    checked = 0
    if not args.skip_checksums:
        for line in (PACKET/'SHA256SUMS').read_text().splitlines():
            expected, relative = line.split('  ',1)
            assert digest(PACKET/relative) == expected, 'Checksum mismatch: '+relative
            checked += 1
    snapshot = json.loads((PACKET/'evidence/source_snapshot.json').read_text())
    for record in snapshot['files']:
        file = PACKET/'sources'/record['path']
        assert digest(file) == record['sha256'], record['path']
    metrics = json.loads((PACKET/'evidence/source_metrics.json').read_text())
    for record in metrics['files']:
        original = PACKET/'sources'/record['path']
        proposed = PACKET/'proposed'/record['path']
        assert digest(original) == record['original_sha256'], record['path']
        assert digest(proposed) == record['proposed_sha256'], record['path']
        assert len(original.read_bytes().splitlines()) == record['original_lines']
        assert len(proposed.read_bytes().splitlines()) == record['proposed_lines']
        assert record['original_lines']-record['proposed_lines'] == record['lines_removed']
    assert sum(r['lines_removed'] for r in metrics['files']) == metrics['total_lines_removed'] == 437
    applied = []
    with tempfile.TemporaryDirectory(prefix='proveit-patch-check-') as directory:
        checkout = Path(directory)
        shutil.copytree(PACKET/'sources', checkout, dirs_exist_ok=True)
        for patch in sorted((PACKET/'patches').glob('*.patch')):
            for mode in [['--check'], []]:
                subprocess.run(['git','apply',*mode,str(patch)],cwd=checkout,check=True,
                               stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            applied.append(patch.name)
        for record in metrics['files']:
            assert (checkout/record['path']).read_bytes() == (PACKET/'proposed'/record['path']).read_bytes(), record['path']
    result = {'status':'passed', 'checksums_verified':checked, 'source_snapshots_verified':len(snapshot['files']),
              'patches_applied_to_temporary_snapshot':applied, 'all_proposed_bytes_matched':True,
              'total_physical_lines_removed':437, 'production_lean_build_performed':False}
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
