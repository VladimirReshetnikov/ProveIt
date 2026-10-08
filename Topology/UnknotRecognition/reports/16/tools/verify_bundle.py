#!/usr/bin/env python3
"""Verify the delivered manifest, Git baseline, measured inputs, and patch.

The default includes a patch application in a temporary directory when Git is
available. Use --no-patch to perform only read-only hash/provenance checks.
Neither mode writes to a user's repository. No benchmark is rerun.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

BUNDLE = Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def read(name):
    return json.loads((BUNDLE / name).read_text())


def measured_match(data, expected):
    """Only the documented single terminal transport LF may differ."""
    return expected in (sha(data), sha(data + b'\n'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-patch', action='store_true')
    args = parser.parse_args()
    results = {}
    manifest = read('manifest.json')
    for name, item in manifest['files'].items():
        data = (BUNDLE / name).read_bytes()
        assert len(data) == item['bytes'], ('size', name)
        assert sha(data) == item['sha256'], ('sha256', name)
    results['manifest_files'] = len(manifest['files'])

    baseline = read('provenance/baseline_files.json')
    for item in baseline:
        data = (BUNDLE / 'baseline/fast' / item['path']).read_bytes()
        assert git_blob(data) == item['git_blob_sha1'], item['path']
        assert sha(data) == item['canonical_sha256'], item['path']
        assert sha(data + b'\n') == item['measured_sha256'], item['path']
    results['exact_baseline_git_blobs'] = len(baseline)

    scanner = read('implementation/fast/paired_scanner_benchmark.json')
    metadata = scanner['metadata']
    for kind, folder in [('baseline', 'baseline/fast'), ('integrated', 'implementation/fast')]:
        for name, expected in metadata[kind + '_source_sha256'].items():
            data = (BUNDLE / folder / 'fastunknot' / name).read_bytes()
            assert measured_match(data, expected), (kind, name)
    for fixture in scanner['fixtures']:
        encoded = json.dumps(fixture['pd'], separators=(',', ':')).encode()
        assert sha(encoded) == fixture['pd_sha256'], fixture['name']
        source = fixture['source_input']
        if 'file' in source:
            data = (BUNDLE / 'implementation/fast' / source['file']).read_bytes()
            assert measured_match(data, source['sha256']), source['file']
        else:
            data = (BUNDLE / 'baseline/fast/hard_unknots.py').read_bytes()
            assert measured_match(data, source['generator_sha256']), 'hard_unknots.py'
        samples = fixture['samples']
        assert len(samples) == 15 and all(s['status'] == 'OK' for s in samples)
        outputs = {(s['rank'], s['reduced_rank'], json.dumps(s['by_degree'], sort_keys=True)) for s in samples}
        assert len(outputs) == 1, fixture['name']
    results['recorded_scanner_samples'] = sum(len(f['samples']) for f in scanner['fixtures'])

    qroot = BUNDLE / 'verification/finite_quotient'
    quotient = read('verification/finite_quotient/finite_quotient_benchmark.json')
    for fixture in quotient['fixtures']:
        assert sha((qroot / 'fixtures' / (fixture['name'] + '.json')).read_bytes()) == fixture['fixture_sha256']
    results['exact_quotient_fixture_hashes'] = len(quotient['fixtures'])
    local_manifest = read('verification/finite_quotient/artifact_manifest.json')
    for name, item in local_manifest['files'].items():
        data = (qroot / name).read_bytes()
        assert sha(data) == item['sha256'] and len(data) == item['bytes'], name
    results['quotient_artifact_hashes'] = len(local_manifest['files'])

    from build_patch import make_patch, files
    expected_patch, changed = make_patch()
    patch_file = BUNDLE / 'patches/fast_dense_algebra_and_a5.patch'
    assert patch_file.read_text() == expected_patch, 'patch text does not match trees'
    results['patch_changed_or_new_files'] = len(changed)
    if not args.no_patch:
        if not shutil.which('git'):
            raise RuntimeError('Git is needed for the patch-application check; use --no-patch to skip it.')
        with tempfile.TemporaryDirectory(prefix='unknot-patch-check-') as folder:
            work = Path(folder)
            target = work / 'Topology/UnknotRecognition/fast'
            shutil.copytree(BUNDLE / 'baseline/fast', target)
            for command in (['git', 'apply', '--check', str(patch_file)], ['git', 'apply', str(patch_file)]):
                completed = subprocess.run(command, cwd=work, capture_output=True, text=True)
                if completed.returncode:
                    raise RuntimeError(completed.stderr)
            actual, expected = files(target), files(BUNDLE / 'implementation/fast')
            assert actual.keys() == expected.keys(), 'patched file set'
            for name in actual:
                assert actual[name].read_bytes() == expected[name].read_bytes(), ('patched bytes', name)
        results['patch_application_matches_implementation'] = True
    results['status'] = 'PASS'
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
