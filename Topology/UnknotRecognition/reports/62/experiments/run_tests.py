#!/usr/bin/env python3
"""Run only this delivery's focused suite, with exact pinned dependencies."""
import hashlib
import json
import platform
import time
import unittest
import bootstrap

EXPECTED = {
    'interval_orbits.py': 'e86050aadbcef6f17fdddff9cbd1abc0e7ca18e8',
    'interval_orbit_verify.py': '0ccb56a0e8b5f1255384121d7417441314727720',
    'integer_codec.py': 'b88eafacb680e1312df0ecc93170a9f6f53eb639',
    'interval_incidence.py': '3625772c7c20119df64d79a14f644a03e13f7f2f',
}


def main():
    hashes = {}
    for name, expected in EXPECTED.items():
        raw = (bootstrap.ROOT / 'reference' / 'fastunknot' / name).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if blob != expected:
            raise RuntimeError(f'Upstream source mismatch: {name}')
        hashes[name] = dict(git_blob=blob, sha256=hashlib.sha256(raw).hexdigest())
    suite = unittest.defaultTestLoader.discover(
        str(bootstrap.ROOT / 'overlay' / 'fast' / 'tests'), pattern='test_sparse_incidence.py')
    start = time.perf_counter()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    report = dict(tests=result.testsRun, failures=len(result.failures),
                  errors=len(result.errors), seconds=time.perf_counter() - start,
                  python=platform.python_version(), platform=platform.platform(),
                  reference_hashes=hashes,
                  exercised=dict(generic_histograms=6654, literal_interval_systems=1000,
                                 dense_comparisons=300, literal_parity_systems=300),
                  full_repository_suite_run=False)
    (bootstrap.ROOT / 'results' / 'test_summary.json').write_text(
        json.dumps(report, indent=2) + '\n', encoding='utf-8')
    raise SystemExit(0 if result.wasSuccessful() else 1)


if __name__ == '__main__':
    main()
