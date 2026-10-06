#!/usr/bin/env python3
"""Replay a sealed Report 128 bundle in a clean copy; keep all source bytes immutable."""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def snapshot(root):
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'SYMLINK_IN_REPLAY_SOURCE')
        if path.is_file():
            result[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def run(root, script, optimized=False, args=(), timeout=900):
    command = [sys.executable, '-B'] + (['-O'] if optimized else [])
    command += [str(root/script), *map(str, args)]
    result = subprocess.run(command, cwd=root, capture_output=True, timeout=timeout)
    require(result.returncode == 0,
            'REPLAY_COMMAND_FAILED: '+script+'\n'+(result.stdout+result.stderr).decode(errors='replace'))
    return result.stdout


def main():
    run(ROOT, 'integrity.py')
    before = snapshot(ROOT)
    receipt = json.loads((ROOT/'verification_results.json').read_text())
    require(receipt['status'] == 'PASS', 'RECEIPT_NOT_PASS')
    for name, digest in receipt['article_sha256'].items():
        require(before.get(name) == digest, 'RECEIPT_ARTICLE_MISMATCH: '+name)
    with tempfile.TemporaryDirectory(prefix='report128-clean-replay-') as td:
        tmp = Path(td)
        copy = tmp/'report128'
        shutil.copytree(ROOT, copy)
        require(snapshot(copy) == before, 'INITIAL_COPY_MISMATCH')
        run(copy, 'integrity.py')
        normal = run(copy, 'checks/check_exact.py')
        optimized = run(copy, 'checks/check_exact.py', optimized=True)
        require(normal == optimized, 'NORMAL_OPTIMIZED_EXACT_MISMATCH')
        require(normal == (copy/'checks/exact_results.json').read_bytes(), 'EXACT_RECEIPT_MISMATCH')
        exact = json.loads(normal)
        require(exact['status'] == 'PASS' and exact['infinite_limits_certified'] is False,
                'EXACT_STATUS_OR_SCOPE_INVALID')
        audit = run(copy, 'checks/test_exact.py')
        audit_optimized = run(copy, 'checks/test_exact.py', optimized=True)
        require(audit == audit_optimized, 'NORMAL_OPTIMIZED_AUDIT_MISMATCH')
        require(audit == (copy/'checks/audit_results.json').read_bytes(), 'AUDIT_RECEIPT_MISMATCH')
        audit_result = json.loads(audit)
        require(audit_result['status'] == 'PASS', 'EXACT_AUDIT_NOT_PASS')
        outer = run(copy, 'test_integrity.py')
        outer_optimized = run(copy, 'test_integrity.py', optimized=True)
        require(outer == outer_optimized, 'OUTER_OPTIMIZED_MISMATCH')
        outer_result = json.loads(outer)
        require(outer_result == receipt['outer_inventory_tests'], 'OUTER_RECEIPT_MISMATCH')
        build_output = run(copy, 'build.py').decode().strip()
        require(snapshot(copy) == before, 'REPLAY_MUTATED_COPY')
        first, second = tmp/'one.zip', tmp/'two.zip'
        run(copy, 'repack.py', args=[first])
        run(copy, 'repack.py', args=[second])
        require(first.read_bytes() == second.read_bytes(), 'ZIP_NONDETERMINISTIC')
        with zipfile.ZipFile(first) as archive:
            expected = ['report128/'+name for name in sorted(before)]
            require(archive.namelist() == expected, 'ZIP_CLOSED_INVENTORY_MISMATCH')
            require(archive.testzip() is None, 'ZIP_CRC_FAILURE')
            destination = tmp/'extracted'
            archive.extractall(destination)
        require(snapshot(destination/'report128') == before, 'ZIP_ROUNDTRIP_MISMATCH')
        run(destination/'report128', 'integrity.py')
        result = {
            'status': 'PASS',
            'package_file_count_including_manifest': len(before),
            'exact_checks_normal_optimized_and_receipt_identical': True,
            'exact_result_sha256': hashlib.sha256(normal).hexdigest(),
            'exact_adversarial_cases': len(audit_result['cases']),
            'exact_audit_normal_optimized_and_receipt_identical': True,
            'exact_audit_sha256': hashlib.sha256(audit).hexdigest(),
            'outer_inventory_tests': outer_result,
            'build': build_output,
            'article_sha256': receipt['article_sha256'],
            'deterministic_zip_sha256': hashlib.sha256(first.read_bytes()).hexdigest(),
            'zip_closed_inventory_crc_roundtrip': True,
            'clean_copy_immutable': True,
            'source_package_immutable': True,
        }
    require(snapshot(ROOT) == before, 'REPLAY_MUTATED_SOURCE')
    run(ROOT, 'integrity.py')
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
