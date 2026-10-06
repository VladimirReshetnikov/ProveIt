#!/usr/bin/env python3
"""Verify a sealed package, then replay every gate in an isolated clean copy."""
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
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob('*')) if p.is_file()}


def run(root, script, optimized=False, args=(), timeout=600):
    command = [sys.executable, '-B'] + (['-O'] if optimized else [])
    command += [str(root / script), *map(str, args)]
    result = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=timeout)
    require(result.returncode == 0,
            'REPLAY_COMMAND_FAILED: ' + script + '\n' + result.stdout + result.stderr)
    return result.stdout


def main():
    run(ROOT, 'integrity.py')
    before = snapshot(ROOT)
    receipt = json.loads((ROOT / 'verification_results.json').read_text())
    require(receipt['build']['pdf_sha256'] == before['report124.pdf'], 'RECEIPT_PDF_MISMATCH')
    require(receipt['build']['tex_sha256'] == before['report124.tex'], 'RECEIPT_TEX_MISMATCH')
    with tempfile.TemporaryDirectory(prefix='report124-clean-replay-') as td:
        tmp = Path(td)
        copy = tmp / 'report124'
        shutil.copytree(ROOT, copy)
        require(snapshot(copy) == before, 'INITIAL_COPY_MISMATCH')
        run(copy, 'integrity.py')
        normal = run(copy, 'checks/verify.py')
        optimized = run(copy, 'checks/verify.py', optimized=True)
        require(normal == optimized, 'NORMAL_OPTIMIZED_OUTPUT_MISMATCH')
        check_result = json.loads(normal)
        require(check_result.get('status') == 'PASS', 'FINITE_CHECKS_NOT_PASS')
        require(check_result == receipt['finite_checks'], 'FINITE_CHECK_RECEIPT_MISMATCH')
        negative = json.loads(run(copy, 'checks/negative_tests.py', timeout=900))
        negative_optimized = json.loads(run(copy, 'checks/negative_tests.py', optimized=True, timeout=900))
        require(negative == negative_optimized, 'NEGATIVE_RUNNER_OPTIMIZATION_MISMATCH')
        require(negative.get('status') == 'PASS', 'NEGATIVE_CAMPAIGN_NOT_PASS')
        require({k: negative[k] for k in receipt['negative_campaign_summary']} == receipt['negative_campaign_summary'], 'NEGATIVE_RECEIPT_MISMATCH')
        outer = json.loads(run(copy, 'test_integrity.py'))
        outer_optimized = json.loads(run(copy, 'test_integrity.py', optimized=True))
        require(outer == outer_optimized, 'OUTER_RUNNER_OPTIMIZATION_MISMATCH')
        require(outer == receipt['outer_inventory_tests'], 'OUTER_RECEIPT_MISMATCH')
        build_output = run(copy, 'build.py', timeout=900).strip()
        require(snapshot(copy) == before, 'REPLAY_MUTATED_COPY')
        first, second = tmp / 'one.zip', tmp / 'two.zip'
        run(copy, 'repack.py', args=[first])
        run(copy, 'repack.py', args=[second])
        require(first.read_bytes() == second.read_bytes(), 'ZIP_NONDETERMINISTIC')
        with zipfile.ZipFile(first) as archive:
            expected = ['report124/' + path for path in sorted(before)]
            require(archive.namelist() == expected, 'ZIP_INVENTORY_MISMATCH')
            require(archive.testzip() is None, 'ZIP_CRC_FAILURE')
            extracted = tmp / 'extracted'
            archive.extractall(extracted)
        require(snapshot(extracted / 'report124') == before, 'ZIP_ROUNDTRIP_MISMATCH')
        run(extracted / 'report124', 'integrity.py')
        result = {
            'status': 'PASS',
            'package_file_count_including_manifest': len(before),
            'normal_optimized_finite_checks_identical': True,
            'finite_checks': check_result,
            'negative_campaign': negative,
            'negative_runner_normal_optimized_identical': True,
            'outer_inventory_tests': outer,
            'build': build_output,
            'pdf_sha256': before['report124.pdf'],
            'deterministic_zip_sha256': hashlib.sha256(first.read_bytes()).hexdigest(),
            'zip_closed_inventory_crc_roundtrip': True,
            'clean_copy_immutable': True,
            'source_package_immutable': True,
        }
    require(snapshot(ROOT) == before, 'REPLAY_MUTATED_SOURCE')
    run(ROOT, 'integrity.py')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
