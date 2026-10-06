#!/usr/bin/env python3
"""Verify, rebuild, extract, and repack this package without modifying its sources.
Requires Python 3.10+, pdfTeX, and the TeX packages listed in report121.tex.
All temporary work and ZIPs are outside the package. No network is used.
"""
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def run(root, name, *args, optimize=False, timeout=240):
    cmd = [sys.executable, '-B'] + (['-O'] if optimize else []) + [str(root/name), *map(str,args)]
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    cp = subprocess.run(cmd, cwd=root, env=env, capture_output=True, timeout=timeout)
    need(cp.returncode == 0, f'REPLAY_COMMAND_FAILED {name}: '+(cp.stdout+cp.stderr).decode(errors='replace'))
    return cp.stdout

def main():
    run(ROOT, 'integrity.py')
    expected = (ROOT/'verification_results.json').read_bytes()
    normal = run(ROOT, 'checks/verify.py')
    optimized = run(ROOT, 'checks/verify.py', optimize=True)
    need(normal == optimized == expected, 'CHECKER_OUTPUT_MISMATCH')
    mutations = json.loads(run(ROOT, 'checks/mutation_tests.py', timeout=300))
    outer = json.loads(run(ROOT, 'test_integrity.py'))
    before = (ROOT/'report121.pdf').read_bytes()
    run(ROOT, 'build.py', timeout=480)
    need((ROOT/'report121.pdf').read_bytes() == before, 'DELIVERED_PDF_REBUILD_MISMATCH')
    run(ROOT, 'integrity.py')
    with tempfile.TemporaryDirectory(prefix='report121-roundtrip-') as td:
        work=Path(td)
        first=work/'first.zip'
        run(ROOT, 'pack.py', first)
        with zipfile.ZipFile(first) as archive:
            for info in archive.infolist():
                parts=Path(info.filename).parts
                need(parts and parts[0]=='report121' and '..' not in parts
                     and not Path(info.filename).is_absolute(), 'UNSAFE_ZIP_MEMBER')
            archive.extractall(work/'extracted')
        copy=work/'extracted'/'report121'
        run(copy, 'integrity.py')
        need(run(copy, 'checks/verify.py') == expected, 'EXTRACTED_CHECKER_MISMATCH')
        need(run(copy, 'checks/verify.py', optimize=True) == expected, 'EXTRACTED_OPTIMIZED_MISMATCH')
        run(copy, 'build.py', timeout=480)
        need((copy/'report121.pdf').read_bytes() == before, 'EXTRACTED_PDF_MISMATCH')
        run(copy, 'integrity.py')
        second=work/'second.zip'
        run(copy, 'pack.py', second)
        need(first.read_bytes() == second.read_bytes(), 'ZIP_REPACK_MISMATCH')
        zip_hash=sha256(first.read_bytes()).hexdigest()
    run(ROOT, 'integrity.py')
    print(json.dumps({
        'status':'PASS',
        'normal_optimized_and_reference_checker_bytes_equal':True,
        'mathematical_negative_tests':mutations,
        'outer_inventory_negative_tests':outer,
        'delivered_pdf_matches_two_clean_builds':True,
        'fresh_extraction_checker_pass':True,
        'fresh_extraction_two_clean_builds_match_pdf':True,
        'fresh_repack_bytes_equal':True,
        'pdf_sha256':sha256(before).hexdigest(),
        'zip_sha256':zip_hash,
        'checker_output_sha256':sha256(expected).hexdigest()
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
