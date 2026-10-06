#!/usr/bin/env python3
"""Immutable offline replay of exact checks, PDF and deterministic ZIP roundtrip."""
import sys
sys.dont_write_bytecode = True
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile
import zipfile
ROOT = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def run(root, script, *args, optimize=False, timeout=900):
    command = [sys.executable, '-B'] + (['-O'] if optimize else [])
    command += [str(root / script), *map(str, args)]
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    cp = subprocess.run(command, cwd=root, env=env, capture_output=True, timeout=timeout)
    require(cp.returncode == 0, 'REPLAY_FAILED ' + script + ': ' +
            (cp.stdout + cp.stderr).decode(errors='replace'))
    return cp.stdout

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--skip-pdf', action='store_true')
    args = ap.parse_args()
    if args.output:
        require(not args.output.resolve().is_relative_to(ROOT), 'OUTPUT_INSIDE_PACKAGE')
    run(ROOT, 'integrity.py')
    expected = (ROOT / 'data/verification_results.json').read_bytes()
    expected_negative = (ROOT / 'data/negative_results.json').read_bytes()
    pdf = (ROOT / 'report123.pdf').read_bytes()
    with tempfile.TemporaryDirectory(prefix='report123-replay-') as td:
        work = Path(td)
        for opt, label in [(False, 'normal'), (True, 'optimized')]:
            dest = work / (label + '.json')
            run(ROOT, 'checks/verify.py', '--output', dest, optimize=opt)
            require(dest.read_bytes() == expected, 'CHECKER_REFERENCE_BYTE_MISMATCH')
        negative = work / 'negative.json'
        run(ROOT, 'checks/negative_tests.py', '--output', negative, timeout=1800)
        require(negative.read_bytes() == expected_negative, 'NEGATIVE_REFERENCE_BYTE_MISMATCH')
        outer = json.loads(run(ROOT, 'test_integrity.py'))
        if not args.skip_pdf:
            dest = work / 'rebuilt.pdf'
            run(ROOT, 'build.py', '--output', dest, timeout=600)
            require(dest.read_bytes() == pdf, 'DELIVERED_PDF_BYTE_MISMATCH')
        first = work / 'first.zip'
        run(ROOT, 'repack.py', first)
        with zipfile.ZipFile(first) as archive:
            for member in archive.infolist():
                rel = Path(member.filename)
                require(rel.parts and rel.parts[0] == 'report123' and
                        '..' not in rel.parts and not rel.is_absolute(), 'UNSAFE_ZIP_MEMBER')
            archive.extractall(work / 'extracted')
        copy = work / 'extracted/report123'
        run(copy, 'integrity.py')
        for opt, label in [(False, 'extracted'), (True, 'extracted-optimized')]:
            dest = work / (label + '.json')
            run(copy, 'checks/verify.py', '--output', dest, optimize=opt)
            require(dest.read_bytes() == expected, 'EXTRACTED_CHECKER_BYTE_MISMATCH')
        if not args.skip_pdf:
            dest = work / 'extracted-rebuilt.pdf'
            run(copy, 'build.py', '--output', dest, timeout=600)
            require(dest.read_bytes() == pdf, 'EXTRACTED_PDF_BYTE_MISMATCH')
        run(copy, 'integrity.py')
        second = work / 'second.zip'
        run(copy, 'repack.py', second)
        require(first.read_bytes() == second.read_bytes(), 'ZIP_REPACK_BYTE_MISMATCH')
        result = {
            'status': 'PASS',
            'normal_optimized_reference_bytes_equal': True,
            'independent_negative_tests': json.loads(negative.read_text()),
            'outer_inventory_negative_tests': outer,
            'two_clean_pdf_builds_match': not args.skip_pdf,
            'fresh_extraction_normal_and_optimized_pass': True,
            'fresh_extraction_two_clean_pdf_builds_match': not args.skip_pdf,
            'fresh_repack_bytes_equal': True,
            'pdf_sha256': sha256(pdf).hexdigest(),
            'zip_sha256': sha256(first.read_bytes()).hexdigest(),
            'checker_output_sha256': sha256(expected).hexdigest(),
        }
    run(ROOT, 'integrity.py')
    encoded = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end='')

if __name__ == '__main__':
    main()
