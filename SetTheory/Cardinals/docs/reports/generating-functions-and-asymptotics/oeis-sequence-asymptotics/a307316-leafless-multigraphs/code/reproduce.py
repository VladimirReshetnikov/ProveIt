#!/usr/bin/env python3
"""Immutable offline replay of exact checks, PDF and deterministic ZIP roundtrip."""
import sys
sys.dont_write_bytecode = True
from output_guard import external_output, write_external_bytes
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
        external_output(args.output,ROOT)
    run(ROOT, 'integrity.py')
    expected = (ROOT / 'checks/results-normal.json').read_bytes()
    require((ROOT/'checks/results-optimized.json').read_bytes()==expected,'REFERENCE_MODE_MISMATCH')
    pdf = (ROOT / 'report131.pdf').read_bytes()
    with tempfile.TemporaryDirectory(prefix='report131-replay-') as td:
        work = Path(td)
        for opt, label in [(False, 'normal'), (True, 'optimized')]:
            dest = work / (label + '.json')
            run(ROOT, 'checks/verify.py', '--output', dest, optimize=opt)
            require(dest.read_bytes() == expected, 'CHECKER_REFERENCE_BYTE_MISMATCH')
        outputs = json.loads(run(ROOT, 'test_output_guard.py'))
        outer = json.loads(run(ROOT, 'test_integrity.py'))
        outer_opt = json.loads(run(ROOT, 'test_integrity.py', optimize=True))
        require(outer_opt==outer,'OPTIMIZED_OUTER_NEGATIVE_MISMATCH')
        if not args.skip_pdf:
            dest = work / 'rebuilt.pdf'
            run(ROOT, 'build.py', '--output', dest, timeout=900)
            require(dest.read_bytes() == pdf, 'DELIVERED_PDF_BYTE_MISMATCH')
        first = work / 'first.zip'
        run(ROOT, 'repack.py', first)
        with zipfile.ZipFile(first) as archive:
            members=archive.infolist()
            names=[i.filename for i in members]
            require(len(names)==len(set(names)), 'DUPLICATE_ZIP_MEMBER')
            for member in members:
                rel = Path(member.filename)
                require(rel.parts and rel.parts[0] == 'report131' and
                        '..' not in rel.parts and not rel.is_absolute() and
                        '\\' not in member.filename, 'UNSAFE_ZIP_MEMBER')
                require((member.external_attr>>16)&0o170000 != 0o120000, 'ZIP_SYMLINK')
            archive.extractall(work / 'extracted')
        copy = work / 'extracted/report131'
        run(copy, 'integrity.py')
        for opt, label in [(False, 'extracted'), (True, 'extracted-optimized')]:
            dest = work / (label + '.json')
            run(copy, 'checks/verify.py', '--output', dest, optimize=opt)
            require(dest.read_bytes() == expected, 'EXTRACTED_CHECKER_BYTE_MISMATCH')
        extracted_outputs = json.loads(run(copy, 'test_output_guard.py'))
        require(extracted_outputs==outputs,'EXTRACTED_OUTPUT_GUARD_MISMATCH')
        extracted_outer = json.loads(run(copy, 'test_integrity.py'))
        extracted_outer_opt = json.loads(run(copy, 'test_integrity.py', optimize=True))
        require(extracted_outer==outer and extracted_outer_opt==outer, 'EXTRACTED_OUTER_NEGATIVE_MISMATCH')
        if not args.skip_pdf:
            dest = work / 'extracted-rebuilt.pdf'
            run(copy, 'build.py', '--output', dest, timeout=900)
            require(dest.read_bytes() == pdf, 'EXTRACTED_PDF_BYTE_MISMATCH')
        run(copy, 'integrity.py')
        second = work / 'second.zip'
        run(copy, 'repack.py', second)
        require(first.read_bytes() == second.read_bytes(), 'ZIP_REPACK_BYTE_MISMATCH')
        result = {
            'status': 'PASS',
            'normal_optimized_reference_bytes_equal': True,
            'checker_adversarial_tests_in_each_run': json.loads(expected)['adversarial_checks']['expected_rejections'],
            'outer_inventory_negative_tests': outer,
            'output_guard_negative_tests':outputs,
            'two_clean_pdf_builds_match': not args.skip_pdf,
            'fresh_extraction_normal_and_optimized_pass': True,
            'fresh_extraction_outer_mutations_equal': True,
            'fresh_extraction_two_clean_pdf_builds_match': not args.skip_pdf,
            'fresh_repack_bytes_equal': True,
            'pdf_sha256': sha256(pdf).hexdigest(),
            'zip_sha256': sha256(first.read_bytes()).hexdigest(),
            'checker_output_sha256': sha256(expected).hexdigest(),
        }
    run(ROOT, 'integrity.py')
    encoded = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        write_external_bytes(args.output,encoded.encode('utf-8'),ROOT)
    print(encoded, end='')

if __name__ == '__main__':
    main()
