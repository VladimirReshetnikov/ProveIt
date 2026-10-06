#!/usr/bin/env python3
"""Immutable offline replay of Report 129 and its unchanged Report 127 input.
Uses only local sources. Requires Python 3 and the TeX toolchain for PDF replay.
"""
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

def run(root, script, *args, optimize=False, timeout=2400):
    command = [sys.executable, '-B'] + (['-O'] if optimize else [])
    command += [str(root / script), *map(str, args)]
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    cp = subprocess.run(command, cwd=root, env=env, capture_output=True, timeout=timeout)
    require(cp.returncode == 0, 'REPLAY_FAILED ' + script + ': ' +
            (cp.stdout + cp.stderr).decode(errors='replace'))
    return cp.stdout

def verify_copy(root, work, label, skip_pdf):
    run(root, 'integrity.py')
    expected = (root / 'data/verification_results.json').read_bytes()
    expected_negative = (root / 'data/negative_results.json').read_bytes()
    for opt, mode in [(False, 'normal'), (True, 'optimized')]:
        out = work / (label + '-' + mode + '.json')
        run(root, 'checks/verify.py', '--output', out, optimize=opt)
        require(out.read_bytes() == expected, label + '_CHECKER_REFERENCE_BYTE_MISMATCH')
    for opt, mode in [(False, 'normal'), (True, 'optimized')]:
        out = work / (label + '-negative-' + mode + '.json')
        run(root, 'checks/negative_tests.py', '--output', out, optimize=opt)
        require(out.read_bytes() == expected_negative, label + '_NEGATIVE_REFERENCE_BYTE_MISMATCH')
    outer = json.loads(run(root, 'test_integrity.py'))
    pdf = (root / 'report129.pdf').read_bytes()
    if not skip_pdf:
        rebuilt = work / (label + '-rebuilt.pdf')
        run(root, 'build.py', '--output', rebuilt)
        require(rebuilt.read_bytes() == pdf, label + '_DELIVERED_PDF_BYTE_MISMATCH')
    old = root / 'earlier-inputs/report127'
    old_result = work / (label + '-report127-replay.json')
    old_args = ['--output', old_result] + (['--skip-pdf'] if skip_pdf else [])
    run(old, 'reproduce.py', *old_args)
    old_report = json.loads(old_result.read_text())
    require(old_report['status'] == 'PASS', label + '_EARLIER_INPUT_REPLAY_FAILED')
    run(root, 'integrity.py')
    return outer, old_report

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--skip-pdf', action='store_true')
    args = ap.parse_args()
    if args.output:
        require(not args.output.resolve().is_relative_to(ROOT), 'OUTPUT_INSIDE_PACKAGE')
        require(not args.output.exists() and not args.output.is_symlink(), 'OUTPUT_ALREADY_EXISTS')
    run(ROOT, 'integrity.py')
    with tempfile.TemporaryDirectory(prefix='report129-replay-') as td:
        work = Path(td)
        outer, old = verify_copy(ROOT, work, 'original', args.skip_pdf)
        first = work / 'first.zip'
        run(ROOT, 'repack.py', first)
        with zipfile.ZipFile(first) as archive:
            for member in archive.infolist():
                rel = Path(member.filename)
                require(rel.parts and rel.parts[0] == 'report129' and
                        '..' not in rel.parts and not rel.is_absolute(), 'UNSAFE_ZIP_MEMBER')
                require((member.external_attr >> 16) & 0o170000 != 0o120000, 'SYMLINK_ZIP_MEMBER')
            archive.extractall(work / 'extracted')
        copy = work / 'extracted/report129'
        other_outer, other_old = verify_copy(copy, work, 'extracted', args.skip_pdf)
        require(other_outer == outer, 'EXTRACTED_OUTER_NEGATIVE_MISMATCH')
        require(other_old == old, 'EXTRACTED_EARLIER_REPLAY_MISMATCH')
        second = work / 'second.zip'
        run(copy, 'repack.py', second)
        require(first.read_bytes() == second.read_bytes(), 'ZIP_REPACK_BYTE_MISMATCH')
        result = {
            'status': 'PASS',
            'normal_and_optimized_checker_reference_bytes_equal': True,
            'normal_and_optimized_negative_reference_bytes_equal': True,
            'outer_inventory_negative_tests': outer,
            'two_clean_pdf_builds_match': not args.skip_pdf,
            'fresh_extraction_checker_and_negative_reference_bytes_equal': True,
            'fresh_extraction_two_clean_pdf_builds_match': not args.skip_pdf,
            'unchanged_report127_full_replay': old,
            'fresh_extraction_report127_replay_equal': True,
            'fresh_repack_bytes_equal': True,
            'pdf_sha256': sha256((ROOT / 'report129.pdf').read_bytes()).hexdigest(),
            'tex_sha256': sha256((ROOT / 'report129.tex').read_bytes()).hexdigest(),
            'zip_sha256': sha256(first.read_bytes()).hexdigest(),
            'checker_output_sha256': sha256((ROOT / 'data/verification_results.json').read_bytes()).hexdigest(),
        }
    run(ROOT, 'integrity.py')
    encoded = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end='')

if __name__ == '__main__':
    main()
