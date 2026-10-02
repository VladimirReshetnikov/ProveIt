#!/usr/bin/env python3
"""Verify this distribution and rerun its checks in an isolated work directory.

Python 3.10+, SymPy and mpmath are required. Optional PDF rebuilding also needs
pdfLaTeX, kpsewhich and a POSIX shell. Poppler enables page/text comparison.
No network access, installation, or modification of the distributed files occurs.
"""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time


def verify_manifest(root):
    manifest = root / 'SHA256SUMS'
    verified = []
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest, relative = line.split('  ', 1)
        path = Path(relative)
        if path.is_absolute() or '..' in path.parts or not re.fullmatch(r'[0-9a-f]{64}', digest):
            raise ValueError('Invalid manifest entry: ' + relative)
        actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
        if actual != digest:
            raise ValueError('Checksum mismatch: ' + relative)
        verified.append(relative)
    if not verified:
        raise ValueError('Empty checksum manifest')
    return verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-pdf', action='store_true', help='rebuild PDF in isolation and compare with Poppler if installed')
    parser.add_argument('--output', type=Path, help='parent directory for unique replay run; default: .replay beside this script')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    verified = verify_manifest(root)
    print('Verified %d distributed file checksums' % len(verified), flush=True)
    parent = (args.output or root / '.replay').resolve()
    parent.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix=dt.datetime.now(dt.timezone.utc).strftime('run-%Y%m%dT%H%M%SZ-'), dir=parent))
    work = run / 'work'
    work.mkdir()
    shutil.copytree(root / 'code', work / 'code', ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    receipts = work / 'receipts'
    receipts.mkdir()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', LC_ALL='C')
    report = {'status': 'running', 'verified_files': verified, 'python': sys.version,
              'platform': platform.platform(), 'commands': [], 'pdf': {'requested': args.build_pdf}}

    def save():
        (run / 'replay-summary.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')

    def execute(command, cwd, logname):
        print('Running ' + ' '.join(command[1:] if command[0] == sys.executable else command), flush=True)
        start = time.perf_counter()
        result = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (run / logname).write_text(result.stdout, encoding='utf-8')
        report['commands'].append({'command': [Path(command[0]).name] + command[1:],
                                   'exit_status': result.returncode,
                                   'elapsed_seconds': round(time.perf_counter() - start, 3),
                                   'log': logname})
        save()
        if result.returncode:
            raise RuntimeError('Command failed; see ' + str(run / logname))
        print('PASS: ' + logname, flush=True)
        return result

    save()
    try:
        commands = [
            ['code/check_two_coefficients.py'],
            ['code/check_bell_comparison.py'],
            ['code/derive_residual.py', '--include-p3', '--order', '5', '--output', 'receipts/result-recomputed.json'],
            ['code/test_generator.py'],
            ['code/check_independent.py'],
            ['code/check_third_literal.py'],
            ['code/check_inverse.py'],
            ['code/check_numeric.py', '--max-n', '1500', '--output', 'receipts/numeric-recomputed.json'],
        ]
        for command in commands:
            execute([sys.executable] + command, work, Path(command[0]).stem + '.log')
        if args.build_pdf:
            shell = shutil.which('sh')
            if shell is None:
                raise RuntimeError('The optional PDF build requires a POSIX shell (sh)')
            build = run / 'pdf-build'
            build.mkdir()
            for name in ['takeuchi-asymptotics.tex', 'build.sh']:
                shutil.copy2(root / name, build / name)
            execute([shell, 'build.sh'], build, 'pdf-build.log')
            pdf = build / 'takeuchi-asymptotics.pdf'
            if not pdf.is_file() or not pdf.stat().st_size:
                raise RuntimeError('The PDF build did not produce a nonempty PDF')
            latex_log = (build / 'takeuchi-asymptotics.log').read_text(errors='replace')
            warnings = [line for line in latex_log.splitlines() if re.search(r'LaTeX Warning|Overfull \\|Underfull \\|undefined references', line)]
            report['pdf']['warnings'] = warnings
            if warnings:
                raise RuntimeError('The final LaTeX log contains warnings or box defects')
            pdfinfo = shutil.which('pdfinfo')
            if pdfinfo:
                info = execute([pdfinfo, 'takeuchi-asymptotics.pdf'], build, 'pdfinfo.log').stdout
                match = re.search(r'^Pages:\s+(\d+)', info, flags=re.MULTILINE)
                original_info = subprocess.run([pdfinfo, str(root / 'takeuchi-asymptotics.pdf')], env=env, capture_output=True, check=True, text=True).stdout
                original_match = re.search(r'^Pages:\s+(\d+)', original_info, flags=re.MULTILINE)
                if not match or not original_match or match.group(1) != original_match.group(1):
                    raise RuntimeError('Rebuilt and distributed PDF page counts differ')
                report['pdf']['pages'] = int(match.group(1))
            else:
                report['pdf']['pages'] = 'not checked; pdfinfo unavailable'
            pdftotext = shutil.which('pdftotext')
            if pdftotext:
                original = subprocess.run([pdftotext, '-layout', str(root / 'takeuchi-asymptotics.pdf'), '-'], env=env, capture_output=True, check=True).stdout
                rebuilt = subprocess.run([pdftotext, '-layout', str(pdf), '-'], env=env, capture_output=True, check=True).stdout
                if original != rebuilt:
                    raise RuntimeError('Rebuilt and distributed PDF layout text differ')
                report['pdf']['layout_text_identical'] = True
            else:
                report['pdf']['layout_text_identical'] = 'not checked; pdftotext unavailable'
            report['pdf']['build_status'] = 'passed'
        report['status'] = 'passed'
        save()
        print('All requested replay checks passed. Results: ' + str(run), flush=True)
    except Exception as exc:
        report['status'] = 'failed'
        report['error'] = str(exc)
        save()
        raise


if __name__ == '__main__':
    main()
