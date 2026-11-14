#!/usr/bin/env python3
"""Compile the two reports with pdflatex; retain only the final PDFs."""
from pathlib import Path
import argparse
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', default='pdflatex')
    args = parser.parse_args()
    engine = shutil.which(args.engine)
    if not engine:
        raise SystemExit(f'{args.engine} not found; install a standard TeX distribution.')
    for stem in ['pa194_qns_research', 'calculus_proofs']:
        with tempfile.TemporaryDirectory(prefix=stem + '-tex-') as tmp:
            command = [engine, '-interaction=nonstopmode', '-halt-on-error',
                       '-file-line-error', '-output-directory=' + tmp, stem + '.tex']
            for pass_number in range(4):
                result = subprocess.run(command, cwd=ROOT / 'report', text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                if result.returncode:
                    print(result.stdout)
                    raise SystemExit(result.returncode)
                current_log = (Path(tmp) / (stem + '.log')).read_text(errors='replace')
                rerun = any(message in current_log for message in
                            ['Label(s) may have changed', 'Rerun to get', 'Rerun LaTeX'])
                if pass_number >= 1 and not rerun:
                    break
            log = (Path(tmp) / (stem + '.log')).read_text(errors='replace')
            warnings = [line for line in log.splitlines()
                        if 'Overfull' in line or 'undefined' in line or 'Warning:' in line]
            target = ROOT / 'report' / (stem + '.pdf')
            shutil.copy2(Path(tmp) / (stem + '.pdf'), target)
            print(f'Built {target.name}: {target.stat().st_size:,} bytes')
            if warnings:
                print('\n'.join(warnings))


if __name__ == '__main__':
    main()
