"""Reproduce the complete checker checks and metrics; optionally build the PDF."""
import argparse
import ast
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    subprocess.run([sys.executable, str(ROOT / 'code/verify_raw.py')], check=True)
    shutil.copyfile(ROOT / 'code/raw_verification.json', ROOT / 'evidence/raw_verification.json')
    for name in ('raw_parameter', 'raw_template_control'):
        tree = ast.parse((ROOT / 'code' / (name + '.py')).read_text())
        if (tree.body and isinstance(tree.body[0], ast.Expr)
                and isinstance(tree.body[0].value, ast.Constant)
                and isinstance(tree.body[0].value.value, str)):
            tree.body.pop(0)
        data = (ast.unparse(tree) + '\n').encode()
        (ROOT / 'code' / (name + '.normalized.py')).write_bytes(data)
        (ROOT / 'code' / (name + '.normalized.py.gz')).write_bytes(gzip.compress(data, mtime=0))
    if args.pdf:
        for _ in range(2):
            subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                            'ipra_parameter_substitution.tex'], cwd=ROOT, check=True)
    print('All supplied checks passed.')


if __name__ == '__main__':
    main()
