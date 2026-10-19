#!/usr/bin/env python3
"""Restore the pinned source-search dependency for optional new searches."""
import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE.parent / 'reference/zfc-below245-source-search-20261018.zip'
EXPECTED = 'd020de063fbcba82327b6b5db8b57ff8ce8df8d6eb24858bc67a73a0db3ded95'

def extract(destination):
    assert hashlib.sha256(ARCHIVE.read_bytes()).hexdigest() == EXPECTED
    destination.mkdir(parents=True, exist_ok=True)
    destination = destination.resolve()
    with zipfile.ZipFile(ARCHIVE) as z:
        for item in z.infolist():
            target = (destination / item.filename).resolve()
            if not target.is_relative_to(destination):
                raise ValueError('Archive path escapes requested extraction directory')
            if ((item.external_attr >> 16) & 0o170000) == 0o120000:
                raise ValueError('Symbolic links are not expected in this reference archive')
        z.extractall(destination)
    return destination / 'zfc-below245-source-search-20261018'

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, default=HERE/'build')
    p.add_argument('--syntax-only', action='store_true')
    a = p.parse_args()
    package = extract(a.output)
    if not a.syntax_only:
        subprocess.run([sys.executable, '-B', str(package/'prepare_experiments.py')],
                       cwd=package, check=True)
        subprocess.run(['c++', '-O3', '-std=c++17',
                        str(HERE/'anneal_fine_compound_hardened.cpp'),
                        '-o', str(HERE/'anneal_combined')], check=True)
    print(package)

if __name__ == '__main__':
    main()
