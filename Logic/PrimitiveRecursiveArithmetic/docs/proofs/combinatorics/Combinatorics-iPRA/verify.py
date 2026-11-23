#!/usr/bin/env python3
"""Re-run the supplied checks; pass --lean /path/to/lean or --python-only."""
import argparse
from pathlib import Path
import subprocess
import sys


def run(args, root):
    print('$ ' + ' '.join(map(str, args)), flush=True)
    subprocess.run(args, cwd=root, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--python-only', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if not args.python_only:
        run([args.lean, '--version'], root)
        for name in ('Bounded', 'WordCount', 'Handshaking', 'Kirkman', 'ThueMorse'):
            run([args.lean, f'lean/{name}.lean'], root)
    for script in sorted((root/'checks').glob('*.py')):
        run([sys.executable, script.relative_to(root)], root)
    print('All requested checks passed.')


if __name__ == '__main__':
    main()
