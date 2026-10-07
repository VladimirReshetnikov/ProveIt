#!/usr/bin/env python3
"""Reproduce all numerical certificates in normal and optimized Python.

Both subprocesses use -S, disabling site-package imports. Every output must
match both modes and the supplied reference certificate byte for byte.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def run(root, output_dir):
    reference = root/'certificates'
    script = root/'code'/'run_all.py'
    names = sorted(p.name for p in reference.glob('*.json'))
    require('summary.json' in names, 'reference certificates are missing')
    for label, flags in [('normal', []), ('optimized', ['-O'])]:
        destination = output_dir/label
        bootstrap = ('import runpy,sys; from pathlib import Path; '
                     'script=sys.argv.pop(1); '
                     'sys.path.insert(0,str(Path(script).resolve().parent)); '
                     'runpy.run_path(script,run_name="__main__")')
        process = subprocess.run([sys.executable, '-I', '-S', '-B', *flags, '-c', bootstrap,
                                  str(script), '--output-dir', str(destination)],
                                 cwd=output_dir, capture_output=True, text=True, check=False,
                                 env={'PATH': os.defpath, 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'})
        require(process.returncode == 0, label+' reproduction failed:\n'+process.stderr)
        produced = sorted(p.name for p in destination.glob('*.json'))
        require(produced == names, label+' output file set differs from reference')
        for name in names:
            require((destination/name).read_bytes() == (reference/name).read_bytes(),
                    label+' byte mismatch: '+name)
    return {'status': 'PASS', 'standard_library_only': True,
            'normal_and_optimized_identical_to_reference': True,
            'certificate_file_count': len(names),
            'certificate_sha256': {name: hashlib.sha256((reference/name).read_bytes()).hexdigest()
                                   for name in names}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if args.output_dir is not None:
        output_dir = args.output_dir.resolve()
        output_dir.mkdir(parents=True, exist_ok=True)
        result = run(root, output_dir)
    else:
        with tempfile.TemporaryDirectory(prefix='report183-replay-') as temporary:
            result = run(root, Path(temporary))
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
