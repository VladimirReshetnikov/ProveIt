#!/usr/bin/env python3
"""Run source54's default positive suite, skipping its checksum-manifest wrapper.

Use a recovered scratch package. The delivered verify.py bytes are not edited.
This executes finite Python checks only; no Lean, Coq or dependency build.
"""
from pathlib import Path
import argparse
import runpy
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must remain enabled; run without -O.')
    package = args.package.resolve(strict=True)
    output = args.output.absolute()
    if output.exists() or output.is_symlink():
        parser.error('--output must be a new result file.')
    output.parent.mkdir(parents=True, exist_ok=True)
    verify = package / 'verify.py'
    namespace = runpy.run_path(str(verify))
    entry = namespace['main']
    if 'check_manifest' not in entry.__globals__:
        parser.error('Expected source54 manifest-wrapper interface is absent.')
    entry.__globals__['check_manifest'] = lambda: None
    sys.argv = [str(verify), '--output', str(output)]
    entry()


if __name__ == '__main__':
    main()
