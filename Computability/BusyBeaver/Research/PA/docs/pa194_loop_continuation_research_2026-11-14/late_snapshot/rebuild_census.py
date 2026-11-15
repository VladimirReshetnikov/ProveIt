#!/usr/bin/env python3
"""Regenerate the separate latest census from the pinned Git objects.

Use --repo for a checkout containing commit603c58ca3bd6bf3222fcfc4e308e6b079f65d573
and --output for a fresh output directory. This never updates the initial
32d0d8b7 census shipped in comparison/.
"""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'comparison/census_tool'))
import audit_repository


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert args.output.resolve() != (ROOT / 'comparison').resolve()
    audit_repository.PIN = '603c58ca3bd6bf3222fcfc4e308e6b079f65d573'
    sys.argv = ['audit_repository.py', '--repo', str(args.repo), '--output', str(args.output)]
    audit_repository.main()


if __name__ == '__main__':
    main()
