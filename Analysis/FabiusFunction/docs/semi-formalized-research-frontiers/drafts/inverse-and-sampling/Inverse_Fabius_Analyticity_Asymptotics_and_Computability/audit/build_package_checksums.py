#!/usr/bin/env python3
"""Compatibility entry point for the retired package-checksum workflow.

Repository policy no longer creates or validates package checksum manifests.
The script remains only so older documented commands terminate successfully
without writing or requiring a ledger.
"""

from __future__ import annotations

import argparse


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help=argparse.SUPPRESS)
    parser.parse_args()
    print("package checksum manifests are retired; nothing to build or check")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
