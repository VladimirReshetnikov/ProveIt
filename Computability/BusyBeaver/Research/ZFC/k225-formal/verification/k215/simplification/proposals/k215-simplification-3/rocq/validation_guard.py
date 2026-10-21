"""Fail-closed runtime and exact source binding for research checkers.

These checks improve reproducibility; they do not constitute a kernel proof.
"""
import os
import sys


def ensure_safe_runtime():
    if not __debug__ or sys.flags.optimize != 0 or 'PYTHONOPTIMIZE' in os.environ:
        raise SystemExit('UNSAFE_PYTHON_OPTIMIZATION: run without -O/-OO and unset PYTHONOPTIMIZE; assertions are required.')


ensure_safe_runtime()

from pathlib import Path
import hashlib

BASELINE_COMMIT = 'b6fb232916d008383e7cf2990d68ddb30fded7db'
SOURCE_DIRECTORY = Path(__file__).resolve().parent / 'snapshot/rocq/rocq-extension/coq/215'
# Literal pins independently audited against Git blob/source_stats.json. The
# mutable metadata file is deliberately not an authority for these checks.
SOURCE_SHA256 = {
    'Cert215Offsets.v': '32197f6f31bd3c7c7bf5fb94af0e721434f1238d64a64a715b8c9d2cbdd4e728',
    'Prog215.v': '6cc81c19652b26467b584e5a9f550becfea10e550a7cadd416d64a616c05b010',
    'DagPerm.v': 'ba2b28487ae978bd27b0d804e9b2bde6d9adcd1dd575de55572465c050b86aa1',
}


def read_pinned_source_bytes(name):
    ensure_safe_runtime()
    if name not in SOURCE_SHA256:
        raise ValueError('UNPINNED_SOURCE: ' + name)
    data = (SOURCE_DIRECTORY / name).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    expected = SOURCE_SHA256[name]
    if actual != expected:
        raise SystemExit('SOURCE_SHA256_MISMATCH: ' + name + '; expected ' + expected + '; got ' + actual)
    return data


def read_pinned_source(name):
    return read_pinned_source_bytes(name).decode('utf-8')


# Imports also fail closed, before any checker parses data or writes outputs.
for _name in SOURCE_SHA256:
    read_pinned_source_bytes(_name)
