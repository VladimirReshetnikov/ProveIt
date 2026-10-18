#!/usr/bin/env python3
"""Frozen inputs and source instruction semantics for the prefix250 checks.

Original binary machine: Mira-Cult; verification: Jeff; compiler: Wade.
Physical permutation252 and the retained strict affine checker: ProveIt.
See ../sources/provenance.json and ../NOTICE.txt for attribution.
"""
from pathlib import Path
import hashlib
import json
from regenerate import construct, parse

ROOT = Path(__file__).resolve().parents[1]
PHYS = (6, 2, 0, 4, 3, 7, 8, 5, 1)
PROGRAM_SHA = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
SITES_SHA = 'dc6853f57bc48b834c2a635a82dfad8e344dd324ca11ef8e70ae2f36d66be357'

def build():
    """Return the final original-label table, checked against its frozen bytes."""
    _, table, _, _, old, _ = construct()
    assert old == (ROOT/'machine/zfc_prefix250_old.tm').read_bytes()
    return table

def sites():
    """Check the frozen site list against a fresh traversal of literal Prog254."""
    from check_candidate250 import program_sites
    program = ROOT/'sources/Prog254.v'
    sitepath = ROOT/'sources/instruction-sites.json'
    assert hashlib.sha256(program.read_bytes()).hexdigest() == PROGRAM_SHA
    assert hashlib.sha256(sitepath.read_bytes()).hexdigest() == SITES_SHA
    decoded = [(pc, op, PHYS[r] if op in ('CI', 'CD') else r)
               for pc, op, r in program_sites(program)]
    frozen = [tuple(row) for row in json.loads(sitepath.read_text())]
    assert decoded == frozen and len(frozen) == 6460
    assert max(len(pc) for pc, op, r in frozen) == 34
    return frozen

def inc(path):
    """Binary successor, dropping trailing zeros; None denotes overflow."""
    if '0' not in path:
        return None
    return path[:path.rindex('0')] + '1'

def strip(path, bit, count):
    while path and count:
        count -= path[-1] == bit
        path = path[:-1]
    return path

