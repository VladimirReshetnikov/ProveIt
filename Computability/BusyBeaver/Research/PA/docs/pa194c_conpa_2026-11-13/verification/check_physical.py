#!/usr/bin/env python3
"""Replay independent literal-tape verification for PA194C.

This imports the frozen independent checker, not the compiler or its arithmetic
oracle. Generic list-sweep lemmas are derived from the actual supplied rows.
Current-corpus novelty is separately checked by check_novelty.py.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REF = ROOT / 'reference/pa194'
sys.path.insert(0, str(REF / 'verification/independent'))
import check as v

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    out = ap.parse_args().output or Path(tempfile.mkdtemp(prefix='pa194c-physical-'))
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    job = {'family': 'PA194C', 'working_states': 194,
           'native': str(ROOT / 'tables/pa194C.native.tm'),
           'dense': str(ROOT / 'tables/pa194C.tm'),
           'labels': str(ROOT / 'tables/pa194C.labels.json'),
           'sites': str(ROOT / 'source/pa194C.sites.json'),
           'instructions': str(ROOT / 'source/pa194C.instructions.json'),
           'reference_instructions': str(ROOT / 'reference/cached/parent195C.source.instructions.json'),
           'native_sha256': 'b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c',
           'dense_sha256': 'd759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b',
           'startup_steps': 57922, 'source_sites': 3649, 'source_contracts': 4749,
           'physical_map': [6, 2, 0, 4, 3, 7, 8, 5, 1]}
    old = v.reference_classes()
    for name in ['pa194', 'pa194_AD']:
        rows, states, halt = v.parse(REF / ('construction/tables/' + name + '.tm'), 194)
        old.append((v.unrooted(rows, states, halt)[0], (rows, states, halt)))
    receipt = v.check(job, old, out)
    assert receipt['source_contracts'] == 4749
    assert receipt['symbolic_steps'] == 1096302
    assert receipt['maximum_symbolic_steps'] == 403
    assert receipt['minimum_positive_duration_constant'] == 3
    assert receipt['contracts_sha256'] == '5890f8c8564c6743f7cfeae411e9be3be79e89795129ad8854909eb2d3c3e2bf'
    print('Physical verification passed; current-corpus novelty is a separate certificate.')
    print('Fresh evidence:', out)

if __name__ == '__main__': main()
