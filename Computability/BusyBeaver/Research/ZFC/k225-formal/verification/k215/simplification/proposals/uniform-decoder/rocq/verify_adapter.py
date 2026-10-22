#!/usr/bin/env python3
"""Focused Coq 8 check of the adapter using pinned archived arithmetic modules.

This is not a production Rocq 9.1 or complete endpoint check. The sole source
compatibility edit is 'From Stdlib' -> 'From Coq' in the adapter import.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--repo', type=Path, required=True)
ap.add_argument('--coq-bin', type=Path, required=True)
ap.add_argument('--build', type=Path, default=Path(__file__).with_name('adapter_build'))
a = ap.parse_args()
here = Path(__file__).resolve().parent
source = a.repo / ('Computability/BusyBeaver/Research/ZFC/k225-formal/verification/'
                 'k215/simplification/proposals/checked-transport/rocq_seed_rank/source')
pins = {
    'K230S/KCode230.v': 'bf7f032ca4408f50dcee14d2b49d113fb442a717b585f0cfdfe48bf14e4908be',
    'K230L/Codes230.v': '09ad45fa4d67885f293a0709e13a7e0ea0e16b5d2094bbc1bb98aea0e7bce06a',
}
sha = lambda raw: hashlib.sha256(raw).hexdigest()
files = {}
for path, digest in pins.items():
    raw = (source / path).read_bytes()
    if sha(raw) != digest:
        raise ValueError('dependency changed: ' + path)
    files[path] = raw
files['K215F/DominatedImplication.v'] = (here / 'DominatedImplication.v').read_bytes()
adapter = (here / 'DomRho8Adapter.v').read_bytes()
if adapter.count(b'From Stdlib Require Import Arith Lia.') != 1:
    raise ValueError('unexpected adapter import')
files['K215F/DomRho8.v'] = adapter.replace(b'From Stdlib Require Import Arith Lia.',
                                        b'From Coq Require Import Arith Lia.')
for path, raw in files.items():
    target = a.build / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(raw)
paths = ['-Q', 'K230S', 'K230S', '-Q', 'K230L', 'K230L', '-Q', 'K215F', 'K215F']
receipt = {
    'scope': 'generic core and numerical adapter, archived arithmetic dependencies, Coq 8 import compatibility',
    'production_endpoint_rebuilt': False,
    'production_rocq91_checked': False,
    'original_adapter_sha256': sha(adapter),
    'compatibility_edit': 'From Stdlib Require Import Arith Lia. -> From Coq Require Import Arith Lia.',
    'sources': {path: sha(raw) for path, raw in files.items()},
    'runs': [],
}
commands = [[str(a.coq_bin / 'coqc')] + paths + [path] for path in files]
commands += [[str(a.coq_bin / 'coqchk'), '-silent'] + paths + ['K215F.DomRho8']]
for cmd in commands:
    r = subprocess.run(cmd, cwd=a.build, capture_output=True, text=True)
    receipt['runs'].append({'command': cmd, 'exit_code': r.returncode,
                            'stdout': r.stdout, 'stderr': r.stderr})
    (here / 'adapter_check.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if r.returncode:
        raise RuntimeError(r.stderr or r.stdout)
print(json.dumps({'status': 'PASS_FOCUSED_ADAPTER_WITH_COMPATIBILITY_IMPORT',
                  'compilations': 4, 'coqchk_exit': 0,
                  'receipt': str(here / 'adapter_check.json')}, indent=2))
