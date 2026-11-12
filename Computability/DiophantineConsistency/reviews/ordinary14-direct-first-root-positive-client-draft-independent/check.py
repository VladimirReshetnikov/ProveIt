#!/usr/bin/env python3
"""Independent source and finite update controls; no Lean invocation."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-direct-first-root-positive-client-draft'
R = D / 'reviews/ordinary14-direct-first-root-graph-client-draft-independent'

def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

source = pinned(A / 'PositiveClient.lean', '888f0d0641246eedfdcafdffafa32d0986a46a5db4106196b20e7e48472aeda3').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-direct-first-root-positive-client-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '7c93779f7c39c338b09bb08e0c62737a7296fdeef7a6ab06e2f62233fc8cd849'
graph = pinned(D / 'research/ordinary14-direct-first-root-graph-client-draft/GraphFirstRootClient.lean',
               '864fb3935afd53711562656a3d5cbf7473d9182ded7face06b72416f6d72a78a').decode()
root = pinned(D / 'Lean/DiophantineConsistency/Compact44/P72Root.lean',
              '066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091').decode()
for text in ('theorem putRoot_self', 'theorem positive_zero_iff',
             'theorem positive_zero_iff_natural_ports', '(hbeta : 0<beta)',
             '(hport : (p 0 : DiffRing V)=ι beta)', 'P72Root.cast_port p 0',
             'putRoot_positive v t hv ht', 'putRoot_positive v r hv hr',
             '(positive_first_coordinate_iff p beta v hbeta (hv 0) hport).mp hold',
             '(positive_first_coordinate_iff p beta v hbeta (hv 0) hport).mpr hnew'):
    assert text in source, text
assert 'def putRoot (v : Fin 14 → V) (r : V) : Fin 14 → V := Function.update v 8 r' in graph
assert 'theorem putRoot_positive' in graph and 'theorem positive_first_coordinate_iff' in graph
assert 'theorem cast_port (p : Fin 4 → ℕ) (j : Fin 4)' in root
assert '(((fun j => (p j : ℤ)) j : ℤ) : DiffRing V) = ι (p j : V)' in root

def replay(path, receipt):
    run = subprocess.run([sys.executable, '-I', '-S', '-B', str(path)], cwd=D,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True)
    assert not run.stderr and run.stdout == receipt.read_bytes()

replay(A / 'check_source.py', A / 'observation.json')
replay(R / 'check.py', R / 'result.json')

checks = 0
for seed in range(1, 101):
    original = [1 + ((seed * (j+3)) % 19) for j in range(14)]
    for replacement in range(1, 11):
        updated = original.copy()
        updated[8] = replacement
        assert all(x > 0 for x in updated)
        assert all(updated[j] == original[j] for j in range(14) if j != 8)
        self_update = original.copy()
        self_update[8] = original[8]
        assert self_update == original
        checks += 1
for first_port in range(25):
    p = [first_port, 1, 2, 3]
    z = [int(value) for value in p]
    assert z[0] == int(p[0])

print(json.dumps({'scope': 'source and finite controls only; no Lean or model theorem',
                  'author_readme_prelink_sha256': sha(readme[:-len(tail)]),
                  'update_controls': checks, 'natural_port_controls': 25,
                  'fixed_coordinate_review_replayed': True}, sort_keys=True, indent=2))
