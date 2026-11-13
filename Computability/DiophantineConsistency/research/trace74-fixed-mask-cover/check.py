#!/usr/bin/env python3
"""Check a fixed-payload inequality needed by the trace74 guard probe."""
import gzip
import hashlib
import json
from pathlib import Path
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('invoke python3 -I -S -B without optimization')

here = Path(__file__).resolve().parent
root = here.parents[1]
graph_path = root / 'research/trace74-mask-coordinate-probe/candidate.json'
coeff_dir = root / 'candidates/ten-positive-qcube-product-square/coefficients'
sha = lambda data: hashlib.sha256(data).hexdigest()

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

graph = graph_path.read_bytes()
need(sha(graph) == 'dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353', 'candidate hash')
ports = json.loads(graph)['coefficient_binding']['ports']
values = {}
for name in ('beta', 'MC', 'MF'):
    entry = ports[name]
    compressed = (coeff_dir / entry['file']).read_bytes()
    need(sha(compressed) == entry['parent_gzip_sha256'], name + ' compressed hash')
    raw = gzip.decompress(compressed)
    need(sha(raw) == entry['raw_sha256'], name + ' raw hash')
    values[name] = int.from_bytes(raw, 'little')

beta, mc, mf = (values[k] for k in ('beta', 'MC', 'MF'))
hp = mf - beta
need(beta == (1 << 590069) - 1, 'beta is not the expected repunit')
need(0 < mc < beta < mf < 2 * beta, 'basic mask bounds')
need(hp.bit_length() == 589954, 'HP bit length')
need((beta - mc).bit_length() == 220833, 'complement bit length')
need(hp >= 1 << 589953, 'HP lower bound')
need(beta - mc < 1 << 220833, 'complement upper bound')
need(mc + hp > beta, 'mask cover inequality')
print(json.dumps({'beta_bits': beta.bit_length(), 'hp_bits': hp.bit_length(),
                  'beta_minus_mc_bits': (beta - mc).bit_length(),
                  'mc_plus_hp_gt_beta': True}, sort_keys=True))
