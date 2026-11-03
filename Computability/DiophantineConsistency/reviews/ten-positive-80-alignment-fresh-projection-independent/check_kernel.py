#!/usr/bin/env python3
"""Recheck the external 80-payload / symbolic-original kernel mismatch."""
import gzip
import hashlib
import json
import subprocess
import sys
from pathlib import Path

if sys.flags.optimize or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('isolated, non-optimized Python required')
D = Path(__file__).resolve().parents[2]
repo = D.parents[1]
candidate = D / 'research/ten-positive-unshift-t-finite/coefficients/K.bin.gz'
retained = D / 'candidates/ten-positive-shifted-strong/coefficients/K.bin.gz'
spec = D / 'research/ten-positive-unshift-t-finite/data/equation_qcube_V2.json'
independent = D / 'reviews/compact44-symbolic-k-byte-independent-review/audit.py'
graph = D / 'research/ten-positive-80-model-binding-prototype/Direct80Graph.lean'
alignment = D / 'research/ten-positive-80-aligned-shift-prototype/Direct80AlignedShift.lean'
h = lambda b: hashlib.sha256(b).hexdigest()
before = {str(p): h(p.read_bytes()) for p in [candidate, retained, spec, independent, graph, alignment]}
result = subprocess.run([sys.executable, '-I', '-S', '-B', str(independent)], cwd=repo,
                        capture_output=True, text=True, timeout=120, check=True)
prior = json.loads(result.stdout)
if result.stderr or prior['status'] != 'PASS_EXTERNAL_K_RECIPE_INDEPENDENT_REVIEW':
    raise RuntimeError('independent original-kernel reconstruction failed')
raw_candidate = gzip.decompress(candidate.read_bytes())
raw_original = gzip.decompress(retained.read_bytes())
metadata = json.loads(spec.read_text())['coefficient_binding']['ports']['K0']
if h(candidate.read_bytes()) != metadata['gzip_sha256'] or h(raw_candidate) != metadata['raw_sha256']:
    raise RuntimeError('candidate coefficient metadata mismatch')
if h(raw_original) != prior['raw_sha256']:
    raise RuntimeError('original recipe mismatch')
if len(raw_candidate) != 74111 or len(raw_original) != 74111 or raw_candidate == raw_original:
    raise RuntimeError('expected distinct equal-length payloads')
if int.from_bytes(raw_candidate, 'little').bit_length() != 592884 or int.from_bytes(raw_original, 'little').bit_length() != 592884:
    raise RuntimeError('unexpected bit length')
graph_text, align_text = graph.read_text(), alignment.read_text()
if 'let K0 : Expr (Fin 10) := .constant (p 1)' not in graph_text or '(hp1 : p 1=paramKernel rho)' not in align_text:
    raise RuntimeError('graph port or alignment premise changed')
differences = [(i, x ^ y) for i, (x, y) in enumerate(zip(raw_candidate, raw_original)) if x != y]
if before != {str(p): h(p.read_bytes()) for p in [candidate, retained, spec, independent, graph, alignment]}:
    raise RuntimeError('inputs changed during comparison')
print(json.dumps({'status':'PASS_DISTINCT_PAYLOADS', 'candidate_raw_sha256':h(raw_candidate),
                  'original_raw_sha256':h(raw_original), 'byte_length':len(raw_candidate),
                  'differing_bytes':len(differences), 'differing_bits':sum(x.bit_count() for _,x in differences),
                  'first_differing_byte_offset':differences[0][0], 'input_sha256':before,
                  'original_recipe_review':prior, 'scope':'external payload comparison only; no Lean file binding or iPRA theorem'},
                 indent=2, sort_keys=True))
