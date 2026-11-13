#!/usr/bin/env python3
"""Run the retained local-search engine on the current Carrier65 graph.

The engine is pinned and loaded as parsed function definitions only.  Its
original top-level graph search is not executed.  The samples are a negative
filter, never a proof that a surviving candidate is an identity.
"""
import ast
import gzip
import hashlib
import json
from pathlib import Path
import random
from itertools import product
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
ENGINE = D / 'research/p64-qcube79-local-rewrite-search/search.py'
GRAPH = D / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
ENGINE_HASH = '4c8e09ecb5ca438123ab0ac1b6cb6e07b5d27f95c6cee651debde2ccbb438f46'
GRAPH_HASH = 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
PRIME, SAMPLES, SEED = 1_000_000_007, 3, 0x46BE

def checked_read(path, expected):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise RuntimeError(f'hash mismatch: {path}')
    return data

engine = ast.parse(checked_read(ENGINE, ENGINE_HASH), filename=str(ENGINE))
names = {'evaluate', 'live_count', 'search', 'alias_and_square_sign'}
defs = [node for node in engine.body if isinstance(node, ast.FunctionDef) and node.name in names]
if {node.name for node in defs} != names:
    raise RuntimeError('expected search functions missing')
exec(compile(ast.Module(body=defs, type_ignores=[]), str(ENGINE), 'exec'))
if PRIME % 4 != 3 or any(PRIME % d == 0 for d in range(2, int(PRIME**0.5) + 1)):
    raise RuntimeError('expected a prime congruent to three modulo four')
graph = json.loads(checked_read(GRAPH, GRAPH_HASH))
rows, output = graph['source'], graph['output']
variables = graph['witnesses'] + graph['fixed_numerals']
if len(rows) != 65 or live_count(rows, output) != 65 or len(graph['witnesses']) != 14:
    raise RuntimeError('unexpected graph dimensions or liveness')
result = search(rows, variables, output)
extra = alias_and_square_sign(rows, variables, output)
ports = {}
for name, metadata in graph['coefficient_binding']['ports'].items():
    compressed = (GRAPH.parent / 'coefficients' / metadata['file']).read_bytes()
    if hashlib.sha256(compressed).hexdigest() != metadata['gzip_sha256']:
        raise RuntimeError(f'compressed {name} hash mismatch')
    raw = gzip.decompress(compressed)
    if hashlib.sha256(raw).hexdigest() != metadata['raw_sha256']:
        raise RuntimeError(f'raw {name} hash mismatch')
    ports[name] = int.from_bytes(raw, 'big') % PRIME
fixed_result = search(rows, variables, output, fixed=ports)
if any(fixed_result['counts'][k] for k in ('targets_with_sample_zero', 'sample_zero_nonconstant')):
    raise RuntimeError('fixed-port zero sample needs separate treatment')
control = rows[:-1] + [['__neg_one__', '-', 0, rows[-1][2]],
                      ['__neg_two__', '-', 0, '__neg_one__'],
                      [rows[-1][0], rows[-1][1], '__neg_two__', rows[-1][3]]]
control_result = alias_and_square_sign(control, variables, output)
if not control_result['aliases']:
    raise RuntimeError('double-negation alias control not detected')
sign_control = [['a', '+', 'x', 1], ['b', '-', 'a', 1],
                ['sq', '*', 'b', 'b'], ['N', '+', 'sq', 0]]
sign_result = alias_and_square_sign(sign_control, ['x'], 'N')
if not any(x['target'] == 'b' and x['live'] == 3 for x in sign_result['square_only_negations']):
    raise RuntimeError('square-sign control not detected')
print(json.dumps({'graph_sha256': GRAPH_HASH, 'engine_sha256': ENGINE_HASH,
                  'wrapper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  'prime': PRIME, 'samples': SAMPLES, 'seed': SEED,
                  'result': result, 'extra': extra, 'fixed_port_result': fixed_result,
                  'fixed_port_residues': ports,
                  'positive_control': control_result, 'square_sign_control': sign_result},
                 indent=2, sort_keys=True))
