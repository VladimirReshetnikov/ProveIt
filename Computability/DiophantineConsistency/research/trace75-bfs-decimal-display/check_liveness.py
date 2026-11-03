#!/usr/bin/env python3
"""Check the displayed JSON graph's live operation and input counts."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import sys

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
h = Path(__file__).resolve().parent
graph = h.parents[1] / 'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
raw = graph.read_bytes()
expected = '8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9'
if sha256(raw).hexdigest() != expected:
    raise ValueError('graph SHA mismatch')
g = json.loads(raw)
nodes = {r[0]: r for r in g['source']}
if len(nodes) != len(g['source']) or len(nodes) != 75:
    raise ValueError('duplicate/count')
seen = set()
stack = [g['output']]
while stack:
    n = stack.pop()
    if n in seen:
        continue
    seen.add(n)
    if n in nodes:
        stack.extend(x for x in nodes[n][2:] if isinstance(x, str))
inputs = set(g['witnesses'] + g['fixed_numerals'])
if seen != set(nodes) | inputs:
    raise ValueError('dead or unknown node/input')
counts = Counter(row[1] for row in g['source'])
if counts != {'*': 44, '+': 17, '-': 14}:
    raise ValueError('operation counts')
print(json.dumps({'status': 'PASS_LIVENESS', 'graph_sha256': expected,
                  'live_operations': len(nodes), 'live_inputs': len(inputs),
                  'operation_breakdown': dict(counts),
                  'scope': 'external graph check'}, sort_keys=True))
