#!/usr/bin/env python3
"""Check the displayed JSON graph's live operation and input counts."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json
h=Path(__file__).resolve().parent;graph=h.parent/'ten-positive-unshift-t-finite/data/equation_qcube_V2.json'
raw=graph.read_bytes();expected='fcc5e40f5d22320541ec2af5857725ceafaa69d0df36708ec60d6b9a40a71f01'
if sha256(raw).hexdigest()!=expected:raise ValueError('graph SHA mismatch')
g=json.loads(raw);nodes={r[0]:r for r in g['source']}
if len(nodes)!=80:raise ValueError('duplicate/count')
seen=set();stack=[g['output']]
while stack:
 n=stack.pop()
 if n in seen:continue
 seen.add(n)
 if n in nodes:stack.extend(x for x in nodes[n][2:] if isinstance(x,str))
inputs=set(g['witnesses']+g['fixed_numerals'])
if not (set(nodes)|inputs)<=seen or seen!=set(nodes)|inputs:raise ValueError('dead or unknown node/input')
counts=Counter(row[1] for row in g['source'])
if counts!={'*':48,'+':18,'-':14}:raise ValueError('operation counts')
print(json.dumps({'status':'PASS_LIVENESS','graph_sha256':expected,'live_operations':len(nodes),'live_inputs':len(inputs),'operation_breakdown':dict(counts),'scope':'external graph check'},sort_keys=True))
