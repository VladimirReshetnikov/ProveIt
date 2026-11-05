#!/usr/bin/env python3
"""Compare the source-pinned, physical-order K recipe with retained payloads.

The Lean theorem concerns the recipe, not filesystem or gzip semantics.
"""
import gzip
import hashlib
import json
import re
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
D = HERE.parents[1]

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def pinned(relative, expected):
    data = (D / relative).read_bytes()
    need(sha(data) == expected, 'source drift: ' + relative)
    return data

source = (HERE / 'KernelRecipe.lean').read_bytes()
need(sha(source) == '13a3b32b1c87156229608a5e8cac2a33a2f85b8b87bec329f35b51cc71ab649a',
     'Lean recipe source drift')
source_text = source.decode()
recipe_text = source_text.split('def recipe (r : ℕ) : ℕ :=', 1)[1].split('theorem rawWord_recipe', 1)[0]
need('r ^ 18 + r ^ 1004 + r ^ 2020' in recipe_text and
     '(∑ p : Fin 942, 2 * weightAt p * r ^ (1005 - p.val))' in recipe_text,
     'Lean selector or base-power recipe drift')
control_terms = re.findall(r'∑ j : Fin (\d+), 2 \* 2 \^ \((\d+) \+ j.val\) \* r \^ \(1005 - \((\d+) \+ j.val\)\)', recipe_text)
need(control_terms == [('8','10','978'),('9','18','960'),('8','27','969'),('9','35','942')],
     'Lean control recipe drift')
physical = pinned('Lean/DiophantineConsistency/MFWangTiles942PhysicalData.lean',
    '208c3debcda84b159bc850feedc78628d36dd31bb8fd580598fa4d0988967f34').decode()
order = pinned('Lean/DiophantineConsistency/MFWangTiles942PhysicalOrder.lean',
    '39787941a0926b3553cee91ee900d8f6a7508509c2de41b6ba9332b338dcb8f8').decode()
table = pinned('Lean/DiophantineConsistency/WangTiles942TableData.lean',
    '0d2bf996f4e7e19acba82d5d3f1805a71c17cb1a9bcdc959e67453da14697a2c').decode()
pinned('Lean/DiophantineConsistency/CurrentKernelData2011.lean',
    '529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c')
pinned('Lean/DiophantineConsistency/MFCurrentKernel2011.lean',
    '3cd9029a0eeaa4dd81c72355f9eb6afbe785b6a12a1fb2369fa688288622c560')
need('def weightAt (p : Fin 942) : ℕ := Fin.cases (selectorWeight start) value p' in order,
     'weightAt definition drift')
need('def value (j : Fin 941) : ℕ := (row j).2' in order and
     "def row (j : Fin 941) : ℕ × ℕ := rows[j.val]'(by rw [rows_length]; exact j.isLt)" in order,
     'physical row lookup drift')
parts = re.findall(r'def chunk(\d+) : List \(ℕ × ℕ\) := \[(.*?)\]', physical, re.S)
need([n for n, _ in parts] == [f'{i:02d}' for i in range(59)], 'chunk names/order')
rows_expr = physical.split('def rows : List (ℕ × ℕ) :=', 1)[1].split('theorem rows_length', 1)[0]
need(re.findall(r'chunk\d+', rows_expr) == [f'chunk{i:02d}' for i in range(59)], 'rows order')
rows = []
for _, chunk_text in parts:
    pairs = re.findall(r'\((\d+),\s*(\d+)\)', chunk_text)
    need(re.sub(r'\(\d+,\s*\d+\)|[\s,]', '', chunk_text) == '', 'unparsed row data')
    rows.extend((int(i), int(w)) for i, w in pairs)
need(len(rows) == 941 and set(i for i, _ in rows) == set(range(1, 942)), 'index coverage')
need(all(a[1] > b[1] for a, b in zip(rows, rows[1:])), 'weights not descending')
start = re.search(r'def start : Tile := ⟨(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩', table)
need(start is not None, 'Start tuple missing')
need('1 + 2 ^ 10 * (1 + t.west + 2 ^ 8 * t.north + 2 ^ 17 * t.east + 2 ^ 25 * t.south)' in table,
     'selector weight formula drift')
w,n,e,s = map(int, start.groups())
start_weight = 1 + 2**10 * (1 + w + 2**8*n + 2**17*e + 2**25*s)
weights = [start_weight] + [weight for _, weight in rows]
need(len(weights) == 942 and start_weight == 34876427265, 'Start weight mismatch')
# Recompute the exact source formula using shifts: rho = 2^47.
value = sum(1 << (47*k) for k in (18,1004,2020))
value += sum(2 * weight * (1 << (47*(1005-pos))) for pos,weight in enumerate(weights))
for count, power, pos in (tuple(map(int, x)) for x in control_terms):
    value += sum((2 << (power+j)) * (1 << (47*(1005-pos-j))) for j in range(count))
recipe_bytes = value.to_bytes((value.bit_length()+7)//8, 'big')
results = []
for graph, graph_sha in (
    ('research/current2011-ordinary67-94-candidate/polynomial.json',
     'd76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb'),
    ('research/fourteen-normalized-product106/polynomial.json',
     '0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1')):
    data = json.loads(pinned(graph, graph_sha)); binding = data['coefficient_binding']; meta = binding['ports']['K0']
    payload = (D / graph).parent / binding['path'] / meta['file']
    compressed = payload.read_bytes(); raw = gzip.decompress(compressed)
    need(sha(compressed)==meta['gzip_sha256'] and sha(raw)==meta['raw_sha256'] and
         len(raw)==meta['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==meta['bits'], 'metadata mismatch')
    need(raw == recipe_bytes, 'recipe bytes mismatch: ' + graph)
    results.append({'graph':graph,'raw_sha256':sha(raw),'gzip_sha256':sha(compressed),
                    'bytes':len(raw),'bits':value.bit_length()})
print(json.dumps({'status':'PASS','physical_selectors':len(weights),'control_terms':34,
                  'start_weight':start_weight,'source_recipe_sha256':sha(source),
                  'payloads':results,'scope':'External source-row recipe evaluation and gzip comparison; Lean does not parse files.'},
                 indent=2,sort_keys=True))
