#!/usr/bin/env python3
"""Exact lookup-work census. These counts are not wall-clock speed claims."""
from pathlib import Path
import hashlib, json, re
ROOT = Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

program = (ROOT/'deps/K215F/Prog215.v').read_text()
block = program.split('Definition p215_tab', 1)[1].split(':= [', 1)[1].split('].', 1)[0]
nodes = re.findall(r'\((C[NIDBC] \d+|CH), (C[NIDBC] \d+|CH)\)', block)
root = int(re.search(r'root := (\d+)', program).group(1))
if len(nodes) != 179 or root != 178: raise ValueError('Unexpected literal program')

def leaf(code):
    bits = []
    while code > 1:
        bits.append(code & 1); code //= 2
    n = root
    for depth in range(180):
        tag = nodes[n][bits[depth] if depth < len(bits) else 0].split()
        if tag[0] != 'CN': return tag[0]
        n = int(tag[1])
    raise ValueError('Tree traversal exhausted')

def depth(n, j):
    if not 0 <= j < n: raise ValueError('Out of range index')
    if n == 1: return 1
    k = n // 2
    return 1 + (depth(k, j) if j < k else depth(n-k, j-k))

def census(file, count):
    p = ROOT/file
    rows = [tuple(map(int, r)) for r in re.findall(
        r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)', p.read_text())]
    if len(rows) != count: raise ValueError((file, len(rows)))
    refs, kinds = [0], {}
    for a,b,j,k in rows:
        kind = leaf(a); kinds[kind] = kinds.get(kind,0)+1
        if kind == 'CD': refs.extend([j,k])
        elif kind != 'CH': raise ValueError(kind)
    if kinds != {'CD':count-1, 'CH':1}: raise ValueError(kinds)
    return {'data_file':file, 'data_sha256':sha(p), 'entries':count,
        'lookups':len(refs), 'list_visits':sum(j+1 for j in refs),
        'tree_visits':sum(depth(count,j) for j in refs),
        'max_tree_visits':max(depth(count,j) for j in refs),
        'certificate_bytes':p.stat().st_size}

result = {'scope':'Only linked-list constructor / balanced-tree node visits for endpoint lookup',
          'program_sha256':sha(ROOT/'deps/K215F/Prog215.v'),
          'ordinary':census('baseline/Cert215Compact.v',2240),
          'normalized':census('NormalizedCert215.v',1426)}
print(json.dumps(result,indent=2))
