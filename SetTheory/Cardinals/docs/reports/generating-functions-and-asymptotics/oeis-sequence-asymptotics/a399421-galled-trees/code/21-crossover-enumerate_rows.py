"""Exact integer enumeration from the published Pólya equation.
Run from any directory. The output path is fixed relative to this file.
"""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
N = 160
G = [[0] for _ in range(N + 1)]
S = [[0] for _ in range(N + 1)]

def addto(a, b, shift=0):
    if len(a) < len(b) + shift:
        a.extend([0] * (len(b) + shift - len(a)))
    for j, value in enumerate(b):
        a[j + shift] += value

def conv(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out

def square_co(n, seq):
    out = [0]
    for i in range(1, n):
        addto(out, conv(seq[i], seq[n - i]))
    return out

for n in range(1, N + 1):
    twice = square_co(n, G)
    if n % 2 == 0:
        for k, value in enumerate(G[n // 2]):
            addto(twice, [value], 2 * k)
    gall_sides = square_co(n - 1, S)
    if n % 2:
        for k, value in enumerate(S[(n - 1) // 2]):
            addto(gall_sides, [value], 2 * k)
    addto(twice, gall_sides, 1)
    assert all(value % 2 == 0 for value in twice), (n, "nonintegral row")
    G[n] = [value // 2 for value in twice]
    if n == 1:
        G[n][0] += 1
    while len(G[n]) > 1 and G[n][-1] == 0:
        G[n].pop()
    assert len(G[n]) == (n - 1) // 2 + 1
    assert all(value > 0 for value in G[n])
    S[n] = G[n].copy()
    for i in range(1, n):
        addto(S[n], conv(G[i], S[n - i]))

# Independent scalar calculation of the gall-free column.
scalar = [0] * (N + 1)
for n in range(1, N + 1):
    twice = sum(scalar[i] * scalar[n - i] for i in range(1, n))
    if n % 2 == 0:
        twice += scalar[n // 2]
    assert twice % 2 == 0
    scalar[n] = twice // 2 + int(n == 1)
assert scalar == [row[0] for row in G]
reference = json.loads((ROOT / 'data/reference-rows.json').read_text())
assert G == reference['rows'], 'Exact reference-row mismatch'
fixture = json.loads((ROOT / 'data/oeis-numeric-fixture.json').read_text())
assert G[1:14] == fixture['A399421_rows_n1_to_n13']
assert [sum(row) for row in G[:28]] == fixture['A397952_terms_n0_to_n27']
(ROOT / 'results').mkdir(exist_ok=True)
(ROOT / 'results/exact-rows.json').write_text(json.dumps({'N': N, 'rows': G, 'totals': [sum(row) for row in G]}, separators=(',', ':')) + '\n')
summary = {'N': N, 'reference_rows_match': True, 'gall_free_scalar_match': True,
           'A399421_cells_checked': 49, 'A399421_rows_checked': 13,
           'A397952_terms_checked': 28, 'all_divisions_even': True}
(ROOT / 'results/exact-checks.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
