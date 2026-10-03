#!/usr/bin/env python3
"""Independent standard-library check. Reads literal JSON; imports no prior code."""
from collections import deque
from itertools import product
from math import comb
from pathlib import Path
import json
import hashlib

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'data'
PINS = {
    'semigroup.json': '506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9',
    'accepting-witness.json': '13a3857d28b0207d9baa83facac5b2e67bbaeb858d00b82ef9a91c4ab38df890'
}
def pinned_json(name):
    raw = (SOURCE / name).read_bytes()
    if hashlib.sha256(raw).hexdigest() != PINS[name]:
        raise RuntimeError('Pinned source hash mismatch: ' + name)
    return json.loads(raw)
DATA = pinned_json('semigroup.json')
TILES = {t['id']: t for t in DATA['tiles']}
NONSEP = [t for t in DATA['tiles'] if t['kind'] != 'separator']
SEP = next(t['id'] for t in DATA['tiles'] if t['kind'] == 'separator')
COPY = {t['letter']: t['id'] for t in NONSEP if t['kind'] == 'copy'}
MATS = {g['name']: g['matrix'] for g in DATA['generators']}

def require(ok, why):
    if not ok:
        raise RuntimeError(why)

def copy_block(w):
    return tuple(COPY[c] for c in w) + (SEP,)

def batches(w):
    """Enumerate ALL tile segmentations of bottom word w, then separator."""
    out = []
    def visit(pos, top, seq):
        if pos == len(w):
            out.append((top, seq + (SEP,)))
            return
        for t in NONSEP:
            if w.startswith(t['g'], pos):
                visit(pos + len(t['g']), top + t['h'], seq + (t['id'],))
    visit(0, '', ())
    return out

def graph(w):
    pending, G = deque([w]), {}
    while pending:
        v = pending.popleft()
        if v in G:
            continue
        require(len(G) < 10000, 'fixture graph unexpectedly large')
        G[v] = batches(v)
        require(len({s for u, s in G[v]}) == len(G[v]), 'duplicate batch')
        copy_loops = []
        for u, s in G[v]:
            nrules = sum(TILES[i]['kind'] == 'rewrite' for i in s)
            require(nrules <= 1, 'multiple rules in one batch')
            if nrules == 0:
                require(u == v and s == copy_block(v), 'noncanonical copy loop')
                copy_loops.append(s)
            else:
                require(u != v, 'actual rewrite self-loop')
                pending.append(u)
        require(len(copy_loops) == 1, 'copy loop not unique')
    return G

def paths(G, v):
    if v == 'X':
        return [([v], [])]
    out = []
    for u, s in G[v]:
        if u == v:
            continue
        for vs, blocks in paths(G, u):
            out.append(([v] + vs, [s] + blocks))
    return out

def graph_coefficients(G, w, limit):
    """Coefficient recurrence on all literal bottom-segmentations, loops included."""
    a = {v: [0] * (limit + 1) for v in G}
    for n in range(limit + 1):
        for v, edges in G.items():
            a[v][n] = int(v == 'X' and n == 0) + sum(
                a[u][n - len(s)] for u, s in edges if n >= len(s))
    return a[w]

def product_coefficients(weights, mult, shift, limit):
    a = [1] + [0] * limit
    for weight in weights:
        for n in range(weight, limit + 1):
            a[n] += a[n - weight]
    return [0 if n < shift else mult * a[n - shift] for n in range(limit + 1)]

def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]

def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]

def inverse2(A):
    a, b = A[0]; c, d = A[1]
    require(a*d-b*c == 1, 'nonunimodular input')
    return [[d, -b], [-c, a]]

def phi(w):
    out = eye(2)
    for c in w:
        j = DATA['top_codes'][c]
        out = mm(out, [[1+4*j, 2], [-8*j*j, 1-4*j]])
    return out

def check_literal_witness(w, seq):
    h = ''.join(TILES[i]['h'] for i in seq)
    g = ''.join(TILES[i]['g'] for i in seq)
    require(w + '#' + h == g + 'X#', 'word equation failed')
    names = [f'A{i}' for i in seq] + ['C'] + [f'B{i}' for i in reversed(seq)]
    out = eye(4)
    for name in names:
        out = mm(out, MATS[name])
    T = inverse2(phi(w + '#'))
    wanted = [[0] * 4 for _ in range(4)]
    for i, j in product(range(2), repeat=2):
        wanted[i][j] = T[i][j]
        wanted[i+2][j+2] = [[1, 2], [0, 1]][i][j]
    require(out == wanted, 'full 4x4 product failed')
    # Construct canonical prefix state parts and evaluate every residual type.
    # Selectors are literal one-hot vectors, not an imported certificate helper.
    H, G, sos, residual_count = eye(2), eye(2), 0, 0
    for chosen in seq:
        selectors = [int(i == chosen) for i in range(1, 115)]
        sos += (sum(selectors) - 1) ** 2
        residual_count += 1
        U = [row[:2] for row in MATS[f'A{chosen}'][:2]]
        V = inverse2([row[:2] for row in MATS[f'B{chosen}'][:2]])
        newH, newG = mm(H, U), mm(G, V)
        for old, new, kind in ((H, newH, 'A'), (G, newG, 'B')):
            for a, b in product(range(2), repeat=2):
                z = new[a][b]
                plus, minus = max(z, 0), max(-z, 0)
                predicted = 0
                for index, e in enumerate(selectors, 1):
                    M = [row[:2] for row in MATS[f'{kind}{index}'][:2]]
                    if kind == 'B':
                        M = inverse2(M)
                    predicted += e * sum(old[a][k] * M[k][b] for k in range(2))
                sos += (plus-minus-predicted)**2 + (plus*minus)**2
                residual_count += 2
        H, G = newH, newG
    D = [row[:2] for row in MATS['C'][:2]]
    HD, TG = mm(H, D), mm(T, G)
    for a, b in product(range(2), repeat=2):
        sos += (HD[a][b] - TG[a][b])**2
        residual_count += 1
    require(sos == 0 and residual_count == 17 * len(seq) + 4,
            'canonical paired SOS residual check failed')
    return {'inner_length': len(seq), 'generator_length': len(names),
            'natural_auxiliaries': 130 * len(seq),
            'squared_residuals': residual_count, 'sos': sos}

def run_case(w):
    G = graph(w)
    all_paths = paths(G, w)
    require(all_paths, 'fixture does not accept')
    first_states, first_blocks = all_paths[0]
    H = next(i for i, v in enumerate(first_states) if 'J1' in v)
    halt = first_states[H]
    left, right = halt[1:-1].split('J1')
    m = len(left) + len(right)
    live_lengths = [len(v) for v in first_states[:H+1]]
    rstar = sum(n-1 for n in live_lengths[:-1]) + (m+4) + sum(a+3 for a in range(1,m+1)) + 2
    weights = [n+1 for n in live_lengths] + list(range(4,m+5)) + [2]
    C = comb(m, len(left))
    require(len(all_paths) == C, 'cleanup binomial count failed')
    require(len(weights) == H+m+3, 'denominator factor count failed')
    for states, blocks in all_paths:
        require(sum(map(len, blocks)) == rstar, 'core lengths differ')
        require(sorted(len(v)+1 for v in states) == sorted(weights), 'loop weights differ')
    limit = rstar + 36
    actual = graph_coefficients(G, w, limit)
    predicted = product_coefficients(weights, C, rstar, limit)
    require(actual == predicted, 'exact GF coefficient comparison failed')
    expected_support = {rstar, rstar+2} | set(range(rstar+4,limit+1))
    require({n for n,a in enumerate(actual) if a} == expected_support, 'exact support failed')
    # Independently enumerate bounded stutter tuples and verify no tile-word collisions,
    # both within one history and across different genuine cleanup histories.
    seen = set()
    for states, blocks in all_paths:
        for ks in product(range(2), repeat=len(states)):
            seq = ()
            for j, v in enumerate(states):
                seq += copy_block(v) * ks[j]
                if j < len(blocks):
                    seq += blocks[j]
            require(seq not in seen, 'distinct path/stutter data collided')
            seen.add(seq)
            require(len(seq) == rstar + sum(k*(len(v)+1) for k,v in zip(ks,states)), 'length formula failed')
    samples = []
    for k, l in ((0,0), (1,0), (0,1), (1,2)):
        core = sum(first_blocks, ())
        samples.append(check_literal_witness(w, copy_block(w)*k + core + copy_block('X')*l))
    return {'word': w, 'graph_states': len(G), 'genuine_histories': C,
            'H': H, 'left_length': len(left), 'right_length': len(right),
            'rstar': rstar, 'loop_weights': weights, 'degree': H+m+2,
            'coefficients_checked_through': limit,
            'coefficients_at_offsets_0_to_12': actual[rstar:rstar+13],
            'distinct_stutter_witnesses_checked': len(seen),
            'literal_matrix_and_canonical_SOS_samples': samples}

if __name__ == '__main__':
    saved = pinned_json('accepting-witness.json')
    results = [run_case(saved['derivation'][0]), run_case('[01J110]'), run_case('[J1]')]
    require(results[0]['rstar'] == saved['tile_count'] == 94, 'saved witness length changed')
    # The malformed zero-step target X is separate: its only batches are copies.
    GX = graph('X')
    actualX = graph_coefficients(GX, 'X', 24)
    require(actualX == [int(n%2 == 0) for n in range(25)], 'zero-step X boundary case failed')
    summary = {'cases': results, 'zero_step_X_GF': '1/(1-z^2)',
               'zero_step_X_coefficients_checked_through': 24,
               'imports_prior_python': False,
               'total_bounded_stutter_witnesses': sum(r['distinct_stutter_witnesses_checked'] for r in results),
               'total_literal_matrix_and_SOS_samples': sum(len(r['literal_matrix_and_canonical_SOS_samples']) for r in results)}
    Path(__file__).with_name('CHECKS.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))
