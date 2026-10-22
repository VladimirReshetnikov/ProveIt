"""Refined T4 coefficient compiler, using only Python's standard library.

The literal K215 transition JSON is the sole mathematical data input.
The script verifies finite claims, not the universal Pell/tableau theorem.
Run: python3 compiler5263.py [--output DIRECTORY]
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TRANSITIONS = ROOT / 'k215_transitions.json'
L, Q, R, V, H = 434, 435, 436, 437, 438
A0 = 439
PHASE_EDGES = {(L, L), (L, Q), (Q, R), (R, R)}
START = (L, Q, R, 1)
FORBIDDEN = (H, 0, 0, H)

def data(x):
    if x < 434:
        q1, bit = divmod(x, 2)
        return bit, None if q1 == 0 else q1 - 1, None
    if x in (L, Q, R):
        return 0, 0 if x == Q else None, x
    return None, None, None

DATA = tuple(data(x) for x in range(A0))
HEADLESS = tuple(x for x in range(A0) if DATA[x][1] is None)
HEADED = tuple(x for x in range(A0) if DATA[x][1] is not None)

def load_transition():
    raw = TRANSITIONS.read_bytes()
    assert hashlib.sha256(raw.rstrip(b'\n') + b'\n').hexdigest() == '880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755'
    rows = json.loads(raw)['transitions']
    assert len(rows) == 430
    delta = {(q, b): (write, move, nq) for q, b, write, move, nq in rows}
    assert len(delta) == 430 and delta[0, 0] == (1, 1, 93)
    delta.update({(215, b): (b, 0, 215) for b in (0, 1)})
    return delta

def original_valid(w, delta):
    """Literal four-cell T4 predicate from package 11, rewritten here."""
    left, center, right, nxt = w
    if sum(DATA[x][1] is not None for x in (left, center, right)) > 1:
        return False
    if ((center == V) != (nxt == V) or
        center == V and right == V or center == H and nxt == H):
        return False
    if center != V and right != V and (center == H) != (right == H):
        return False
    if center == V:
        return True
    if center == H:
        return DATA[nxt][2] is not None
    bit, state, phase = DATA[center]
    if phase is not None:
        if left == V and phase != L or right == V and phase != R:
            return False
        if right != V and (phase, DATA[right][2]) not in PHASE_EDGES:
            return False
    if state is not None:
        move = delta[state, bit][1]
        if move == -1 and left == V or move == 1 and right == V:
            return False
    if nxt == H:
        return state is None or state == 215
    if DATA[nxt][2] is not None or left == H or right == H:
        return False
    expected_bit = bit if state is None else delta[state, bit][0]
    arrivals = []
    for x, move in ((left, 1), (center, 0), (right, -1)):
        bx, qx, _ = DATA[x]
        if qx is not None and delta[qx, bx][1] == move:
            arrivals.append(delta[qx, bx][2])
    return len(arrivals) <= 1 and DATA[nxt][:2] == (expected_bit, arrivals[0] if arrivals else None)

def compatible_pair(left, right):
    """Horizontal phase/boundary adjacency of canonical computation strips."""
    if left == V:
        return right != V and (DATA[right][2] is None or right == L)
    if right == V:
        return DATA[left][2] is None or left == R
    if (left == H) != (right == H):
        return False
    if (DATA[left][2] is not None) != (DATA[right][2] is not None):
        return False
    if DATA[left][2] is not None:
        return (left, right) in PHASE_EDGES
    return True

def horizontal_ok(triple):
    left, center, right = triple
    if sum(DATA[x][1] is not None for x in triple) > 1:
        return False
    if not compatible_pair(left, center) or not compatible_pair(center, right):
        return False
    # Every ordinary cell within distance two of a vertical boundary is blank
    # and headless.  A genuine finite halt can always be padded this way.
    if V in triple and any(x < 434 and x != 0 or x == Q for x in triple):
        return False
    return True

def valid(w, delta):
    if w == FORBIDDEN:
        return True
    if not horizontal_ok(w[:3]):
        return False
    if w[3] == H and any(DATA[x][1] not in (None, 215) for x in w[:3]):
        return False
    return original_valid(w, delta)

def enumerate_windows(delta):
    triples = set(itertools.product(HEADLESS, repeat=3))
    for pos in range(3):
        for q in HEADED:
            for a, b in itertools.product(HEADLESS, repeat=2):
                t = [a, b]
                t.insert(pos, q)
                triples.add(tuple(t))
    candidates = sorted(t for t in triples if horizontal_ok(t))
    windows = [t + (n,) for t in candidates for n in range(A0) if valid(t + (n,), delta)]
    assert START in windows and FORBIDDEN not in windows
    windows.remove(START)
    windows = [START, FORBIDDEN] + windows
    assert len(windows) == 5263 and len(set(windows)) == 5263
    assert all(original_valid(w, delta) for w in windows)
    return windows, len(candidates)

def geometry(windows):
    k, a, ell = len(windows), A0, (len(windows) + 1).bit_length()
    base = 2 * ell + 11 * a + 8
    p = max(0, (k + 4 * a + 4 - base + 1) // 2)
    m = base + 2 * p
    nd = m + 1 - k - 4 * a - 4
    es = k + 4 * a
    M = es + nd + 1
    emax = 27 * M
    hc = 51 * M + 3 * a + 1
    t1 = hc + 2 * emax + a + 1
    t2 = t1 + 2 * emax + 4
    assert M % 2 == 1 and nd == 1
    lc = 1
    while lc < t2 + 2 * emax + 2:
        lc *= 5
    bmin = max(ell * (4 * a + 5 + p) + 3,
        ell * (4 * a + 4) + (4 * (m + 3) * (18 * (k + 4 * a + 4) + 6) + 8).bit_length() + 1, 4)
    b = 1
    while b < bmin:
        b *= 5
    # j=0,1,2,3 means left,center,right,next respectively.
    def e(j, symbol):
        return k + (3 - j) * a + symbol
    support = (set(range(k)) | {e(j, u) for j in range(4) for u in range(a)} |
               set(range(es, es + nd)) | {M, 3 * M, 9 * M, 27 * M})
    assert len(support) == m + 1
    assert max(support - {M, 3 * M, 9 * M, 27 * M}) < M
    expand = support | {es + 1}
    assert not ({(t1 - e) % lc for e in expand} & {(t2 - e) % lc for e in expand})
    assert {(9 * M - e) % lc for e in support} & {(27 * M - e) % lc for e in support} == {0}
    bare = (2 * a, hc + a, 8 * M, 24 * M)
    targets = []
    for u in range(a):
        targets.append((e(1, u), {e(3, u)}, set(), {e(1, u)}))
        for j, src in ((0, 1), (1, 2)):
            targets.append((hc + e(j, u), {e(src, u)}, {e(j, u)}, set()))
    targets += [(9 * M, {M}, set(), {9 * M}), (27 * M, {3 * M}, set(), {27 * M})]
    assert len({x for x, *_ in targets}) == 3 * a + 2
    for x, d0, d1, d2 in targets:
        assert {x - v for v in bare if x - v in support} == d0
        assert ({x - hc} if x - hc in support else set()) == d1
        assert ({x} if x in support else set()) == d2
        assert x < t1 - emax
    for t, other in ((t1, t2), (t2, t1)):
        assert not {t - v for v in bare} & support
        assert all(other + e - t not in support for e in support)
    A = 1 << ell
    jmax = 4 * a + 4 + p
    mu = A - 2 + (pow(A, jmax + 1) - A) // (A - 1)
    census = Counter((j, u) for w in windows for j, u in enumerate(w))
    sum_v = (k + sum((census[j, u] + 1) * pow(A, 1 + j * a + u) for j in range(4) for u in range(a))
             + sum((k + 1) * pow(A, 4 * a + t) for t in range(1, 5)))
    mass = (len(support) + 2) * (2 * sum_v + 6)
    assert 4 * mass + 8 < (1 << b) and 2 * mu + 4 < (1 << b)
    assert 2 * mu.bit_count() + 3 * a + 2 + 1 == len(support)
    assert (t2 - t1) % 4 == 2 and t2 - t1 > 2 * emax
    # Every paired clause contribution is zero mod5, independently of v_e.
    assert (pow(2, t1, 5) + pow(2, t2, 5)) % 5 == 0
    dc_mod5 = sum(pow(2, x, 5) for x in bare) % 5
    unit = (2 * dc_mod5 - pow(2, hc, 5)) % 5
    assert unit == 2
    gamma_mod5 = pow(2, es, 5) * (pow(2, 2, 5) - 1) * (1 + 2 * (dc_mod5 + 2 * pow(2, hc, 5) + 2)) % 5
    assert gamma_mod5 == 3
    return dict(k=k, a=a, ell=ell, A=A, p=p, m=m, dummy_count=nd, dummy_start=es,
        M=M, Emax=emax, Hc=hc, T1=t1, T2=t2, bmin=bmin, b=b, L=lc, d=b * lc,
        copy_offsets={name:e(j, 0) for j,name in enumerate(('left','center','right','next'))},
        native_support=len(support), target_positions=len(targets), mod5_unit=unit,
        mu_jmax=jmax, mu_bit_length=mu.bit_length(), mu_population=mu.bit_count(),
        clause_mass_bit_length=sum_v.bit_length(), carry_threshold_bit_length=(4 * mass + 8).bit_length(),
        beta_bit_length=b * lc, K_bit_length=b * lc + b * hc + 1,
        all_rotation_geometry=True, exact_convolution_targets=True, carry_bound=True,
        MC_mod4=2, MF_native_mod8=4, population_sum=b * lc)

def seam_checks(delta):
    checked = 0
    controls = 0
    for control in (0, 1):
        tr = dict(delta)
        tr[93, 0] = (0, 0, 215) if control == 0 else (1, -1, 2)
        tr[2, 1] = (0, -1, 3)
        tr[3, 0] = (1, 1, 215)
        tape, head, state, history = {}, 0, 0, []
        for _ in range(10):
            history.append((dict(tape), head, state))
            if state == 215:
                break
            write, move, state = tr[state, tape.get(head, 0)]
            tape[head] = write
            head += move
        assert history[-1][2] == 215
        lm = max(2, 2 - min(h for _, h, _ in history))
        rm = max(2, 2 + max(h for _, h, _ in history))
        for dw, dh in itertools.product(range(3), repeat=2):
            width, height = lm + rm + 2 + dw, len(history) + 1 + dh
            xs = lm + 1
            grid = []
            for y in range(height):
                row = [V]
                for x in range(1, width):
                    if y == 0:
                        cell = H
                    elif y == 1:
                        cell = L if x < xs else Q if x == xs else R
                    else:
                        tape, head, state = history[min(y - 1, len(history) - 1)]
                        pos = x - xs
                        cell = tape.get(pos, 0) + (2 * (state + 1) if pos == head else 0)
                    row.append(cell)
                grid.append(row)
            word = [None] * (width * height)
            for y, row in enumerate(grid):
                for x, cell in enumerate(row):
                    word[(-(x - xs) - width * (y - 1)) % len(word)] = cell
            windows = [(word[(i+1)%len(word)], word[i], word[(i-1)%len(word)], word[(i-width)%len(word)]) for i in range(len(word))]
            assert all(valid(w, tr) for w in windows)
            assert windows[0] == START and windows.count(START) == 1 and FORBIDDEN not in windows
            controls += 1
            checked += len(windows)
    return dict(control_tableaux=controls, checked_windows=checked)

def coefficient_recipe(geom, windows_hash):
    """Exact finite recipe; coefficient numerals themselves are not expanded."""
    recipe = {'schema': 'proveit-k215-refined-t4-fixed-coefficients-v1',
     'status': 'Ordinary mathematical adapter plus exact finite checks; no new end-to-end kernel proof',
     'source_commit': 'f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
     'parent_recipe': '11-t4/bridge/T4_CONSTANTS.json',
     'machine_table_sha256': 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
     'transition_json': 'k215_transitions.json',
     'tile_list': 'windows5263.json',
     'tile_list_sha256': None,
     'start': [434, 435, 436, 1],
     'forbidden': [438, 0, 0, 438],
     'order': 'Start first, forbidden second, other passing tuples lexicographically',
     'predicate': 'compiler5263.py:valid',
     'scalars': None,
     'definitions': {'rho': '2^78125',
                     'B': 'rho^1953125 = 2^(5^16)',
                     'E': 'selectors0..5262 union copy intervals '
                          '(6580+u,6141+u,5702+u,5263+u),u=0..438, union '
                          '{7019,7021,21063,63189,189567}',
                     'mu': '8192-2 + sum(8192^j,j=1..2840)',
                     'v_selector': '1+A^(1+l)+A^(440+c)+A^(879+r)+A^(1318+n)+sum(A^(1756+t),t=1..4)',
                     'v_copy': 'A^(1+j*439+u) at e_j(u),j=(left,center,right,next)=0..3',
                     'v_anchor': 'A^(1756+t) at 3^(t-1)*7021,t=1..4',
                     'v_dummy': '0 at 7019',
                     'DC': 'rho^878+rho^359828+rho^56168+rho^168504+sum(v_e*(rho^(738963-e)+rho^(1118101-e)),e '
                           'in E)',
                     'DR': 'rho^359389',
                     'MF0': 'mu*(rho^738963+rho^1118101)+sum(rho^(6141+u),u=0..438)+sum(rho^(359389+6580+u)+rho^(359389+6141+u),u=0..438)+rho^63189+rho^189567',
                     'MC': 'B-1-sum(rho^e,e in E except e=1)-2*rho^7019',
                     'MF_native': 'MF0+4',
                     'beta': 'B-1',
                     'K': 'DC+B*DR',
                     'MF_source': 'MF_native+B-1'},
     'ports': ['beta', 'K', 'MC', 'MF_source'],
     'invariants': {'five_adic_unit': 2,
                    'Gamma_mod5': 3,
                    'MC_mod4': 2,
                    'MF_native_mod8': 4,
                    'positive_ports': True,
                    'population_sum': '5^16',
                    'whole_tuple_only': True},
     'scope': 'Exact finite recipes for giant integers, not expanded numerals; universal compiler/Pell '
              'theorems inherited.'}
    recipe['scalars'] = geom
    recipe['tile_list_sha256'] = windows_hash
    return recipe

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT / 'output5263')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    delta = load_transition()
    windows, triples = enumerate_windows(delta)
    # Forbidden cannot extend: its left neighbor must be centered at H and
    # therefore cannot be the unique exception, nor have ordinary right cell 0.
    assert all(not valid((left, H, 0, nxt), delta) for left in range(A0) for nxt in range(A0))
    geom = geometry(windows)
    data_bytes = (json.dumps(windows, separators=(',', ':')) + '\n').encode()
    (args.output / 'windows5263.json').write_bytes(data_bytes)
    receipt = dict(status='PASS', source_commit='f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
        windows_count=len(windows), horizontal_triples=triples, successors_exhausted=triples*A0,
        windows_sha256=hashlib.sha256(data_bytes).hexdigest(),
        center_class_counts=dict(Counter(str(w[1]) if w[1]>=434 else ('headless' if w[1]<2 else 'head') for w in windows)),
        geometry=geom, seams=seam_checks(delta),
        scope='Finite alphabet, geometry, and control-tableau checks; not a new kernel formalization or a K215-halting computation.')
    recipe = coefficient_recipe(geom, receipt['windows_sha256'])
    (args.output / 'T5263_CONSTANTS.json').write_text(json.dumps(recipe, indent=2)+'\n')
    (args.output / 'verification5263.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
