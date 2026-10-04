"""Cross-validate archive 01's grid search (Dynnikov moves) against archive 04's Khovanov recognizer.

A grid is converted to a PD code by an independent traversal written here.
"""
import itertools, json, random, sys, time
sys.path.insert(0, '.')
from grid01.grid import Grid
from grid01.recognize import recognize as grid_recognize
from grid01.determinant import determinant as grid_det
from kh04 import Diagram, recognize as kh_recognize

def grid_to_pd(grid):
    rows = grid.rows
    n = grid.size
    cols = grid.columns()
    # traverse; record events (crossing_id, is_over, dx or dy)
    crossing_id = {}
    events = []
    r, c = 0, rows[0][0]
    start = (r, c)
    while True:
        a, b = rows[r]
        d = b if c == a else a
        dx = 1 if d > c else -1
        for col in range(c + dx, d, dx):
            lo, hi = cols[col]
            if lo < r < hi:
                key = (r, col)
                crossing_id.setdefault(key, len(crossing_id))
                events.append((crossing_id[key], False, dx))
        c = d
        lo, hi = cols[c]
        s = hi if r == lo else lo
        dy = 1 if s > r else -1
        for row in range(r + dy, s, dy):
            a2, b2 = rows[row]
            if a2 < c < b2:
                key = (row, c)
                crossing_id.setdefault(key, len(crossing_id))
                events.append((crossing_id[key], True, dy))
        r = s
        if (r, c) == start:
            break
    m = len(events)
    if m == 0:
        return []
    # edge k runs from event k to event (k+1) % m
    info = {}
    for k, (cid, over, direction) in enumerate(events):
        incoming, outgoing = (k - 1) % m, k
        info.setdefault(cid, {})['over' if over else 'under'] = (incoming, outgoing, direction)
    pd = []
    for cid in range(len(crossing_id)):
        u_in, u_out, dx = info[cid]['under']
        o_in, o_out, dy = info[cid]['over']
        south = o_in if dy == 1 else o_out
        north = o_out if dy == 1 else o_in
        if dx == 1:   # under enters from the west; counterclockwise next port is south
            pd.append([u_in, south, u_out, north])
        else:         # under enters from the east; counterclockwise next port is north
            pd.append([u_in, north, u_out, south])
    return pd

def khovanov_verdict(grid):
    pd = grid_to_pd(grid)
    res = kh_recognize(Diagram.from_pd(pd))
    assert res.status in ('UNKNOT', 'KNOTTED'), res.status
    return res.status, res.reduced_rank, len(pd)

def all_orbits(n):
    raw, orbits = set(), set()
    for x in itertools.permutations(range(n)):
        for tail in itertools.permutations(range(1, n)):
            cycle = (0,) + tail
            o = [0] * n
            for i, row in enumerate(cycle):
                o[row] = x[cycle[(i + 1) % n]]
            g = Grid.from_rows(list(zip(x, o)))
            if g.rows not in raw:
                raw.add(g.rows)
                orbits.add(g.canonical())
    return sorted(orbits, key=lambda g: g.rows)

def random_knot_grid(rng, n):
    while True:
        x = list(range(n)); rng.shuffle(x)
        o = list(range(n)); rng.shuffle(o)
        if any(a == b for a, b in zip(x, o)):
            continue
        g = Grid.from_rows(list(zip(x, o)))
        if g.components() == 1:
            return g

summary = {'exhaustive': [], 'random': []}
for n in range(2, 7):
    t = time.perf_counter()
    orbits = all_orbits(n)
    counts = {'agree': 0, 'disagree': 0, 'unknot': 0, 'knotted': 0}
    knotted_ranks = {}
    for g in orbits:
        gv = grid_recognize(g, use_determinant=False, include_certificate=False)['verdict']
        kv, rank, crossings = khovanov_verdict(g)
        counts['agree' if gv == kv else 'disagree'] += 1
        counts['unknot' if kv == 'UNKNOT' else 'knotted'] += 1
        if kv == 'KNOTTED':
            knotted_ranks[rank] = knotted_ranks.get(rank, 0) + 1
        if gv != kv:
            print('DISAGREEMENT', n, g.rows, gv, kv, rank)
    row = {'size': n, 'orbits': len(orbits), **counts, 'khovanov_ranks_of_knots': knotted_ranks,
           'seconds': round(time.perf_counter() - t, 2)}
    summary['exhaustive'].append(row)
    print(row)

rng = random.Random(1)
for n, trials in ((7, 300), (8, 200), (9, 100), (10, 60)):
    t = time.perf_counter()
    counts = {'agree': 0, 'disagree': 0, 'unknot': 0, 'knotted': 0, 'det1_knotted': 0,
              'max_states': 0, 'max_crossings': 0}
    for _ in range(trials):
        g = random_knot_grid(rng, n)
        if g.crossing_count() > 14:
            continue
        res = grid_recognize(g, use_determinant=False, include_certificate=False)
        gv = res['verdict']
        kv, rank, crossings = khovanov_verdict(g)
        counts['agree' if gv == kv else 'disagree'] += 1
        counts['unknot' if kv == 'UNKNOT' else 'knotted'] += 1
        counts['det1_knotted'] += (kv == 'KNOTTED' and grid_det(g) == 1)
        counts['max_states'] = max(counts['max_states'], res['states_seen'])
        counts['max_crossings'] = max(counts['max_crossings'], crossings)
        if gv != kv:
            print('DISAGREEMENT', n, g.rows, gv, kv, rank)
    row = {'size': n, 'trials_drawn': trials, 'tested': counts['agree'] + counts['disagree'], **counts, 'seconds': round(time.perf_counter() - t, 2)}
    summary['random'].append(row)
    print(row)
json.dump(summary, open('grid_xval.json', 'w'), indent=1)
