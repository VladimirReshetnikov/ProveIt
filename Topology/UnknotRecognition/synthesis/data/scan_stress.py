import sys, time, random, json
sys.path.insert(0, 'C:/Knots/fast')
sys.path.insert(0, 'C:/Users/vresh/AppData/Local/Temp/claude/C--Knots/098bb8b7-a324-4a1d-a8ef-b20101618640/scratchpad/xval')
from fastunknot.scan import khovanov_rank
from kh04 import Diagram, recognize

def one_component(strands, word):
    p = list(range(strands))
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    seen, cnt = set(), 0
    for s in range(strands):
        if s in seen: continue
        cnt += 1
        x = s
        while x not in seen:
            seen.add(x); x = p[x]
    return cnt == 1

rng = random.Random(2026)
mismatches = 0
tested = 0
t0 = time.perf_counter()
while tested < 120:
    strands = rng.choice([3, 4, 5])
    length = rng.randint(6, 13)
    word = [rng.choice([-1, 1]) * rng.randint(1, strands - 1) for _ in range(length)]
    if not one_component(strands, word):
        continue
    d = Diagram.from_braid(strands, word)
    pd = [list(c) for c in d.pd]
    ref = recognize(d).reduced_rank
    order = list(range(len(pd))); rng.shuffle(order)
    r1 = khovanov_rank(pd, check_d_squared=(tested % 4 == 0))
    r2 = khovanov_rank(pd, order=order)
    tested += 1
    if r1['reduced_rank'] != ref or r2['reduced_rank'] != ref:
        mismatches += 1
        print('MISMATCH', strands, word, ref, r1['reduced_rank'], r2['reduced_rank'])
print('random braids tested', tested, 'mismatches', mismatches, 'seconds', round(time.perf_counter() - t0, 1))

# Atlas PDs
for f in ['C:/Knots/reports/06/examples/kt11n42.json', 'C:/Knots/reports/06/examples/conway11n34.json', 'C:/Knots/reports/04/examples/atlas_10_124.json']:
    pd = json.load(open(f))['pd']
    t = time.perf_counter(); r = khovanov_rank(pd); t = time.perf_counter() - t
    t2 = time.perf_counter(); ref = recognize(Diagram.from_pd(pd)).reduced_rank; t2 = time.perf_counter() - t2
    print(f.split('/')[-1], 'scan', r['reduced_rank'], round(t, 3), 's  cube', ref, round(t2, 3), 's', r['stats'])

# Larger inputs: the exponential family of archive 03 (unknot sigma_1...sigma_n), random 4-strand braids
for n in (10, 20, 40, 80):
    pd = [list(c) for c in Diagram.from_braid(n + 1, list(range(1, n + 1))).pd]
    t = time.perf_counter(); r = khovanov_rank(pd); t = time.perf_counter() - t
    print('unknot family n =', n, 'reduced rank', r['reduced_rank'], round(t, 3), 's', r['stats'])
for length in (16, 20, 24, 28, 32):
    while True:
        word = [rng.choice([-1, 1]) * rng.randint(1, 3) for _ in range(length)]
        if one_component(4, word): break
    pd = [list(c) for c in Diagram.from_braid(4, word).pd]
    t = time.perf_counter(); r = khovanov_rank(pd, seconds=600); t = time.perf_counter() - t
    print('random 4-braid length', length, 'reduced rank', r['reduced_rank'], round(t, 3), 's', r['stats'])
