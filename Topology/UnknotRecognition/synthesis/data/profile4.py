import sys, time, random
sys.path.insert(0, 'C:/Knots/fast')
from fastunknot import Diagram
from fastunknot.scan import ScanComplex, best_scan_order, order_profile
rng = random.Random(4)
def one_component(strands, word):
    p = list(range(strands))
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    seen, cnt = set(), 0
    for s in range(strands):
        if s in seen: continue
        cnt += 1; x = s
        while x not in seen: seen.add(x); x = p[x]
    return cnt == 1
for length in (9, 13, 17):
    while True:
        word = [rng.choice([-1, 1]) * rng.randint(1, 3) for _ in range(length)]
        if one_component(4, word): break
    pd = [tuple(c) for c in Diagram.from_braid(4, word).pd]
    for name, order in (('greedy', best_scan_order(pd, 12)), ('braid', list(range(len(pd))))):
        print('length', length, name, 'profile', order_profile(pd, order), flush=True)
        c = ScanComplex()
        t0 = time.perf_counter()
        for k, i in enumerate(order):
            t = time.perf_counter()
            c.add_crossing(pd[i])
            entries = sum(len(v) for v in c.out.values())
            print(f"  step {k:2d} boundary {len(c.points):2d} objects {len(c.objects):5d} entries {entries:6d} step {time.perf_counter()-t:6.2f}s total {time.perf_counter()-t0:6.1f}s", flush=True)
        print('  rank', len(c.objects), flush=True)
