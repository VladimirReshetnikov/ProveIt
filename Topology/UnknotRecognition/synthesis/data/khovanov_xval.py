"""Cross-validate the five reduced-Khovanov recognizers (archives 02-06) on shared inputs."""
import json, random, sys, time
sys.path.insert(0, '.')
from kh02 import braid_closure as bc02, reduced_khovanov as rk02, Diagram as D02
from kh03.diagrams import PlanarDiagram as PD03
from kh03.khovanov import recognize as rec03, Limits as L03
from kh04 import Diagram as D04, recognize as rec04
from kh05 import braid_closure as bc05, recognize as rec05, PlanarDiagram as PD05
from kh06 import from_braid as fb06, recognize as rec06, Diagram as D06

def rank02(kind, data):
    d = bc02(*data) if kind == 'braid' else D02.from_pd(data)
    return rk02(d).total_rank
def rank03(kind, data):
    d = PD03.from_braid(*data) if kind == 'braid' else PD03.from_pd(data)
    return rec03(d, limits=L03(None, None, None), determinant_filter=False)['reduced_rank_f2']
def rank04(kind, data):
    d = D04.from_braid(*data) if kind == 'braid' else D04.from_pd(data)
    return rec04(d).reduced_rank
def rank05(kind, data):
    d = bc05(*data) if kind == 'braid' else PD05(tuple(map(tuple, data)))
    r = rec05(d, reduce=False, determinant=False)
    return r['khovanov']['total_rank'] if 'khovanov' in r else (1 if r['status'] == 'UNKNOT' else None)
def rank06(kind, data):
    d = fb06(*data) if kind == 'braid' else D06.from_pd(data)
    return rec06(d)['reduced_homology_dimension']

impls = {'02': rank02, '03': rank03, '04': rank04, '05': rank05, '06': rank06}

def one_component(strands, word):
    p = list(range(strands))
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    seen, c, cnt = set(), 0, 0
    for s in range(strands):
        if s in seen: continue
        cnt += 1
        x = s
        while x not in seen:
            seen.add(x); x = p[x]
    return cnt == 1

cases = [
    ('unknot circle', 'braid', (1, [])),
    ('trefoil', 'braid', (2, [1, 1, 1])),
    ('figure-eight', 'braid', (3, [1, -2, 1, -2])),
    ('T(2,5)', 'braid', (2, [1] * 5)),
    ('T(2,7)', 'braid', (2, [1] * 7)),
    ('T(3,4)', 'braid', (3, [1, 2] * 4)),
    ('T(3,5) det 1', 'braid', (3, [1, 2] * 5)),
    ('unknot s1 s2', 'braid', (3, [1, 2])),
    ('unknot s1s2s3s4', 'braid', (5, [1, 2, 3, 4])),
    ('conjugated unknot', 'braid', (3, [-2, -2, 1, 2, 2, 2])),
    ('hard unknot 05', 'braid', (3, [-2, -2, -2, 2, 1, 1, 2, 1])),
    ('KT 11n42 (Atlas PD)', 'pd', json.load(open('C:/Knots/reports/06/examples/kt11n42.json'))['pd']),
    ('Conway 11n34 (Atlas PD)', 'pd', json.load(open('C:/Knots/reports/06/examples/conway11n34.json'))['pd']),
    ('10_124 (Atlas PD)', 'pd', json.load(open('C:/Knots/reports/04/examples/atlas_10_124.json'))['pd']),
]
rng = random.Random(20260917)
n_random = 0
while n_random < 30:
    strands = rng.choice([3, 4])
    length = rng.randint(6, 10)
    word = [rng.choice([-1, 1]) * rng.randint(1, strands - 1) for _ in range(length)]
    if one_component(strands, word):
        cases.append((f'random braid {strands} strands {word}', 'braid', (strands, word)))
        n_random += 1

rows, disagreements = [], 0
for name, kind, data in cases:
    ranks, times = {}, {}
    for key, fn in impls.items():
        t = time.perf_counter()
        ranks[key] = fn(kind, data)
        times[key] = time.perf_counter() - t
    agree = len(set(ranks.values())) == 1
    disagreements += not agree
    rows.append({'case': name, 'ranks': ranks, 'seconds': {k: round(v, 4) for k, v in times.items()}, 'agree': agree})
    print(f"{'OK ' if agree else 'XX '} {name[:60]:60s} ranks={list(ranks.values())}")
json.dump({'cases': rows, 'disagreements': disagreements}, open('khovanov_xval.json', 'w'), indent=1)
print('cases', len(rows), 'disagreements', disagreements)
