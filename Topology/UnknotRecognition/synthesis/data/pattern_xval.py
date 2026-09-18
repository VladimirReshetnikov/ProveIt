"""Cross-validate the six ball-boundary-pattern testers on random cubic spherical rotation systems."""
import json, random, sys, time
sys.path.insert(0, '.')
from grid01.pattern import BallPattern as P01, assess_pattern
from kh02.pattern import BallPattern as P02
from kh03.patterns import BallPattern as P03, decide_ball_pattern
from kh04.pattern import classify_ball_pattern
from kh05.pattern import SphericalPattern as P05
from kh06.patterns import BallPattern as P06, classify_pattern

def random_rotation(rng, V):
    """Random perfect matching of darts 3v+j; returned in the 2e/2e+1 dart format if spherical."""
    darts = list(range(3 * V)); rng.shuffle(darts)
    pairs = [(darts[i], darts[i + 1]) for i in range(0, 3 * V, 2)]
    new = {}
    for e, (a, b) in enumerate(pairs):
        new[a], new[b] = 2 * e, 2 * e + 1
    rotations = tuple(tuple(new[3 * v + j] for j in range(3)) for v in range(V))
    try:
        P01(rotations, 0)  # validates sphericity of every component
    except ValueError:
        return None
    return rotations

def run_all(rotations):
    V = len(rotations)
    out = {}
    out['01'] = assess_pattern(P01(rotations, 0))['essential']
    # 02: positional darts 3i+j, edge pairs of positions
    pos = {}
    for v, row in enumerate(rotations):
        for j, d in enumerate(row):
            pos[d] = 3 * v + j
    E = 3 * V // 2
    out['02'] = P02(V, [(pos[2 * e], pos[2 * e + 1]) for e in range(E)]).test_essential().essential
    out['03'] = decide_ball_pattern(P03(rotations, 0))['essential']
    signed = [[(d // 2 + 1) * (1 if d % 2 == 0 else -1) for d in row] for row in rotations]
    out['04'] = classify_ball_pattern(signed, 0).essential_on_ball
    out['05'] = P05([[d // 2 for d in row] for row in rotations], 0).classify().essential
    out['06'] = classify_pattern(P06.from_json({'ambient': '3-ball', 'rotation': [list(r) for r in rotations], 'circles': 0}))['status'] == 'essential'
    return out

rng = random.Random(7)
summary = []
for V in (2, 4, 6, 8, 10):
    t = time.perf_counter()
    seen, tested, essential, disagreements = set(), 0, 0, 0
    attempts = 0
    while tested < 400 and attempts < 200000:
        attempts += 1
        rot = random_rotation(rng, V)
        if rot is None or rot in seen:
            continue
        seen.add(rot)
        res = run_all(rot)
        tested += 1
        if len(set(res.values())) != 1:
            disagreements += 1
            print('DISAGREEMENT', rot, res)
        essential += res['01']
    row = {'vertices': V, 'spherical_systems_tested': tested, 'attempts': attempts,
           'essential': essential, 'disagreements': disagreements, 'seconds': round(time.perf_counter() - t, 2)}
    summary.append(row); print(row)
# named examples in the shared dart format
named = {
 'theta': ((0, 2, 4), (1, 5, 3)),
 'tetrahedron': json.load(open('C:/Knots/reports/01/examples/pattern_tetrahedral.json'))['rotations'],
 'cube': json.load(open('C:/Knots/reports/01/examples/pattern_cube.json'))['rotations'],
 'prism': json.load(open('C:/Knots/reports/01/examples/pattern_triangular_prism.json'))['rotations'],
 'dodecahedron': json.load(open('C:/Knots/reports/01/examples/pattern_dodecahedron.json'))['rotations'],
 'dumbbell': json.load(open('C:/Knots/reports/01/examples/pattern_dumbbell.json'))['rotations'],
}
named_results = {}
for name, rot in named.items():
    rot = tuple(tuple(r) for r in rot)
    res = run_all(rot)
    named_results[name] = res
    print(name, res)
json.dump({'random': summary, 'named': named_results}, open('pattern_xval.json', 'w'), indent=1)
