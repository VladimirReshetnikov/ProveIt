"""Concrete validation of the register-box excursion lemmas on zfc_254.tm (own code).
Box = sepsR(vs) = concat(0 1^(v+1)) placed at cells 0.. ; cell -1 is the header 1."""
import sys, random; sys.path.insert(0, '.')
from tmlib import load, Run
T, _ = load(sys.argv[1])
SKIP = {7: '69', 6: '64', 5: '28', 4: '40', 3: '38', 2: '56', 1: '31', 0: '44', -1: '60'}
def box(vs, mark=None):
    t = {}; p = 0
    for i, v in enumerate(vs):
        p += 1
        for j in range(v + 1):
            if not (mark == i and j == 0): t[p] = 1
            p += 1
    return t
def run_box(q, vs, mark=None):
    tape = box(vs, mark); tape[-1] = 1
    R = Run(T, q, tape, 0)
    while R.head >= 0:
        assert R.step(), 'halt inside box'
        assert R.t < 10**6
    tape = dict(R.tape); assert tape.pop(-1, 0) == 1
    assert all(k >= 0 for k in tape)
    return R.state, R.head, tape, R.t
random.seed(1)
cnt = 0
for trial in range(400):
    m = random.randint(9, 13)
    vs = [random.choice([0, 0, 1, 2, 3, 7]) for _ in range(m)]
    for j, q in SKIP.items():
        r = j + 1
        st, h, tape, t = run_box(q, vs)
        assert h == -1 and st == ('2' if r == 0 else '6'), (j, st)
        assert tape == box(vs, r), j
        st, h, tape, t = run_box('73', vs, r)
        w = list(vs); w[r] += 1
        assert (st, tape) == ('48', box(w)), ('inc', r, st)
        st, h, tape, t = run_box('43', vs, r)
        if vs[r] == 0:
            assert (st, tape) == ('3', box(vs)), ('dec0', r, st)
        else:
            w = list(vs); w[r] -= 1; w.append(0)
            assert (st, tape) == ('63' if r == 0 else '48', box(w)), ('dec+', r, st)
        cnt += 1
print('box lemmas validated on', cnt, 'cases')
