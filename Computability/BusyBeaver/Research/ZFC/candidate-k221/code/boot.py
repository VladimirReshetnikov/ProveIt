"""Exact blank-tape startup check for an inherited-label table (start 95, dispatch 96,
halt 254), any state count. Target frame (Sources 80/101/103): head -5 at dispatch 96,
ones exactly at the marker -6, header 176, then the unary blocks of physical registers
[0,0,0,3,0,0,3,0,0] and 167 value-one spares; zero elsewhere. Sparse run, then an
independent dense replay of the same number of steps. Usage: boot.py TABLE..."""
import sys
from tm import load

def wanted():
    w = {-6, 176}; pos = 177
    for v in [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167:
        pos += 1; w.update(range(pos, pos + v + 1)); pos += v + 1
    return w

def check(path, limit=3_000_000):
    T = load(path)
    qs = {q for q, _ in T}
    assert set(T) == {(q, b) for q in qs for b in (0, 1)}
    assert {r for _, _, r in T.values()} - qs == {254}
    W = wanted(); q, h, ones, visits = 95, 0, set(), {}
    for steps in range(limit + 1):
        if (q, h) == (96, -5) and ones == W:
            break
        if q == 254 or steps == limit:
            raise AssertionError(("no exact frame", q, h, steps, len(ones)))
        b = int(h in ones); visits[(q, b)] = visits.get((q, b), 0) + 1
        w, d, q = T[(q, b)]
        (ones.add if w else ones.discard)(h)
        h += 1 if d == "R" else -1
    q2, h2, lo, tape = 95, 0, 0, bytearray(1)
    for _ in range(steps):
        if h2 < lo: tape = bytearray(lo - h2) + tape; lo = h2
        if h2 >= lo + len(tape): tape.extend(bytearray(h2 - lo - len(tape) + 1))
        w, d, q2 = T[(q2, tape[h2 - lo])]; tape[h2 - lo] = w; h2 += 1 if d == "R" else -1
    assert (q2, h2, {lo + i for i, v in enumerate(tape) if v}) == (96, -5, W)
    return len(qs), steps, visits

for p in sys.argv[1:]:
    n, steps, visits = check(p)
    print(p, "states", n, "EXACT_SPARSE_DENSE_BOOT_PASS steps", steps,
          "visits 80/0,169/0,169/1,91/1:", [visits.get(k, 0) for k in [(80, 0), (169, 0), (169, 1), (91, 1)]])
