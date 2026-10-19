"""Re-derive the exceptional block paths of the three savings from the literal tables.

For each exceptional old row (q, read) with its required left bits, run the OLD
table for k steps and the NEW table from phi(q) for n steps on EVERY 5-cell window
(offsets -3..1) consistent with the guard. Both runs must read only cells of the
window, and must end with identical tapes, head position and mapped state. The new
control path must be the same for every window. Prints the path tables shown in
the README. Inherited labels; tables are given relative to this directory.
"""
import itertools
import sys

sys.path.insert(0, __file__.rsplit("code", 1)[0] + "code")
from tm import load  # noqa: E402

ING = "ingredients/"


def run(T, q, t, n):
    t = dict(t); h = 0; path = [q]
    for _ in range(n):
        assert h in t, "read outside window"
        w, d, z = T[(q, t[h])]
        t[h] = w; h += 1 if d == "R" else -1; q = z; path.append(q)
    return q, h, t, path


def check(old, new, phi, specs, title):
    print(f"\n{title}")
    for q, b, guard, k, n in specs:
        paths = set()
        for vals in itertools.product((0, 1), repeat=5):
            t = dict(zip(range(-3, 2), vals))
            if t[0] != b or any(t[x] != v for x, v in guard.items()):
                continue
            oq, oh, ot, _ = run(old, q, t, k)
            nq, nh, nt, p = run(new, phi(q, t), t, n)
            assert (phi(oq, ot, oh), oh, ot) == (nq, nh, nt), (title, q, b, vals)
            paths.add(tuple(p))
        assert len(paths) == 1, paths
        print(f"  {q}/{b}  left {guard}  old {k} step(s) -> new {n}: {' -> '.join(map(str, paths.pop()))}")


# Saving 1 (Source 103): boundary240 -> boundary239, split 218 by the bit behind the head.
B240, B239 = load(ING + "boundary240_old.tm"), load(ING + "boundary239_old.tm")
def phi1(q, t, h=0):
    if q == 218:
        return 223 if t[h - 1] == 0 else 179
    return q
check(B240, B239, phi1, [(179, 1, {-1: 0}, 1, 5), (218, 0, {-1: 0}, 3, 1),
                         (218, 0, {-1: 1}, 3, 1), (218, 1, {-1: 1}, 1, 3)],
      "Saving 1: split of 218 (boundary240 -> boundary239)")

# Saving 2 (Sources 101/102): boundary239 -> combined238, fold 169 into 80.
C238 = load("../candidate-combined238/zfc_combined238_old.tm")
phi2 = lambda q, t, h=0: 80 if q == 169 else q
check(B239, C238, phi2, [(80, 0, {-1: 1}, 1, 5), (169, 0, {-1: 0}, 1, 3),
                         (169, 1, {-1: 0, 1: 1}, 1, 5), (91, 1, {-3: 0, -2: 1, -1: 1}, 1, 9)],
      "Saving 2: delayed erasure, 169 into 80 (boundary239 -> combined238)")

# Saving 3 (Source 106): combined238 -> composed237, fold 235 into 98.
C237 = load("zfc_composed237_old.tm")
phi3 = lambda q, t, h=0: 98 if q == 235 else q
check(C238, C237, phi3, [(98, 0, {-1: 0}, 1, 3), (235, 0, {-2: 1, -1: 1}, 1, 5),
                         (240, 1, {-1: 0}, 1, 3)],
      "Saving 3: 235 into 98 (combined238 -> composed237)")
print("\nALL BLOCK PATHS CHECKED")
