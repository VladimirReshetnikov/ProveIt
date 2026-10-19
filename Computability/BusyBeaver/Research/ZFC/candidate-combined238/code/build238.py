"""Build the combined 238-state table from the boundary239 table (Source 103) by
applying the delayed-erasure fold of the delayed239 table (Sources 101/102).

Inherited labels throughout (start 95, dispatcher 96, halt 254). The fold deletes
state 169 and edits three retained rows exactly as Sources 101/102 do on the 240-state
table: 80/0 -> 0 L 106, 91/1 -> 1 L 167, 147/0 -> 0 R 80. Every other row of the
boundary239 table is kept. Usage (from the candidate directory):

    python code/build238.py ingredients/boundary239_old.tm OUT_old.tm
"""
import hashlib
import sys

sys.path.insert(0, __file__.rsplit("code", 1)[0] + "code")
from tm import load  # noqa: E402

BOUNDARY239 = "d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719"
COMBINED238 = "ab1f12ceb0b1cbc167977286652dd3be3407e9b24fcd3f8e7c9ac630166514b9"

src, out = sys.argv[1], sys.argv[2]
assert hashlib.sha256(open(src, "rb").read()).hexdigest() == BOUNDARY239
B = load(src)
# The three rows the fold edits are untouched by the boundary construction.
assert B[(80, 0)] == (0, "R", 25) and B[(91, 1)] == (0, "L", 50) and B[(147, 0)] == (0, "R", 169)
C = {k: v for k, v in B.items() if k[0] != 169}
C[(80, 0)] = (0, "L", 106)
C[(91, 1)] = (1, "L", 167)
C[(147, 0)] = (0, "R", 80)
assert not [k for k, v in C.items() if v[2] == 169], "a row still enters the deleted state"
data = "".join(f"{q} {b} {w} {d} {r}\n" for (q, b), (w, d, r) in sorted(C.items()))
with open(out, "w", newline="\n") as f:
    f.write(data)
h = hashlib.sha256(data.encode()).hexdigest()
assert h == COMBINED238, h
print("states", len({q for q, _ in C}), "rows", len(C), "sha256", h)
