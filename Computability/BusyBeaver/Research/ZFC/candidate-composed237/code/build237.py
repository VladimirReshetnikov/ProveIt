"""Build the 237-state table from the combined 238-state table by Source 106's fold.

Inherited labels (start 95, dispatcher 96, halt 254). Delete state 235 and merge it
into 98: 98/0 -> 0 L 240, 139/1 -> 1 R 98, 156/1 -> 1 R 98 (the only rows entering
235), and the helper change 240/1 -> 1 L 87. Every other row of the 238 table is kept.
Usage (from this directory):

    python code/build237.py ../candidate-combined238/zfc_combined238_old.tm OUT_old.tm

The output equals zfc_composed237_old.tm byte for byte, '#! start 95' header included.
"""
import hashlib
import sys

sys.path.insert(0, __file__.rsplit("code", 1)[0] + "code")
from tm import load  # noqa: E402

COMBINED238 = "ab1f12ceb0b1cbc167977286652dd3be3407e9b24fcd3f8e7c9ac630166514b9"
COMPOSED237_OLD = "a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a"

src, out = sys.argv[1], sys.argv[2]
assert hashlib.sha256(open(src, "rb").read()).hexdigest() == COMBINED238
C = load(src)
assert C[(98, 0)] == (0, "R", 113) and C[(240, 1)] == (1, "R", 99)
assert sorted(k for k, v in C.items() if v[2] == 235) == [(139, 1), (156, 1)]
D = {k: v for k, v in C.items() if k[0] != 235}
D[(98, 0)] = (0, "L", 240)
D[(139, 1)] = (1, "R", 98)
D[(156, 1)] = (1, "R", 98)
D[(240, 1)] = (1, "L", 87)
data = "#! start 95\n" + "".join(f"{q} {b} {w} {d} {r}\n" for (q, b), (w, d, r) in sorted(D.items()))
with open(out, "w", newline="\n") as f:
    f.write(data)
h = hashlib.sha256(data.encode()).hexdigest()
assert h == COMPOSED237_OLD, h
print("states", len({q for q, _ in D}), "rows", len(D), "sha256", h)
