"""Check the integer208-height32 quartic against its parent, package 191's principal 208.

Run from the repository root:  py -I Computability/DiophantineConsistency/candidates/integer208-height32/verify.py

1. The parent's row 'growth_pell.divisibility' equals F - 2^20 (1+2z)(1+2h) (up to sign) as a
   polynomial (tested at random rational points), so 2^20 | F at every integer zero of the parent.
2. Rebuild: substitute F = 64 f in every parent residual, divide each residual by the gcd of its
   coefficients, then apply the logged elementary operations r_i := r_i + c r_j (i != j). The result
   must equal equation.json residual for residual.
3. Expand the sum of squares and report variables, residuals, degree, terms and coefficient height.
Pass --write to store the results in CHECKS.json; without it nothing is written.
"""
import hashlib, json, math, os, random, sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
eq = json.load(open(os.path.join(HERE, "equation.json"), encoding="utf-8"))
cert = json.load(open(os.path.join(HERE, "certificate.json"), encoding="utf-8"))
ppath = os.path.join(ROOT, *cert["parent"]["path"].split("/"))
pbytes = open(ppath, "rb").read()
assert hashlib.sha256(pbytes).hexdigest() == cert["parent"]["sha256"], "parent file changed"
parent = json.loads(pbytes)
names = [v["name"] for v in parent["variables"]]
F, z, h = names.index("growth.F"), names.index("horizon.affine_parameter"), names.index("growth_pell.odd_half")
labels = [r.get("label", "") for r in parent["residuals"]]
s = cert["rescaling"]["factor"]

# 1. forcing row
div = parent["residuals"][labels.index("growth_pell.divisibility")]["terms"]
rnd = random.Random(2026)
for _ in range(25):
    pt = [Fraction(rnd.randint(-10**9, 10**9), rnd.randint(1, 10**6)) for _ in names]
    val = sum(Fraction(c) * math.prod((pt[i] for i in m), start=Fraction(1)) for c, m in div)
    want = pt[F] - 2**20 * (1 + 2 * pt[z]) * (1 + 2 * pt[h])
    assert val in (want, -want), "forcing row is not F - 2^20 (1+2z)(1+2h)"
assert (2**20) % s == 0

# 2. rebuild
rows = []
for r in parent["residuals"]:
    d = {}
    for c, m in r["terms"]:
        m = tuple(sorted(m))
        d[m] = d.get(m, 0) + c * s ** m.count(F)
    d = {m: c for m, c in d.items() if c}
    g = 0
    for c in d.values():
        g = math.gcd(g, c)
    rows.append({m: c // g for m, c in d.items()})
for i, j, c in cert["row_operations"]["list"]:
    assert i != j and c != 0
    nd = dict(rows[i])
    for m, v in rows[j].items():
        nd[m] = nd.get(m, 0) + c * v
    rows[i] = {m: v for m, v in nd.items() if v}
stored = [{tuple(m): c for c, m in r["terms"]} for r in eq["residuals"]]
assert rows == stored, "equation.json is not the rebuilt system"

# 3. expansion
P = {}
for r in rows:
    it = list(r.items())
    for ma, ca in it:
        for mb, cb in it:
            k = tuple(sorted(ma + mb))
            P[k] = P.get(k, 0) + ca * cb
P = {k: v for k, v in P.items() if v}
res = {
    "variables": len({i for k in P for i in k}),
    "declared_variables": len(eq["variables"]),
    "residuals": len(rows),
    "max_residual_degree": max(len(m) for r in rows for m in r),
    "degree": max(len(k) for k in P),
    "terms": len(P),
    "height": max(abs(v) for v in P.values()),
    "row_operations": len(cert["row_operations"]["list"]),
    "parent_sha256": cert["parent"]["sha256"],
}
for k, v in res.items():
    print(f"{k}: {v}")
assert res["variables"] == res["declared_variables"] == 208 and res["residuals"] == 148 and res["degree"] == 4
if "--write" in sys.argv:
    open(os.path.join(HERE, "CHECKS.json"), "w", encoding="utf-8", newline="\n").write(json.dumps(res, indent=1) + "\n")
print("all checks passed")
