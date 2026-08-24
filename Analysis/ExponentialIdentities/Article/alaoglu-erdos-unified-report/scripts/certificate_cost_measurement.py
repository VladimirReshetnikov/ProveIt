"""Empirical check of Proposition co:prop-cost: total certificate work should scale like
N^(1 + log_4 3), i.e. a factor 2*sqrt(3) = 3.4641 per doubling of N."""
import re, math

# ---- 32768 range: rows are (a, e) plus an enclosure table
LEAN = ("C:/ProveIt/Analysis/ExponentialIdentities/Lean/ExponentialIdentities/"
        "TwoBaseIntegerExponent/")
s32 = open(LEAN + "FiniteCheck32768.lean", encoding="utf-8").read()
encl_body = re.search(r"encl32768 : List \(ℕ × ℕ × ℕ × ℕ\) := \[(.*?)\n\]", s32, re.S).group(1)
ENCL = [tuple(int(x) for x in t)
        for t in re.findall(r"\((\d+), (\d+), (\d+), (\d+)\)", encl_body)]
rows32 = []
for c in range(4):
    body = re.search(rf"certTable32768_{c} : List \(ℕ × ℕ\) := \[(.*?)\n\]", s32, re.S).group(1)
    rows32 += [(int(a), int(e)) for a, e in re.findall(r"\((\d+), (\d+)\)", body)]
assert len(rows32) == 16384, len(rows32)

cost32 = 0
for i, (a, e) in enumerate(rows32):
    m = 16384 + i
    if m == 16384:
        continue
    Lp, Lq, Up, Uq = ENCL[e]
    # bits handled: m^Lp and a^Lq for the lower test, m^Up and (a+1)^Uq for the upper
    cost32 += Lp * math.log2(m) + Up * math.log2(m)

# ---- 16384 range: rows are (a, tier); tiers live in the tieredCheck match
p16 = LEAN + "FiniteCheck16384.lean"
s16 = open(p16, encoding="utf-8").read()
tier_re = re.findall(
    r"\| (\d+) => decide \(a \^ (\d+) < m \^ (\d+)\) && decide \(m \^ (\d+) < \(a \+ 1\) \^ (\d+)\)",
    s16)
TIER = {int(t): (int(Lp), int(Lq), int(Up), int(Uq)) for t, Lq, Lp, Up, Uq in tier_re}
body16 = re.search(r"certTable16384 : List \(ℕ × ℕ\) := \[(.*?)\n\]", s16, re.S).group(1)
rows16 = [(int(a), int(t)) for a, t in re.findall(r"\((\d+), (\d+)\)", body16)]
assert len(rows16) == 8192, len(rows16)

cost16 = 0
for i, (a, t) in enumerate(rows16):
    m = 8192 + i
    if m == 8192:
        continue
    Lp, Lq, Up, Uq = TIER[t]
    cost16 += Lp * math.log2(m) + Up * math.log2(m)

print(f"total certificate bits, [8192,16384):  {cost16/1e9:8.3f} Gbit")
print(f"total certificate bits, [16384,32768): {cost32/1e9:8.3f} Gbit")
print(f"observed ratio per doubling: {cost32/cost16:.3f}")
print(f"predicted 2*sqrt(3)        : {2*math.sqrt(3):.3f}")
print()
print(f"tiers used at 16384: {len(TIER)}; enclosure quadruples at 32768: {len(ENCL)}")
mx16 = max(TIER[t][0] for _a, t in rows16[1:])
mx32 = max(ENCL[e][0] for i, (_a, e) in enumerate(rows32) if i)
print(f"largest lower numerator: 16384 range {mx16:,};  32768 range {mx32:,}"
      f"  (ratio {mx32/mx16:.2f}, predicted ~2^1.29 = {2**1.2925:.2f})")
