"""Independent end-to-end re-verification of the COMMITTED FiniteCheck32768.lean.

This does not trust the generator. It parses the four chunk tables and the enclosure list
back out of the Lean source, reconstructs m from the row's position exactly the way the Lean
dispatch does, and re-checks all four inequalities with exact GMP arithmetic.

Note the certificate is self-certifying in `a`: if a^Lq < m^Lp and m^Up < (a+1)^Uq hold with
2^Lp < 3^Lq and 3^Uq < 2^Up, then a < m^theta < a+1 whatever a was intended to be. So the
only things that can go wrong are a false inequality or a coverage gap. Both are checked.
"""
import re
import sys
from gmpy2 import mpz

SRC = ("C:/ProveIt/Analysis/ExponentialIdentities/Lean/ExponentialIdentities/"
       "TwoBaseIntegerExponent/FiniteCheck32768.lean")
LO, HI, CHUNK, POW2 = 16384, 32768, 4096, 16384

s = open(SRC, encoding="utf-8").read()

# --- guard against native_decide / sorry sneaking in (ignore doc comments)
code = re.sub(r"/-.*?-/", " ", s, flags=re.S)
code = re.sub(r"--.*", " ", code)
for bad in ("native_decide", "sorry", "axiom "):
    if bad in code:
        sys.exit(f"FORBIDDEN TOKEN IN CODE: {bad!r}")
print("code carries no native_decide, no sorry, no axiom declarations")

# --- enclosure list
enc_body = re.search(r"encl32768 : List \(\u2115 \u00d7 \u2115 \u00d7 \u2115 \u00d7 \u2115\) := \[(.*?)\n\]",
                     s, re.S).group(1)
ENCL = [tuple(int(x) for x in t)
        for t in re.findall(r"\((\d+), (\d+), (\d+), (\d+)\)", enc_body)]
print(f"enclosure list: {len(ENCL)} quadruples")

# --- the four chunk tables, in order
rows = []
for c in range(4):
    body = re.search(rf"certTable32768_{c} : List \(\u2115 \u00d7 \u2115\) := \[(.*?)\n\]",
                     s, re.S).group(1)
    chunk = [(int(a), int(e)) for a, e in re.findall(r"\((\d+), (\d+)\)", body)]
    if len(chunk) != CHUNK:
        sys.exit(f"CHUNK {c} HAS {len(chunk)} ROWS, EXPECTED {CHUNK}")
    rows += chunk
print(f"parsed {len(rows)} rows from four chunks of {CHUNK}")

if len(rows) != HI - LO:
    sys.exit(f"COVERAGE GAP: {len(rows)} rows for {HI - LO} values")

# --- verify every row
bad = 0
for i, (a, e) in enumerate(rows):
    m = LO + i                      # exactly what the Lean dispatch computes
    if m == POW2:
        if a != 0:
            print(f"  note: exempt row m={m} carries a={a}")
        continue
    if not (0 <= e < len(ENCL)):
        sys.exit(f"ROW m={m}: enclosure index {e} out of range")
    Lp, Lq, Up, Uq = ENCL[e]
    if Lq == 0 or Uq == 0:
        sys.exit(f"ROW m={m}: zero denominator")
    if a == 0:
        sys.exit(f"ROW m={m}: a = 0 on a certified row")
    checks = (
        ("2^Lp < 3^Lq", mpz(2) ** Lp < mpz(3) ** Lq),
        ("3^Uq < 2^Up", mpz(3) ** Uq < mpz(2) ** Up),
        ("a^Lq < m^Lp", mpz(a) ** Lq < mpz(m) ** Lp),
        ("m^Up < (a+1)^Uq", mpz(m) ** Up < mpz(a + 1) ** Uq),
    )
    for name, ok in checks:
        if not ok:
            print(f"  FAIL m={m} a={a} encl={ENCL[e]}: {name}")
            bad += 1
    if i % 4000 == 0:
        print(f"   ... {i}/{len(rows)}", flush=True)

if bad:
    sys.exit(f"{bad} FAILED CHECKS")

print()
print("ALL ROWS RE-VERIFIED FROM THE COMMITTED LEAN SOURCE.")
print(f"coverage: every m in [{LO}, {HI}) present exactly once; "
      f"exempt row is m={POW2}=2^14 only")
mx = max(ENCL[e][0] for i, (a, e) in enumerate(rows) if LO + i != POW2)
print(f"largest lower numerator actually used: {mx:,}")
