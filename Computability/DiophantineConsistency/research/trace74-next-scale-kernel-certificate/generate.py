#!/usr/bin/env python3
"""Generate untrusted deterministic Pell residue/Bézout benchmark traces.

Run with ``python3 -I -S -B generate.py B OUTPUT_DIR``. The resulting Lean
file uses kernel reduction (``by decide``), never ``native_decide``.
"""
import json
import math
import pathlib
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")
sys.set_int_max_str_digits(0)

if len(sys.argv) != 3:
    raise SystemExit("usage: generate.py B OUTPUT_DIR")
B = int(sys.argv[1])
if B != 65537:
    raise SystemExit("only the approved next scale B=65537 is allowed")
out = pathlib.Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
r = 3056651345
bits = [c == "1" for c in bin(r)[2:]]
q = 1 << B
m = q*q-1
x = pow(2, r, m)
L = (q*(x+1)+1) % m
D = (L*L-1) % m
state = (1 % m, 0)
states = [state]
for bit in bits:
    X, Y = state
    A = (X*X+D*Y*Y) % m
    C = (2*X*Y) % m
    state = ((L*A+D*C) % m, (A+L*C) % m) if bit else (A, C)
    states.append(state)
Y = state[1]
g = math.gcd(Y, m)
if g != 1:
    raise SystemExit(f"scaled B={B}: gcd is {g}, not 1")
s = pow(Y, -1, m)
t = (s*Y-1)//m
assert s*Y == t*m+1

trace = {
    "version": 1, "B": B, "index": r, "bits": "".join("1" if b else "0" for b in bits),
    "modulus": str(m), "L": str(L), "D": str(D),
    "states": [[str(a), str(b)] for a, b in states],
    "bezout_s": str(s), "bezout_t": str(t),
}
(out / "trace.json").write_text(json.dumps(trace, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")

lines = [
    "import Mathlib.Data.Nat.GCD.Basic",
    "set_option maxRecDepth 65536",
    "set_option maxHeartbeats 0",
    "namespace Trace74ScaledCertificate",
    f"def modulus : Nat := {m}", f"def coeffL : Nat := {L}", f"def coeffD : Nat := {D}",
    "def step (xy : Nat × Nat) (bit : Bool) : Nat × Nat :=",
    "  let A := (xy.1*xy.1 + coeffD*xy.2*xy.2) % modulus",
    "  let C := (2*xy.1*xy.2) % modulus",
    "  if bit then ((coeffL*A+coeffD*C)%modulus, (A+coeffL*C)%modulus) else (A,C)",
]
for i, (a, b) in enumerate(states):
    lines.append(f"def state{i:02} : Nat × Nat := ({a}, {b})")
for i, bit in enumerate(bits):
    lines.append(f"theorem transition{i:02} : step state{i:02} {'true' if bit else 'false'} = state{i+1:02} := by decide")
lines.extend([
    f"def bezoutS : Nat := {s}", f"def bezoutT : Nat := {t}",
    "theorem bezout : bezoutS*state32.2 = bezoutT*modulus+1 := by decide",
    "theorem coprime : Nat.Coprime state32.2 modulus := by",
    "  have h₁ : Nat.gcd state32.2 modulus ∣ bezoutS*state32.2 :=",
    "    dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) bezoutS",
    "  have h₂ : Nat.gcd state32.2 modulus ∣ bezoutT*modulus :=",
    "    dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) bezoutT",
    "  have h₃ : Nat.gcd state32.2 modulus ∣ 1 := by",
    "    have h := Nat.dvd_sub h₁ h₂",
    "    simpa only [bezout,Nat.add_sub_cancel_left] using h",
    "  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h₃)",
    "#print axioms Trace74ScaledCertificate.transition00",
    "#print axioms Trace74ScaledCertificate.transition31",
    "#print axioms Trace74ScaledCertificate.bezout",
    "#print axioms Trace74ScaledCertificate.coprime",
    "end Trace74ScaledCertificate",
])
(out / "Certificate.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"B={B} bits={len(bits)} modulus_bits={m.bit_length()} residue_bits={Y.bit_length()} gcd={g}")
