#!/usr/bin/env python3
"""Check the literal new circuit and data; finite checks are not consistency proofs."""
import gzip
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from fractions import Fraction
from math import isqrt

ROOT = Path(__file__).resolve().parent


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    import build
    packet = build.build()
    raw = (ROOT / "p11_positive_degree277.json").read_bytes()
    require(raw == (json.dumps(packet, indent=2) + "\n").encode(), "literal circuit regeneration")
    subprocess.run([sys.executable, str(ROOT / "audit.py")], check=True, capture_output=True)
    from independent_ring import Ring
    Q, x, y = [Ring.variable(z) for z in ("Q", "x", "y")]
    xp = (2*Q-1)*x-2*(Q-1)*y
    yp = (2*Q-1)*y-2*Q*x
    require(Q*xp*xp-(Q-1)*yp*yp == Q*x*x-(Q-1)*y*y, "descent norm identity")
    binding = json.loads((ROOT / "coefficients/ACTIVE_BINDING.json").read_text())
    values = {}
    for name, item in binding["ports"].items():
        comp = (ROOT / "coefficients" / item["gzip_payload"]).read_bytes()
        data = gzip.decompress(comp)
        require(hashlib.sha256(comp).hexdigest() == item["gzip_sha256"], "compressed hash " + name)
        require(hashlib.sha256(data).hexdigest() == item["sha256"], "integer hash " + name)
        values[name] = int.from_bytes(data, "little")
        require(values[name].bit_length() == item["bits"], "bit length " + name)
    beta = values["beta"]
    require(beta == (1 << 590069)-1, "fixed radix")
    require(0 < values["MC"] < beta and 0 < values["MF"] < 2*beta, "fixed mask hypotheses")
    require(values["K0"] > 0 and beta % 3 == 1, "other fixed hypotheses")
    whole = ROOT / "coefficients" / binding["whole_binding"]
    require(hashlib.sha256(whole.read_bytes()).hexdigest() == binding["whole_binding_sha256"], "coherent tuple")
    ledger = json.loads((ROOT / "SOURCE_PINS.json").read_text())
    for item in ledger["files"]:
        data = (ROOT / item["local_path"]).read_bytes()
        require(hashlib.sha256(data).hexdigest() == item["sha256"], "retained source identity")
    # A small exact diagnostic checks the descent on actual Pell solutions.
    # This supplements, and does not prove, the general induction in PROOF.md.
    diagnostic = 0
    for q in range(2, 33):
        for v in range(1, 250):
            numerator = q*v*v-1
            denominator = q-1
            ratio = Fraction(numerator, denominator)
            a, b = isqrt(ratio.numerator), isqrt(ratio.denominator)
            if a*a != ratio.numerator or b*b != ratio.denominator:
                continue
            yy = Fraction(a, b)
            require(yy.denominator == 1, "rational integrality diagnostic")
            if v > 1:
                xx1 = (2*q-1)*v-2*(q-1)*yy
                yy1 = (2*q-1)*yy-2*q*v
                require(xx1.denominator == 1 and 0 < abs(xx1) < v, "strict integral descent")
                require(q*xx1*xx1-(q-1)*yy1*yy1 == 1, "preserved norm diagnostic")
            diagnostic += 1
    receipt = {
        "status": "PASS", "python_optimization": sys.flags.optimize,
        "circuit_sha256": hashlib.sha256(raw).hexdigest(),
        "variables": 11, "domain": "strictly positive integers", "degree": 277,
        "operations": packet["operations"], "system_operations": packet["system_operations"],
        "source_pin": ledger["pin"], "fixed_tuple_identity_checked": True,
        "descent_norm_identity": True, "pell_diagnostic_cases": diagnostic,
        "scope": "Exact finite algebra and coefficient checks. No full native or object-language ZFC kernel certificate is asserted."
    }
    (ROOT / ("VERIFICATION_OPTIMIZED.json" if sys.flags.optimize else "VERIFICATION.json")).write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
