"""Independent numerical diagnostics for the reciprocal endpoint section.

These computations corroborate conventional proofs. They are not interval
certificates and make no claims about the global Taylor radius.
"""
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 80
rows = []
for m in (2, 3, 4):
    alpha = mp.mpf(1) / m
    s = 1 + alpha
    b = -mp.gamma(-alpha)
    for y in map(mp.mpf, ("0.01", "0.003", "0.001")):
        def residual(xi):
            return mp.zeta(s) - mp.polylog(s, mp.exp(-xi ** m)) - y

        xi = mp.findroot(residual, (y / b, mp.mpf("1.01") * y / b))
        t = xi ** m
        approximation = y ** m / b ** m
        approximation -= m * mp.zeta(alpha) * y ** (2 * m - 1) / b ** (2 * m)
        rows.append({
            "m": m,
            "y": str(y),
            "relative_error_two_terms": mp.nstr(abs((approximation - t) / t), 20),
            "scaled_next_term": mp.nstr((t - approximation) / y ** (3 * m - 2), 20),
        })

cut = []
for s in map(mp.mpf, ("1.25", "1.4")):
    for u in map(mp.mpf, ("0.01", "0.0001", "0.000001")):
        value = mp.polylog(s, mp.exp(u) + mp.mpc(0, "1e-100"))
        ratio = (abs(value) - mp.zeta(s)) / u ** (s - 1)
        expected = mp.gamma(1 - s) * mp.cos(mp.pi * (s - 1))
        cut.append({
            "s": str(s),
            "u": str(u),
            "scaled_modulus_difference": mp.nstr(ratio, 20),
            "limit": mp.nstr(expected, 20),
        })

result = {
    "precision_dps": mp.mp.dps,
    "meaning": "Numerical corroboration of proved formulas; not interval certificates.",
    "reciprocal_endpoint": rows,
    "cut_modulus": cut,
}
destination = Path(__file__).resolve().parent.parent / "data" / "endpoint_diagnostics.json"
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(f"Wrote {destination.name}: {len(rows)} endpoint and {len(cut)} cut checks")
