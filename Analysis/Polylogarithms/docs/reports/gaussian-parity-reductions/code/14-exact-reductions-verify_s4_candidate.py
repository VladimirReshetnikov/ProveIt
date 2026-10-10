#!/usr/bin/env python3
"""Independent numerical diagnostic for the still-conjectural S4 identity.

This program does not prove the identity. It compares a real integral for S4
with Mellin integrals for two same-argument multiple polylogarithms.
"""
import json
from pathlib import Path
import mpmath as mp


def main():
    mp.mp.dps = 50
    s4 = -mp.quad(lambda t: (-mp.log(t))**3 * mp.log1p(t*t)/(1+t*t),
                  [0, mp.mpf("0.5"), 1])/6

    def double(a, b):
        return mp.j/mp.factorial(a-1)*mp.quad(
            lambda t: (-mp.log(t))**(a-1)*mp.polylog(b, mp.j*t)/(1-mp.j*t),
            [0, mp.mpf("0.5"), 1])

    g41, g32 = mp.im(double(4, 1)), mp.im(double(3, 2))
    b4 = mp.im(mp.polylog(4, mp.j))
    proposed = (58*g41+24*g32)/7+19*mp.pi**5/3584-2*b4*mp.log(2)
    error = abs(s4-proposed)
    assert error < mp.mpf("1e-45"), "Numerical diagnostic disagrees."
    result = {
        "mathematical_status": "CONJECTURE; numerical diagnostic only",
        "working_decimal_digits": mp.mp.dps,
        "s4": mp.nstr(s4, 50),
        "g41": mp.nstr(g41, 50),
        "g32": mp.nstr(g32, 50),
        "proposed_rhs": mp.nstr(proposed, 50),
        "absolute_residual": mp.nstr(error, 12),
        "note": "No interval certificate and no proof of equality is asserted."
    }
    destination = Path(__file__).resolve().parents[1]/"data"/"s4_diagnostic.json"
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
