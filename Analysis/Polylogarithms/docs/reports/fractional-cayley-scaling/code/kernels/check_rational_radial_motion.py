#!/usr/bin/env python3
"""Selected rational-order radial diagnostics; not interval certificates."""
import json
from pathlib import Path
import check_fractional_radial_motion as radial


def main():
    mp = radial.mp
    mp.mp.dps = 70
    max_terms = radial.nterms(mp.mpf(".98"), mp.mpf("1e-50"))
    rows = []
    for num, den in [(21, 16), (172, 131)]:
        a, b = mp.mpf(num)/den, mp.mpf(".5")
        coeff = radial.coefficients(a, b, max_terms)
        for rho_text in ["0.3", "0.9", "0.98"]:
            row = radial.solve_row(a, b, mp.mpf(rho_text), coeff)
            row["a_exact"] = f"{num}/{den}"
            row["b_exact"] = "1/2"
            row["cos_theta"] = mp.nstr(mp.mpf(row["eta"])*mp.mpf(rho_text), 40)
            rows.append(row)
    data = {"status": "Diagnostics with analytic truncation bounds; rounding is not interval-enclosed.",
            "rows": rows}
    output = Path(__file__).resolve().parents[2] / "data" / "kernels" / "rational_radial_diagnostics.json"
    output.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"output": str(output), "rows": len(rows)}))


if __name__ == "__main__":
    main()
