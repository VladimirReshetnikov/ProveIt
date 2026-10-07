"""Independent stable diagnostic quadrature; not an interval certificate."""
import json
from pathlib import Path
import mpmath as mp

rows = []
for dps in (50, 100, 150):
    mp.mp.dps = dps
    def integrand(theta):
        u = (mp.pi / 4) * mp.cos(theta) ** 2
        return 2 * mp.sqrt(2) * mp.sqrt(u / mp.tan(u)) if u else 2 * mp.sqrt(2)
    length = mp.quad(integrand, [0, mp.pi / 4, mp.pi / 2])
    rows.append({"dps": dps, "L": mp.nstr(length, dps)})
result = {"status": "Diagnostic quadrature only; no interval certificate", "rows": rows}
print(json.dumps(result, indent=2))
Path(__file__).with_name("length_diagnostics.json").write_text(json.dumps(result, indent=2) + "\n")
