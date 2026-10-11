"""Independent numerical diagnostic of the sign in Young 2024, pp. 11--12."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 100
n_terms = 180

def double_zeta_n1(n):
    return (mp.mpf(n) * mp.zeta(n + 1) - mp.fsum(
        mp.zeta(n - j) * mp.zeta(j + 1) for j in range(1, n - 1)
    )) / 2

nu01 = mp.fsum(
    (-1) ** n * double_zeta_n1(n) / n for n in range(2, n_terms + 1)
)
nu_minus1_0 = mp.log(2) + mp.fsum(
    (-1) ** n * (mp.zeta(n) - 1) / (n - 1)
    for n in range(2, n_terms + 1)
)
c2 = (mp.euler ** 2 - mp.zeta(2)) / 2
computed = nu01 - nu_minus1_0 - c2
report = {
    "kind": "noninterval numerical diagnostic",
    "working_digits": mp.mp.dps,
    "terms": n_terms,
    "nu01": mp.nstr(nu01, 85),
    "nu_minus1_0": mp.nstr(nu_minus1_0, 85),
    "corollary3_depth1_value": mp.nstr(computed, 85),
    "conventional_gamma1": mp.nstr(mp.stieltjes(1), 85),
    "literal_linear_coefficient": mp.nstr(-mp.stieltjes(1), 85),
    "residual_conventional": mp.nstr(computed - mp.stieltjes(1), 15),
}
print(json.dumps(report, indent=2))

assert abs(computed-mp.stieltjes(1)) < mp.mpf('1e-50')
assert computed < 0
(Path(__file__).resolve().parent.parent / 'results' / 'young_sign_diagnostic.json').write_text(json.dumps(report,indent=2)+'\n')
