#!/usr/bin/env python3
"""Check that the Lean structure `Jones1980.Sys90`
(`Lean/Diophantine/Paper1980/System90.lean`) transcribes the 90-operation
system of `round37_1980_binary_product_certificate.json`.

Each Lean field is retyped below as a SymPy expression `lhs - rhs`; the
script verifies that it equals the receipt's `source_residual_polynomial`
up to sign (with `sigma` replaced by its defining expression where the
receipt inlines it).  Run with `PYTHONUTF8=1 python lean_sys90_transcription_check.py`.
"""
import json
import os
import sympy as sp

x, V, H, Tindex = sp.symbols('x V H Tindex')
a, b, c, d, e, f, g, h, i, j, k, l, n, o, q, r, s, t, w = sp.symbols(
    'a b c d e f g h i j k l n o q r s t w')
al, ga, eta, th, la, tau, phi, ka, mu, rho, Delta, beta, zeta, sigma, y_aux = sp.symbols(
    'al ga eta th la tau phi ka mu rho Delta beta zeta sigma y_aux')

lean = {
    'positive_product_bound': (l + sigma + al) - q,
    'E1b': b - (x + beta),
    'E2': (la + q**2) - (1 + la * (H + b + 2)),
    'E3': th - (H + b),
    'E4/E5 packed': (l + e * q) - (V + t * th),
    'E6': n - q**8,
    'E7': r - ((g + q**2 * (l + e * q + q**2 * sigma)) * (n**2 - n)
               + (q**2 * (1 + th * la) - b * l + th * l * q**4) * (n**2 - 1)),
    'E9': tau * (tau + 1) - (w * n**2 * (s * n**2)**2) * (w * n**2 * (s * n**2)**2 + 1) * k**2,
    'E10a': c - (k * (s * n**2) + eta),
    'E10b': k - (eta + zeta),
    'E11': k - (r + 1 + h * (w * n**2) * (s * n**2)),
    'E12': a - s * n**2 * (w * n**2 + 1),
    'E13': c - (ka + phi),
    'E14': d - (w * n**2 + a * c + ga * (4 * a + 3)),
    'E15': d**2 - (1 + (a**2 + 4 * a + 3) * c**2),
    'E16': (i * c**2)**2 - (a**2 + 4 * a + 3) * (f**2 - 1),
    'E17': ((a**2 + 4 * a + 3) * (f**2 - 1)) * ((2 * r + 1 + j * c)**2 - y_aux**2)
           - (1 - y_aux**2),
    'E17 normalized-root congruence': (2 * r + 1 + j * c) - (c + o * f),
    'E18': mu - (q + ka * (a + 2 - (H + b + 2))
                 + rho * (2 * (a + 2) * (H + b + 2) - (H + b + 2)**2 - 1)),
    'E19': mu**2 - (1 + (a**2 + 4 * a + 3) * ka**2),
    'E20': ka - (Tindex + Delta * a),
    'positive_product': sigma - (e - l) * (x + g)**2,
}
sigma_def = (e - l) * (x + g)**2

here = os.path.dirname(os.path.abspath(__file__))
receipt = json.load(open(os.path.join(here, 'round37_1980_binary_product_certificate.json'),
                         encoding='utf-8'))
assert receipt['operations'] == 90 and receipt['unknowns'] == 34 and receipt['equations'] == 22
names = {str(v): v for v in [x, V, H, Tindex, a, b, c, d, e, f, g, h, i, j, k, l, n, o, q, r,
                              s, t, w, al, ga, eta, th, la, tau, phi, ka, mu, rho, Delta, beta,
                              zeta, sigma, y_aux]}
ok = True
for entry in receipt['residual_polynomials']:
    name = entry['equation']
    src = sp.sympify(entry['source_residual_polynomial'], locals=names)
    mine = lean[name]
    if name == 'E7':
        mine = mine.subs(sigma, sigma_def)
    diff_plus = sp.expand(mine - src)
    diff_minus = sp.expand(mine + src)
    match = diff_plus == 0 or diff_minus == 0
    ok &= match
    print(f"{name:32s} {'OK' if match else 'MISMATCH'}"
          + ('' if match else f"  mine-src = {diff_plus}"))
assert set(lean) == {e['equation'] for e in receipt['residual_polynomials']}
print('ALL MATCH' if ok else 'FAILURE')
raise SystemExit(0 if ok else 1)
