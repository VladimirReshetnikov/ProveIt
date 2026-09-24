#!/usr/bin/env python3
"""Check that the Lean structures `Jones1980.Sys91` and `Jones1980.Kernel3`
(`Lean/Diophantine/Paper1980/System91.lean`, `Kernel3.lean`) transcribe the
91-operation tag certificate of `explore_product_coordinate_tag.json`, in both
leading branches.

Each Lean field is retyped below as a SymPy expression `lhs - rhs` with the tag
constants as symbols (the receipt writes them `Khalf, Uthird, B, C, jguard, c`);
the script verifies that every field equals the receipt's residual `source`
(plus its `correction`) up to sign.  Run with
`PYTHONUTF8=1 python lean_sys91_transcription_check.py`.
"""
import json
import os
import sympy as sp

Ninit, Linit = sp.symbols('Ninit Linit')
Q, S1, Tcontent, E, H, R, L, q, v, r, betaP = sp.symbols('Q S1 Tcontent E H R L q v r betaP')
D, Z = sp.symbols('transport_scale AH')
pa, pc, pd, pf, ph, pi, pj, pk, po, ps, pw, ptau, peta, pzeta, pga, py = sp.symbols(
    'pell_a pell_c pell_d pell_f pell_h pell_i pell_j pell_k pell_o pell_s pell_w pell_tau '
    'pell_eta pell_zeta pell_ga pell_y_aux')
Khalf, Uthird, B, C, jguard, cc = sp.symbols('Khalf Uthird B C jguard c')

D0 = q**9


def kernel3(D0):
    """The ten fields of `Jones1980.Kernel3 D0 r a c d f h i j k o s w tau eta zeta ga y`."""
    a, c, d, f, h, i, j, k, o, s, w, tau, eta, zeta, ga, y = (
        pa, pc, pd, pf, ph, pi, pj, pk, po, ps, pw, ptau, peta, pzeta, pga, py)
    return {
        'E9': tau * (tau + 1) - ((w * D0 * (s * D0))**2 + w * D0) * (k * (s * D0))**2,
        'E10a': c - (k * (s * D0) + eta),
        'E10b': k - (eta + zeta),
        'E11': k - (r + 1 + h * (w * D0) * (s * D0)),
        'E12': a - s * D0 * (w * D0 + 1),
        'E14': d - (w * D0 + a * c + ga * (6 * a + 8)),
        'E15': d**2 - (1 + (a**2 + 6 * a + 8) * c**2),
        'E16': (i * c**2)**2 - (a**2 + 6 * a + 8) * (f**2 - 1),
        'E17': ((a**2 + 6 * a + 8) * (f**2 - 1)) * ((2 * r + 1 + j * c)**2 - y**2) - (1 - y**2),
        'E17b': (2 * r + 1 + j * c) - (c + o * f),
    }


def lean_fields(eps):
    N = 3 * Tcontent + S1 if eps == 0 else 3 * Tcontent - 2 * Q
    M1 = 2 * Q + S1
    P = (H + (q - 1) * S1 + q**2 * (Q + q * (Q + Z))
         + q**4 * (L + (q - 1) * M1 + q**2 * (cc * H + (q - 1) * E + q**2 * (N + jguard * Z))))
    fields = {
        'E0': Khalf * D - R,
        'E1': D * (Tcontent - E + Uthird * M1) - (N - Ninit),
        'E2': D * (L + (B - 1) * M1) - (L - Linit + 3 * q),
        'E3': R * H + 1 - (H + q),
        'E4': R * H - C * Z,
        'E5': R * v - q,
        'E6': 2 * r + 1 - (q**9 + 2 * P),
        'E7': r + betaP - q**9,
    }
    fields.update(kernel3(D0))
    return fields


order = ['E0', 'E1', 'E2', 'E3', 'E4', 'E5', 'E6', 'E7',
         'E9', 'E10a', 'E10b', 'E11', 'E12', 'E14', 'E15', 'E16', 'E17', 'E17b']

here = os.path.dirname(os.path.abspath(__file__))
receipt = json.load(open(os.path.join(here, 'explore_product_coordinate_tag.json'),
                         encoding='utf-8'))
names = {str(sym): sym for sym in [Ninit, Linit, Q, S1, Tcontent, E, H, R, L, q, v, r, betaP, D, Z,
                                    pa, pc, pd, pf, ph, pi, pj, pk, po, ps, pw, ptau, peta, pzeta,
                                    pga, py, Khalf, Uthird, B, C, jguard, cc]}
ok = True
for branch in receipt['sources']:
    eps = branch['leading']
    assert branch['operations'] == 91 and branch['positive_unknowns'] == 29
    assert branch['equations'] == 18
    lean = lean_fields(eps)
    residuals = branch['sources']
    assert len(residuals) == len(order)
    print(f'--- leading branch epsilon = {eps}')
    for entry, name in zip(residuals, order):
        src = sp.sympify(entry['source'], locals=names)
        corr = sp.sympify(entry['correction'], locals=names)
        mine = sp.expand(lean[name])
        match = any(sp.expand(mine - t) == 0
                    for t in (src, -src, src + corr, -(src + corr), src - corr, -(src - corr)))
        ok &= match
        print(f"{name:6s} {entry['equality']!s:44s} {'OK' if match else 'MISMATCH'}")
print('ALL MATCH' if ok else 'FAILURE')
raise SystemExit(0 if ok else 1)
