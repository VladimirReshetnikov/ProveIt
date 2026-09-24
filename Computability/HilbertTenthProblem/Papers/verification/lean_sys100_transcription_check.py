#!/usr/bin/env python3
"""Check that the Lean structures `Jones1980.Sys100` and `Jones1980.Kernel3`
(`Lean/Diophantine/Paper1980/System100.lean`, `Kernel3.lean`) transcribe the
100-operation counter-machine system of `explore_state_top_doubled_grid.json`.

Each Lean field is retyped below as a SymPy expression `lhs - rhs`, with the ROM
constants as symbols; the receipt's numerals (read off its instruction schedule)
are substituted, and the script verifies that every field equals the receipt's
residual `source` (plus its `correction`, which records the use of earlier
equations in the computed register) up to sign.  Run with
`PYTHONUTF8=1 python lean_sys100_transcription_check.py`.
"""
import json
import os
import sympy as sp

x = sp.Symbol('x')
q, Jrep, W, H, v, Tgap, A0, A1, Kp, Km, Dzero, alphaI, R, PC, PV, beta, zgrid, r = sp.symbols(
    'q Jrep W H v Tgap A0 A1 Kp Km Dzero alphaI R PC PV beta zgrid r')
a, c, d, f, h, i, j, k, o, s, w, tau, eta, zeta, ga, y_aux = sp.symbols(
    'a c d f h i j k o s w tau eta zeta ga y_aux')
Zon, B0, K, g, I, hs, hz, S = sp.symbols('Zon B0 K g I hs hz S')

D0 = q**12


def kernel3(D0):
    """The ten fields of `Jones1980.Kernel3 D0 r a c d f h i j k o s w tau eta zeta ga y`."""
    return {
        'E9': tau * (tau + 1) - ((w * D0 * (s * D0))**2 + w * D0) * (k * (s * D0))**2,
        'E10a': c - (k * (s * D0) + eta),
        'E10b': k - (eta + zeta),
        'E11': k - (r + 1 + h * (w * D0) * (s * D0)),
        'E12': a - s * D0 * (w * D0 + 1),
        'E14': d - (w * D0 + a * c + ga * (6 * a + 8)),
        'E15': d**2 - (1 + (a**2 + 6 * a + 8) * c**2),
        'E16': (i * c**2)**2 - (a**2 + 6 * a + 8) * (f**2 - 1),
        'E17': ((a**2 + 6 * a + 8) * (f**2 - 1)) * ((2 * r + 1 + j * c)**2 - y_aux**2)
               - (1 - y_aux**2),
        'E17b': (2 * r + 1 + j * c) - (c + o * f),
    }


X = Km + q**2 * (Dzero + q**2 * (A0 + q**2 * (A1 + q**2 * (PV + q**2 * PC))))
lean = {
    'E0': q - (Jrep + 1),
    'E1': q - W * v,
    'E2': H * R - (H + 2 * Jrep),
    'E3': Kp + Km - H,
    'E4': (B0 - 1) * (Zon + zgrid) + 1 - R,
    'E5': 6 * Tgap + 3 * Dzero - Dzero * R,
    'E6': W * (A0 + A1 + Kp) + 4 * x - (A0 + A1 + W * Km),
    'E7': 4 * x + alphaI - R,
    'E8': 2 * r + 1 - (q**12 + (Jrep * X + (q**2 + 1) * (H + q**4 * Tgap)
                                + q**8 * (H * (zgrid + q**2 * S)))),
    'E19': W - R**3,
    'E20': r + beta - q**12,
    'E21': R * K * PC - (g * PC + g * I * (2 * Jrep) + R * (PV + hs * Kp + hz * Dzero)),
}
lean.update(kernel3(D0))

# the receipt's equalities, in the order of its residual list, mapped to Lean fields
order = ['E0', 'E1', 'E2', 'E3', 'E4', 'E5', 'E6', 'E7', 'E8',
         'E9', 'E10a', 'E10b', 'E11', 'E12', 'E14', 'E15', 'E16', 'E17', 'E17b',
         'E19', 'E20', 'E21']

here = os.path.dirname(os.path.abspath(__file__))
receipt = json.load(open(os.path.join(here, 'explore_state_top_doubled_grid.json'),
                         encoding='utf-8'))
arith = receipt['arithmetic']
assert arith['operations'] == 100 and arith['unknown_count'] == 34 and arith['equations'] == 22
ins = arith['primitive_instructions']


def numeral(result, operation=None):
    for e in ins:
        if e['result'] == result and (operation is None or e['operation'] == operation):
            for side in ('left', 'right'):
                if isinstance(e[side], int) and e[side] > 100:
                    return e[side]
    raise KeyError(result)


consts = {
    Zon: numeral('grid_width'),
    K: numeral('WK', '*'),
    g: numeral('WK', '+'),
    hs: numeral('sign_output'),
    hz: numeral('nozero_output'),
    S: numeral('paired_grid_shift'),
}
gI = numeral('route_final')
assert gI % consts[g] == 0, 'the route coefficient 2gI is not a multiple of g'
consts[I] = gI // consts[g]
b0m1 = [e for e in ins if e['result'] == 'grid_width_product'][0]['left']
consts[B0] = b0m1 + 1
print('ROM constants: B0 =', consts[B0], ', I = 3^320' if consts[I] == 3**320 else '')

names = {str(sym): sym for sym in [x, q, Jrep, W, H, v, Tgap, A0, A1, Kp, Km, Dzero, alphaI, R,
                                    PC, PV, beta, zgrid, r, a, c, d, f, h, i, j, k, o, s, w, tau,
                                    eta, zeta, ga, y_aux]}
ok = True
residuals = arith['residuals']
assert len(residuals) == len(order)
for entry, name in zip(residuals, order):
    src = sp.sympify(entry['source'], locals=names)
    corr = sp.sympify(entry['correction'], locals=names)
    mine = sp.expand(lean[name].subs(consts))
    match = any(sp.expand(mine - t) == 0
                for t in (src, -src, src + corr, -(src + corr), src - corr, -(src - corr)))
    ok &= match
    print(f"{name:6s} {entry['equality']!s:40s} {'OK' if match else 'MISMATCH'}")
print('ALL MATCH' if ok else 'FAILURE')
raise SystemExit(0 if ok else 1)
