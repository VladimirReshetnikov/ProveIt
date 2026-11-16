#!/usr/bin/env python3
"""Exact symbolic regression checks for the spherical-trigonometry packet.

The checker verifies finite polynomial/rational generators.  It does not claim
to replace the object-language iPRA soundness proof described in the report.
All computations are exact SymPy arithmetic; no floating-point sampling is
used.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ART = ROOT / "artifacts"
ART.mkdir(parents=True, exist_ok=True)

ledger: list[dict[str, Any]] = []


def record(name: str, family: str, residual: sp.Expr) -> None:
    residual = sp.factor(sp.expand(residual))
    ok = residual == 0
    ledger.append(
        {
            "id": name,
            "family": family,
            "status": "pass" if ok else "fail",
            "residual": str(residual),
        }
    )
    if not ok:
        raise AssertionError(f"{name}: nonzero residual {residual}")


# ---------------------------------------------------------------------------
# Core spherical ideal
# ---------------------------------------------------------------------------
x, y, z, sa, sb, sc, tau = sp.symbols("x y z sa sb sc tau")
cA, sA, cB, sB, cC, sC = sp.symbols("cA sA cB sB cC sC")

gram = 1 + 2 * x * y * z - x**2 - y**2 - z**2
core_relations = [
    sa**2 + x**2 - 1,
    sb**2 + y**2 - 1,
    sc**2 + z**2 - 1,
    tau**2 - gram,
]
G = sp.groebner(core_relations, sa, sb, sc, tau, x, y, z, order="grevlex")

core_subs = {
    cA: (x - y * z) / (sb * sc),
    sA: tau / (sb * sc),
    cB: (y - z * x) / (sc * sa),
    sB: tau / (sc * sa),
    cC: (z - x * y) / (sa * sb),
    sC: tau / (sa * sb),
}


def core_remainder(expr: sp.Expr) -> sp.Expr:
    rat = sp.together(expr.subs(core_subs, simultaneous=True))
    num = sp.expand(rat.as_numer_denom()[0])
    return sp.expand(G.reduce(num)[1])


for name, expr in [
    ("side_cosine_A", x - (y * z + sb * sc * cA)),
    ("side_cosine_B", y - (z * x + sc * sa * cB)),
    ("side_cosine_C", z - (x * y + sa * sb * cC)),
    ("angle_unit_A", cA**2 + sA**2 - 1),
    ("angle_unit_B", cB**2 + sB**2 - 1),
    ("angle_unit_C", cC**2 + sC**2 - 1),
    ("angle_cosine_A", cA + cB * cC - sB * sC * x),
    ("angle_cosine_B", cB + cC * cA - sC * sA * y),
    ("angle_cosine_C", cC + cA * cB - sA * sB * z),
    ("sine_cross_AB", sA * sb - sB * sa),
    ("sine_cross_BC", sB * sc - sC * sb),
    ("sine_cross_CA", sC * sa - sA * sc),
]:
    record(name, "core cosine/sine laws", core_remainder(expr))

# Haversine laws, written without hav notation.
side_hav = [
    ("haversine_A", (1 - x) - (1 - (y * z + sb * sc)) - sb * sc * (1 - cA)),
    ("haversine_B", (1 - y) - (1 - (z * x + sc * sa)) - sc * sa * (1 - cB)),
    ("haversine_C", (1 - z) - (1 - (x * y + sa * sb)) - sa * sb * (1 - cC)),
]
for name, expr in side_hav:
    record(name, "haversine", core_remainder(expr))

angle_hav = [
    (
        "dual_haversine_A",
        (1 - cA) - (1 - (-cB * cC + sB * sC)) - sB * sC * (1 - x),
    ),
    (
        "dual_haversine_B",
        (1 - cB) - (1 - (-cC * cA + sC * sA)) - sC * sA * (1 - y),
    ),
    (
        "dual_haversine_C",
        (1 - cC) - (1 - (-cA * cB + sA * sB)) - sA * sB * (1 - z),
    ),
]
for name, expr in angle_hav:
    record(name, "dual haversine", core_remainder(expr))

# Cotangent rules after multiplying by the sine denominators.
cotangent_checks = [
    ("CT1", y * cC * sa * sA - x * sb * sA + cA * sC * sa),
    ("CT2", y * cA * sc * sC - z * sb * sC + cC * sA * sc),
    ("CT3", z * cA * sb * sB - y * sc * sB + cB * sA * sb),
    ("CT4", z * cB * sa * sA - x * sc * sA + cA * sB * sa),
    ("CT5", x * cB * sc * sC - z * sa * sC + cC * sB * sc),
    ("CT6", x * cC * sb * sB - y * sa * sB + cB * sC * sb),
]
for name, expr in cotangent_checks:
    record(name, "cotangent four-part", core_remainder(expr))

five_part_checks = [
    ("five_part_a", x * sc - sa * z * cB - sb * cA),
    ("five_part_b", y * sa - sb * x * cC - sc * cB),
    ("five_part_c", z * sb - sc * y * cA - sa * cC),
]
for name, expr in five_part_checks:
    record(name, "five-part", core_remainder(expr))

cagnoli_checks = [
    ("cagnoli_A", sb * sc + y * z * cA - sB * sC + cB * cC * x),
    ("cagnoli_B", sc * sa + z * x * cB - sC * sA + cC * cA * y),
    ("cagnoli_C", sa * sb + x * y * cC - sA * sB + cA * cB * z),
]
for name, expr in cagnoli_checks:
    record(name, "Cagnoli", core_remainder(expr))

record(
    "solid_angle_norm",
    "solid angle",
    core_remainder((1 + x + y + z) ** 2 + tau**2 - 2 * (1 + x) * (1 + y) * (1 + z)),
)

# ---------------------------------------------------------------------------
# Right and quadrantal specializations
# ---------------------------------------------------------------------------
right_subs = dict(core_subs)
right_subs.update({z: x * y, tau: sa * sb})
Gr = sp.groebner(
    [sa**2 + x**2 - 1, sb**2 + y**2 - 1, sc**2 + x**2 * y**2 - 1],
    sa,
    sb,
    sc,
    x,
    y,
    order="grevlex",
)


def right_remainder(expr: sp.Expr) -> sp.Expr:
    rat = sp.together(expr.subs(core_subs, simultaneous=True).subs({z: x * y, tau: sa * sb}, simultaneous=True))
    num = sp.expand(rat.as_numer_denom()[0])
    return sp.expand(Gr.reduce(num)[1])


right_checks = [
    ("R1", z - x * y),
    ("R2", sa - sA * sc),
    ("R3", sb - sB * sc),
    ("R4", sa * cA - x * sA * sb),
    ("R5", sb * cB - y * sB * sa),
    ("R6", sb * z - y * cA * sc),
    ("R7", sa * z - x * cB * sc),
    ("R8", cA - sB * x),
    ("R9", cB - sA * y),
    ("R10", z * sA * sB - cA * cB),
]
for name, expr in right_checks:
    record(name, "right spherical triangle", right_remainder(expr))

quad_subs = dict(core_subs)
quad_subs.update({z: sp.Integer(0), sc: sp.Integer(1)})
Gq = sp.groebner(
    [sa**2 + x**2 - 1, sb**2 + y**2 - 1, tau**2 + x**2 + y**2 - 1],
    sa,
    sb,
    tau,
    x,
    y,
    order="grevlex",
)


def quad_remainder(expr: sp.Expr) -> sp.Expr:
    rat = sp.together(expr.subs(core_subs, simultaneous=True).subs({z: sp.Integer(0), sc: sp.Integer(1)}, simultaneous=True))
    num = sp.expand(rat.as_numer_denom()[0])
    return sp.expand(Gq.reduce(num)[1])


quad_checks = [
    ("Q1", cC + cA * cB),
    ("Q2", sA - sa * sC),
    ("Q3", sB - sb * sC),
    ("Q4", sA * x - cA * sa * sB),
    ("Q5", sB * y - cB * sb * sA),
    ("Q6", sB * cC + cB * x * sC),
    ("Q7", sA * cC + cA * y * sC),
    ("Q8", x - sb * cA),
    ("Q9", y - sa * cB),
    ("Q10", cC * sa * sb + x * y),
]
for name, expr in quad_checks:
    record(name, "quadrantal spherical triangle", quad_remainder(expr))

# ---------------------------------------------------------------------------
# Half-angle and half-side squared identities
# ---------------------------------------------------------------------------
ua, va, ub, vb, uc, vc = sp.symbols("ua va ub vb uc vc")
Gh = sp.groebner(
    [ua**2 + va**2 - 1, ub**2 + vb**2 - 1, uc**2 + vc**2 - 1],
    ua,
    va,
    ub,
    vb,
    uc,
    vc,
    order="grevlex",
)


def sin_add(s1: sp.Expr, c1: sp.Expr, s2: sp.Expr, c2: sp.Expr) -> sp.Expr:
    return sp.expand(s1 * c2 + c1 * s2)


def cos_add(s1: sp.Expr, c1: sp.Expr, s2: sp.Expr, c2: sp.Expr) -> sp.Expr:
    return sp.expand(c1 * c2 - s1 * s2)


def sin_signed(signs: tuple[int, int, int]) -> sp.Expr:
    ss = [ua if signs[0] > 0 else -ua, ub if signs[1] > 0 else -ub, uc if signs[2] > 0 else -uc]
    cs = [va, vb, vc]
    s12 = sin_add(ss[0], cs[0], ss[1], cs[1])
    c12 = cos_add(ss[0], cs[0], ss[1], cs[1])
    return sin_add(s12, c12, ss[2], cs[2])


def cos_signed(signs: tuple[int, int, int]) -> sp.Expr:
    ss = [ua if signs[0] > 0 else -ua, ub if signs[1] > 0 else -ub, uc if signs[2] > 0 else -uc]
    cs = [va, vb, vc]
    s12 = sin_add(ss[0], cs[0], ss[1], cs[1])
    c12 = cos_add(ss[0], cs[0], ss[1], cs[1])
    return cos_add(s12, c12, ss[2], cs[2])


full_s = [2 * ua * va, 2 * ub * vb, 2 * uc * vc]
full_c = [va**2 - ua**2, vb**2 - ub**2, vc**2 - uc**2]


def half_remainder(expr: sp.Expr) -> sp.Expr:
    rat = sp.together(expr)
    num = sp.expand(rat.as_numer_denom()[0])
    return sp.expand(Gh.reduce(num)[1])


# For each angle index i, the other two side indices are j,k.
for idx, (i, j, k) in enumerate([(0, 1, 2), (1, 2, 0), (2, 0, 1)]):
    # cAngle_i from side cosine law.
    cang = (full_c[i] - full_c[j] * full_c[k]) / (full_s[j] * full_s[k])
    signs_p_minus_j = [1, 1, 1]
    signs_p_minus_j[j] = -1
    signs_p_minus_k = [1, 1, 1]
    signs_p_minus_k[k] = -1
    signs_p_minus_i = [1, 1, 1]
    signs_p_minus_i[i] = -1
    sin_pj = sin_signed(tuple(signs_p_minus_j))
    sin_pk = sin_signed(tuple(signs_p_minus_k))
    sin_pi = sin_signed(tuple(signs_p_minus_i))
    sin_p = sin_signed((1, 1, 1))
    record(
        f"half_angle_sin_sq_{'ABC'[idx]}",
        "half-angle squares",
        half_remainder(full_s[j] * full_s[k] * (1 - cang) / 2 - sin_pj * sin_pk),
    )
    record(
        f"half_angle_cos_sq_{'ABC'[idx]}",
        "half-angle squares",
        half_remainder(full_s[j] * full_s[k] * (1 + cang) / 2 - sin_p * sin_pi),
    )

# The same polynomial mechanism for half-side formulas, now the half variables
# represent A/2, B/2, C/2 and the dual cosine law defines cos(a), etc.
full_S = full_s
full_C = full_c
for idx, (i, j, k) in enumerate([(0, 1, 2), (1, 2, 0), (2, 0, 1)]):
    cside = (full_C[i] + full_C[j] * full_C[k]) / (full_S[j] * full_S[k])
    signs_P_minus_i = [1, 1, 1]
    signs_P_minus_i[i] = -1
    signs_P_minus_j = [1, 1, 1]
    signs_P_minus_j[j] = -1
    signs_P_minus_k = [1, 1, 1]
    signs_P_minus_k[k] = -1
    cos_P = cos_signed((1, 1, 1))
    cos_Pi = cos_signed(tuple(signs_P_minus_i))
    cos_Pj = cos_signed(tuple(signs_P_minus_j))
    cos_Pk = cos_signed(tuple(signs_P_minus_k))
    record(
        f"half_side_sin_sq_{'abc'[idx]}",
        "half-side squares",
        half_remainder(full_S[j] * full_S[k] * (1 - cside) / 2 + cos_P * cos_Pi),
    )
    record(
        f"half_side_cos_sq_{'abc'[idx]}",
        "half-side squares",
        half_remainder(full_S[j] * full_S[k] * (1 + cside) / 2 - cos_Pj * cos_Pk),
    )

# ---------------------------------------------------------------------------
# Tetrahedral kernels
# ---------------------------------------------------------------------------
ax, ay, az, bx, by, bz, cx, cy, cz = sp.symbols(
    "ax ay az bx by bz cx cy cz"
)

a_vec = sp.Matrix([ax, ay, az])
b_vec = sp.Matrix([bx, by, bz])
c_vec = sp.Matrix([cx, cy, cz])


def cross(u: sp.Matrix, v: sp.Matrix) -> sp.Matrix:
    return sp.Matrix(
        [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]
    )


N1 = -cross(b_vec, c_vec)
N2 = -cross(c_vec, a_vec)
N3 = -cross(a_vec, b_vec)
N4 = cross(b_vec, c_vec) + cross(c_vec, a_vec) + cross(a_vec, b_vec)
closure = sp.simplify(N1 + N2 + N3 + N4)
for i in range(3):
    record(f"tetra_face_closure_{i}", "tetrahedron area vectors", closure[i])

dj, dk, dl, cil, cik, cij = sp.symbols("dj dk dl cil cik cij")
norm_expansion = (
    4 * dj**2
    + 4 * dk**2
    + 4 * dl**2
    + 2 * (-4 * dj * dk * cil)
    + 2 * (-4 * dj * dl * cik)
    + 2 * (-4 * dk * dl * cij)
    - 4
    * (
        dj**2
        + dk**2
        + dl**2
        - 2 * (dj * dk * cil + dj * dl * cik + dk * dl * cij)
    )
)
record("tetra_cosine_norm_expansion", "tetrahedron cosine law", sp.expand(norm_expansion))

OA, OB, OC, kab, kbc, kca = sp.symbols("OA OB OC kab kbc kca", nonzero=True)
sOAB = OB / kab
sOBA = OA / kab
sOBC = OC / kbc
sOCB = OB / kbc
sOCA = OA / kca
sOAC = OC / kca
record(
    "tetra_sine_product",
    "tetrahedron sine law",
    sp.together(sOAB * sOBC * sOCA - sOAC * sOCB * sOBA),
)

# ---------------------------------------------------------------------------
# Write artifacts
# ---------------------------------------------------------------------------
passes = sum(item["status"] == "pass" for item in ledger)
failures = len(ledger) - passes
families: dict[str, int] = {}
for item in ledger:
    families[item["family"]] = families.get(item["family"], 0) + 1

summary = {
    "checker": "exact SymPy polynomial/rational regression",
    "sympy_version": sp.__version__,
    "checks": len(ledger),
    "passes": passes,
    "failures": failures,
    "families": families,
    "scope_note": (
        "Checks finite generators only; quotient guards, positive-root branch "
        "proofs, convergence moduli, and object-language derivability are proved "
        "or planned separately in the report."
    ),
}

(ART / "identity_ledger.json").write_text(
    json.dumps({"summary": summary, "checks": ledger}, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)

lines = [
    "Spherical trigonometry exact verification report",
    "=" * 52,
    f"SymPy version: {sp.__version__}",
    f"Checks: {len(ledger)}",
    f"Passes: {passes}",
    f"Failures: {failures}",
    "",
    "Families:",
]
for family, count in sorted(families.items()):
    lines.append(f"  {family}: {count}")
lines.extend(["", summary["scope_note"], ""])
(ART / "verification_report.txt").write_text("\n".join(lines), encoding="utf-8")

print("\n".join(lines))
