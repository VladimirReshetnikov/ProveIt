#!/usr/bin/env python3
"""Exact sparse-polynomial checks for the constructive Morley proof.

No floating point arithmetic and no CAS are used.  The script checks explicit
ideal-membership certificates for the nontrivial identities used in the paper,
plus the elementary rotation, determinant, and vector identities that connect
the human proof to its arithmetic certificate.  All coefficients are exact
fractions and all polynomial arithmetic is implemented below.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from typing import Dict, Mapping, Tuple

VARS: Tuple[str, ...] = (
    "s", "c", "rho",                    # generic angle and sqrt(3)
    "sx", "cx", "sy", "cy", "sa", "ca", # Morley bracket / a,b,g pairs
    "cu", "su",                         # 60-degree rotation
    "px", "py", "qx", "qy",            # points/vectors
    "ux", "uy", "vx", "vy", "t", "w", # ray data
    "ar", "aq", "k", "spx", "spy",    # local side formula
)
N = len(VARS)
ZERO_EXP = (0,) * N


def _f(x: int | Fraction) -> Fraction:
    return x if isinstance(x, Fraction) else Fraction(x)


@dataclass(frozen=True)
class Poly:
    terms: Mapping[Tuple[int, ...], Fraction]

    def __post_init__(self) -> None:
        clean: Dict[Tuple[int, ...], Fraction] = {}
        for e, a in self.terms.items():
            if len(e) != N:
                raise ValueError("wrong exponent-vector length")
            aa = _f(a)
            if aa:
                clean[e] = clean.get(e, Fraction(0)) + aa
        clean = {e: a for e, a in clean.items() if a}
        object.__setattr__(self, "terms", clean)

    @staticmethod
    def const(a: int | Fraction) -> "Poly":
        aa = _f(a)
        return Poly({ZERO_EXP: aa}) if aa else Poly({})

    @staticmethod
    def var(name: str) -> "Poly":
        i = VARS.index(name)
        e = [0] * N
        e[i] = 1
        return Poly({tuple(e): Fraction(1)})

    def __add__(self, other: int | Fraction | "Poly") -> "Poly":
        q = as_poly(other)
        out = dict(self.terms)
        for e, a in q.terms.items():
            out[e] = out.get(e, Fraction(0)) + a
        return Poly(out)

    __radd__ = __add__

    def __neg__(self) -> "Poly":
        return Poly({e: -a for e, a in self.terms.items()})

    def __sub__(self, other: int | Fraction | "Poly") -> "Poly":
        return self + (-as_poly(other))

    def __rsub__(self, other: int | Fraction | "Poly") -> "Poly":
        return as_poly(other) - self

    def __mul__(self, other: int | Fraction | "Poly") -> "Poly":
        q = as_poly(other)
        out: Dict[Tuple[int, ...], Fraction] = {}
        for e, a in self.terms.items():
            for f, b in q.terms.items():
                ef = tuple(x + y for x, y in zip(e, f))
                out[ef] = out.get(ef, Fraction(0)) + a * b
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n: int) -> "Poly":
        if n < 0:
            raise ValueError("negative polynomial exponent")
        base, acc, k0 = self, Poly.const(1), n
        while k0:
            if k0 & 1:
                acc = acc * base
            base = base * base
            k0 >>= 1
        return acc

    def is_zero(self) -> bool:
        return not self.terms

    def canonical(self) -> str:
        rows = []
        for e, a in sorted(self.terms.items()):
            rows.append([list(e), a.numerator, a.denominator])
        return json.dumps(rows, separators=(",", ":"), sort_keys=False)

    def digest(self) -> str:
        return sha256(self.canonical().encode()).hexdigest()

    def monomials(self) -> int:
        return len(self.terms)


def as_poly(x: int | Fraction | Poly) -> Poly:
    return x if isinstance(x, Poly) else Poly.const(x)


Pair = Tuple[Poly, Poly]
P = {name: Poly.var(name) for name in VARS}


def cadd(z: Pair, y: Pair) -> Pair:
    return z[0] + y[0], z[1] + y[1]


def csub(z: Pair, y: Pair) -> Pair:
    return z[0] - y[0], z[1] - y[1]


def cscale(a: Poly, z: Pair) -> Pair:
    return a * z[0], a * z[1]


def cmul(z: Pair, y: Pair) -> Pair:
    a, b = z
    c, d = y
    return a * c - b * d, a * d + b * c


def cconj(z: Pair) -> Pair:
    return z[0], -z[1]


def cpow(z: Pair, n: int) -> Pair:
    acc = (Poly.const(1), Poly.const(0))
    base, k0 = z, n
    while k0:
        if k0 & 1:
            acc = cmul(acc, base)
        base = cmul(base, base)
        k0 >>= 1
    return acc


def dot(z: Pair, y: Pair) -> Poly:
    return z[0] * y[0] + z[1] * y[1]


def norm_sq(z: Pair) -> Poly:
    return dot(z, z)


checks = []


def check_identity(
    name: str,
    target: Poly,
    certificate: Poly | None = None,
    note: str = "",
) -> None:
    residue = target if certificate is None else target - certificate
    if not residue.is_zero():
        raise AssertionError(f"{name}: nonzero residue: {residue.canonical()}")
    checks.append({
        "name": name,
        "status": "verified",
        "target_monomials": target.monomials(),
        "target_sha256": target.digest(),
        "certificate_monomials": 0 if certificate is None else certificate.monomials(),
        "note": note,
    })


# Shared variables and relations.
s, c, rho = P["s"], P["c"], P["rho"]
cu, su = P["cu"], P["su"]
u = (cu, su)
half_cos = 2 * cu - 1
u_unit = cu**2 + su**2 - 1
rho_def = rho - 2 * su

# 1. The shifted triple-angle identity, with all denominators cleared.
unit = c**2 + s**2 - 1
rho3 = rho**2 - 3
triple = 3 * s - 4 * s**3
triple_target = 2 * triple - (2 * s) * (s + rho * c) * (-s + rho * c)
triple_certificate = -6 * s * unit - 2 * s * c**2 * rho3
check_identity(
    "triple-angle shifted product",
    triple_target,
    triple_certificate,
    "2 sin(3x) = (2 sin x)(2 sin(x+60))(2 sin(x+120)); "
    "certificate uses c^2+s^2=1 and rho^2=3.",
)

# 2. Derive rho^2=3 from a positive 60-degree unit pair and rho=2*su.
rho_target = rho**2 - 3
rho_certificate = (
    rho_def * (rho + 2 * su)
    + 4 * u_unit
    - half_cos * (2 * cu + 1)
)
check_identity(
    "rho squared from the 60-degree pair",
    rho_target,
    rho_certificate,
    "rho=2*Im(u), 2*Re(u)=1, and norm(u)=1 imply rho^2=3.",
)

# 3-4. Algebraic sine-shift formulas for +60 and +120 degrees.
zu = cmul((c, s), u)
zu2 = cmul((c, s), cpow(u, 2))
shift60_target = 2 * zu[1] - (s + rho * c)
shift60_certificate = s * half_cos - c * rho_def
check_identity(
    "sine shift by 60 degrees",
    shift60_target,
    shift60_certificate,
    "2*Im(z*u)=s+rho*c.",
)
shift120_target = 2 * zu2[1] - (-s + rho * c)
shift120_certificate = (
    2 * c * su * half_cos
    + s * (half_cos * (2 * cu + 1) - 2 * u_unit)
    - c * rho_def
)
check_identity(
    "sine shift by 120 degrees",
    shift120_target,
    shift120_certificate,
    "2*Im(z*u^2)=-s+rho*c.",
)

# 5. The local cosine-law bracket in the Morley proof.
sx, cx, sy, cy, sa, ca = (P[x] for x in ("sx", "cx", "sy", "cy", "sa", "ca"))
ux_rel = cx**2 + sx**2 - 1
uy_rel = cy**2 + sy**2 - 1
cos_sum = cx * cy - sx * sy
sin_sum = sx * cy + cx * sy
hcos = cos_sum + ca          # cos(x+y) = -cos(alpha)
hsin = sin_sum - sa          # sin(x+y) = sin(alpha)
bracket_target = sx**2 + sy**2 - 2 * sx * sy * ca - sa**2
bracket_certificate = (
    -sx**2 * uy_rel
    - sy**2 * ux_rel
    - 2 * sx * sy * hcos
    + hsin * (sin_sum + sa)
)
check_identity(
    "Morley cosine-law bracket",
    bracket_target,
    bracket_certificate,
    "sin^2 x+sin^2 y-2 sin x sin y cos(alpha)=sin^2(alpha) "
    "when x+y=180-alpha.",
)

# 6-7. Sixty degrees cubed is a half turn.
u3 = cpow(u, 3)
u3_re_target = u3[0] + 1
u3_re_cert = (2 * cu**2 + cu - 1) * half_cos - 3 * cu * u_unit
check_identity(
    "60-degree cube: real part",
    u3_re_target,
    u3_re_cert,
    "Re(u^3)=-1.",
)
u3_im_target = u3[1]
u3_im_cert = su * (2 * cu + 1) * half_cos - su * u_unit
check_identity(
    "60-degree cube: imaginary part",
    u3_im_target,
    u3_im_cert,
    "Im(u^3)=0.",
)

# 8-13. Complex-pair multiplication laws used to turn angle addition into ring algebra.
a = (ca, sa)
b = (cx, sx)
g = (cy, sy)
assoc_l = cmul(cmul(a, b), g)
assoc_r = cmul(a, cmul(b, g))
check_identity("rotation multiplication associativity: real", assoc_l[0] - assoc_r[0])
check_identity("rotation multiplication associativity: imaginary", assoc_l[1] - assoc_r[1])
comm_l = cmul(a, b)
comm_r = cmul(b, a)
check_identity("rotation multiplication commutativity: real", comm_l[0] - comm_r[0])
check_identity("rotation multiplication commutativity: imaginary", comm_l[1] - comm_r[1])
conj_norm = cmul(cconj(a), a)
check_identity("conjugate product: real", conj_norm[0] - norm_sq(a))
check_identity("conjugate product: imaginary", conj_norm[1])

# 14-15. From a*b*g=u, norm(a)=1, and u^3=-1, derive
# (b*u)*(g*u) = -conj(a), the algebraic form of x+y=180-alpha.
h_abg = csub(cmul(cmul(a, b), g), u)
u2 = cpow(u, 2)
bg_u2 = cmul(cmul(b, g), u2)
u3_plus_one = cadd(cpow(u, 3), (Poly.const(1), Poly.const(0)))
angle_target = cadd(cmul(cmul(b, u), cmul(g, u)), cconj(a))
angle_certificate = cadd(
    cadd(
        cmul(cmul(cconj(a), u2), h_abg),
        cscale(-(norm_sq(a) - 1), bg_u2),
    ),
    cmul(cconj(a), u3_plus_one),
)
check_identity(
    "Morley angle-sum pair: real",
    angle_target[0],
    angle_certificate[0],
    "If a*b*g=u, norm(a)=1, and u^3=-1, then Re((b*u)(g*u))=-Re(a).",
)
check_identity(
    "Morley angle-sum pair: imaginary",
    angle_target[1],
    angle_certificate[1],
    "If a*b*g=u, norm(a)=1, and u^3=-1, then Im((b*u)(g*u))=Im(a).",
)

# 16. Determinant extraction from a ray-incidence equation.
px, py, qx, qy = (P[x] for x in ("px", "py", "qx", "qy"))
ux, uy, vx, vy, t, w = (P[x] for x in ("ux", "uy", "vx", "vy", "t", "w"))
inc_x = px + t * ux - qx - w * vx
inc_y = py + t * uy - qy - w * vy
det_uv = ux * vy - uy * vx
det_yx_v = (qx - px) * vy - (qy - py) * vx
det_target = t * det_uv - det_yx_v
det_certificate = inc_x * vy - inc_y * vx
check_identity(
    "determinant ray-intersection extraction",
    det_target,
    det_certificate,
    "From X+t*u=Y+w*v, taking determinant with v yields t*det(u,v)=det(Y-X,v).",
)

# 17. Squared-distance expansion for two rays with a common origin.
left_point = (px + t * ux, py + t * uy)
right_point = (px + w * vx, py + w * vy)
diff = (left_point[0] - right_point[0], left_point[1] - right_point[1])
distance_target = norm_sq(diff) - (
    t**2 * (ux**2 + uy**2)
    + w**2 * (vx**2 + vy**2)
    - 2 * t * w * (ux * vx + uy * vy)
)
check_identity("two-ray squared-distance expansion", distance_target)

# 18. The final local-side substitution.
ar, aq, k, spx, spy = (P[x] for x in ("ar", "aq", "k", "spx", "spy"))
local_after_defs = (
    (k * spy)**2
    + (k * spx)**2
    - 2 * (k * spy) * (k * spx) * ca
    - (k * sa)**2
)
renamed_bracket = spx**2 + spy**2 - 2 * spx * spy * ca - sa**2
check_identity(
    "local side reduces to renamed Morley bracket",
    local_after_defs - k**2 * renamed_bracket,
    note=(
        "After AR=k*sin(y), AQ=k*sin(x), the difference "
        "RQ^2-k^2*sin^2(alpha) is k^2 times the bracket."
    ),
)

report = {
    "title": "Constructive Morley polynomial certificate",
    "format_version": 2,
    "arithmetic": "exact sparse polynomials over Q",
    "variables": list(VARS),
    "checks": checks,
    "all_verified": True,
}

out = Path(__file__).with_name("morley_identity_certificate.json")
out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(f"verified {len(checks)} exact polynomial identities")
print(f"wrote {out.name}")
