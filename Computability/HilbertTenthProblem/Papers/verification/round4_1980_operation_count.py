#!/usr/bin/env python3
"""Reconstruction of the operation count o = 100 of Jones 1980.

Companion program of the satellite article
``Papers/1980/jones1980_theorem5_operations.tex``.

Three independent checks, all exact:

1. INDICATED-OPERATION COUNT.  Count the addition, subtraction and
   multiplication signs of a printed system, exactly as written (no reuse of
   repeated subexpressions, exponentiation not counted, a numeral coefficient
   counts as one multiplication).  Applied to the fourteen equations of
   Theorem 2.12 of Jones-Sato-Wada-Wiens 1976 (reported count 87), to the
   thirty-six equations (1.3) of Jones 1978 (reported count 243) and to the
   seventeen polynomial equations of Theorem 3 of Jones 1980 (the system
   "modified to do away with q = b^{5^60}"; reported count 100).

2. STRAIGHT-LINE CERTIFICATE.  An explicit straight-line program that
   verifies the modified Theorem 3 system (q = b^{5^60} replaced by the three
   Pell equations of Lemma 2.26 of Jones 1982) with every power built by
   repeated multiplication and every intermediate integer supplied and reused.
   Every residual is checked symbolically against the source equations.

3. CONSTANT GENERATION.  The extra operations needed if the numerals 2, 4, 5
   and the exponent 5^60 have to be generated from 1.

Run:  PYTHONUTF8=1 python round4_1980_operation_count.py
Needs Python 3.10+ and SymPy.  Writes round4_1980_operation_count.json.
"""
from __future__ import annotations
import ast, json, sys
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1980_operation_count.json"


def need(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


# --------------------------------------------------------------------------
# Part 1.  Indicated operations of the printed systems.
#
# Each equation is written as "<lhs> == <rhs>" in Python syntax; ** marks an
# exponent, * a multiplication sign or a juxtaposition, and a numeral
# coefficient is written with an explicit *.  Greek letters are spelled out.

JSWW_1976_THEOREM_2_12 = [
    "q == w*z+h+j",
    "z == (g*k+g+k)*(h+j)+h",
    "(2*k)**3*(2*k+2)*(n+1)**2+1 == f**2",
    "e == p+q+z+2*n",
    "e**3*(e+2)*(a+1)**2+1 == o**2",
    "x**2 == (a**2-1)*y**2+1",
    "u**2 == 16*(a**2-1)*r**2*y**4+1",
    "(x+c*u)**2 == ((a+u**2*(u**2-a))**2-1)*(n+4*d*y)**2+1",
    "m**2 == (a**2-1)*l**2+1",
    "l == k+i*(a-1)",
    "n+l+v == y",
    "m == p+l*(a-n-1)+b*(2*a*(n+1)-(n+1)**2-1)",
    "x == q+y*(a-p-1)+s*(2*a*(p+1)-(p+1)**2-1)",
    "p*m == z+p*l*(a-p)+t*(2*a*p-p**2-1)",
]

JONES_1978_SYSTEM_1_3 = [
    "2*n == (u+v)**2+3*v+u",
    "al == th*be+th",
    "h+h*be+h*be*v == x+rho+rho*be+rho*be*u",
    "(h+h*be+h*be*v-al)**2+x**2+ga+1 == be",
    "z == 3*n+al**3",
    "z**18*(z**6+2)*(r+1)**2+1 == psi**2",
    "t+e+e*be+e*be*s == al+q*vphi",
    "p+b+b*be+b*be*w == al+q*phi",
    "((3*(s+w)**2+9*w+3*s-2*r)**2"
    "+((1+be+r*be)**2*(1+(al-t-p)**2)*(be-t**2-p**2)-(al-t-p)**2-(g+1)*(1+be+r*be)**2)**2)"
    "*((3*(s+w)**2+9*w+3*s+2-2*r)**2"
    "+((1+be+r*be)**2*(1+(al-t*p)**2)*(be-t**2-p**2)-(al-t*p)**2-(g+1)*(1+be+r*be)**2)**2)"
    "*(3*g+2-r)*(3*n+g-r) == q*pi",
    "om == r+q+b+e+g+s+w+fp+gp+hp+ip+jp",
    "om**3*(om+2)*(si+1)**2+1 == de**2",
    "eta == si*r+si",
    "eta == b+(qp+si)*ap",
    "eta == e+(rp+si)*bp",
    "eta == g+(sp+si)*cp",
    "eta == s+(tp+si)*dp",
    "eta == w+(up+si)*ep",
    "eta**3*(eta+2)*(ze+1)**2+1 == eps**2",
    "chi == ze*(eta-r)*(qp+si)*(rp+si)*(sp+si)*(tp+si)*(up+si)",
    "y == q+(1+xi)*(eta-r)",
    "y == q*fp+(qp+si)*kp",
    "y == q*gp+(rp+si)*lp",
    "y == q*hp+(sp+si)*mp",
    "y == q*ip+(tp+si)*np",
    "y == q*jp+(up+si)*pp",
    "(mu**2-1)*ka**2+1 == nu**2",
    "(mu**2*chi**2-1)*la**2+1 == ups**2",
    "5*(c-ka*la*y)**2+io == ka**2*la**2",
    "mu == 9*eta*chi*y",
    "ka == eta-z+1+k*(mu-1)",
    "la == z+1+l*(mu*chi-1)",
    "a == mu*chi+mu",
    "c == m+eta+1",
    "d**2 == (a**2-1)*c**2+1",
    "f**2 == 4*(a**2-1)*i**2*c**4+1",
    "(d+tau*f)**2 == ((a+f**2*(f**2-a))**2-1)*(eta+1+2*j*c)**2+1",
]

# Theorem 3 of Jones 1980 (= Theorem 3 of Jones 1982) without q = b^{5^60}.
JONES_1980_THEOREM_3_POLYNOMIAL = [
    "e*l*g**2+al == (b-x*y)*q**2",
    "la+q**4 == 1+la*b**5",
    "th+2*z == b**5",
    "l == u+t*th",
    "e == y+m*th",
    "n == q**16",
    "r == (g+e*q**3+l*q**5+(2*(e-z*la)*(1+x*b**5+g)**4+la*b**5+la*b**5*q**4)*q**7)*(n**2-n)"
    "+(q**3-b*l+l+th*la*q**3+(b**5-2)*q**8)*(n**2-1)",
    "p == 2*w*s**2*r**2*n**6",
    "p**2*k**2-k**2+1 == tau**2",
    "4*(c-k*s*n**2)**2+eta == k**2",
    "k == r+1+h*p-h",
    "a == (w*n**2+1)*r*s*n**2",
    "c == 2*r+1+phi",
    "d == b*w+c*a-2*c+4*a*ga-5*ga",
    "d**2 == (a**2-1)*c**2+1",
    "f**2 == (a**2-1)*i**2*c**4+1",
    "(d+o*f)**2 == ((a+f**2*(d**2-a))**2-1)*(2*r+1+j*c)**2+1",
]


def indicated_operations(expr: str) -> dict:
    """Count the +, - and * signs of one side of an equation as written."""
    hist = {"+": 0, "-": 0, "*": 0, "pow": 0}

    def walk(node):
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                hist["pow"] += 1
                walk(node.left)          # the exponent is a numeral
                return
            hist[{ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}[type(node.op)]] += 1
            walk(node.left); walk(node.right)
        elif isinstance(node, (ast.Name, ast.Constant)):
            return
        else:
            raise ValueError(ast.dump(node))

    walk(ast.parse(expr.strip(), mode="eval").body)
    return hist


def count_system(system: list[str]) -> dict:
    total = {"+": 0, "-": 0, "*": 0, "pow": 0}
    per_equation = []
    for eq in system:
        lhs, rhs = eq.split("==")
        h = {k: 0 for k in total}
        for side in (lhs, rhs):
            for k, v in indicated_operations(side).items():
                h[k] += v
        per_equation.append(h["+"] + h["-"] + h["*"])
        for k in total:
            total[k] += h[k]
    total["indicated"] = total["+"] + total["-"] + total["*"]
    total["per_equation"] = per_equation
    return total


# --------------------------------------------------------------------------
# Part 2.  Straight-line certificate for the modified Theorem 3 system.
#
# Names: parameters x, z, u, y; the 28 unknowns of Theorem 3 (al = alpha,
# ga = gamma, eta, th = theta, la = lambda, tau, phi); the four new unknowns of
# the Lemma 2.26 replacement: ka (= C_1 of the lemma), mu (= D_1), rho (the
# congruence multiplier) and Delta.  K is the literal 5^60.
K = 5 ** 60

SCHEDULE = [
    # powers of q and b
    ("q2", "*", "q", "q"), ("q3", "*", "q2", "q"), ("q4", "*", "q2", "q2"),
    ("q8", "*", "q4", "q4"), ("q16", "*", "q8", "q8"),
    ("b2", "*", "b", "b"), ("b4", "*", "b2", "b2"), ("b5", "*", "b4", "b"),
    # E1  e l g^2 + alpha = (b - x y) q^2
    ("g2", "*", "g", "g"), ("el", "*", "e", "l"), ("elg2", "*", "el", "g2"),
    ("L1", "+", "elg2", "al"), ("xy", "*", "x", "y"), ("bxy", "-", "b", "xy"),
    ("R1", "*", "bxy", "q2"),
    # E2  lambda + q^4 = 1 + lambda b^5
    ("L2", "+", "la", "q4"), ("Lam", "*", "la", "b5"), ("R2", "+", "Lam", 1),
    # E3  theta + 2 z = b^5
    ("z2", "*", 2, "z"), ("L3", "+", "th", "z2"),
    # E4  l = u + t theta
    ("tth", "*", "t", "th"), ("R4", "+", "u", "tth"),
    # E5  e = y + m theta
    ("mth", "*", "m", "th"), ("R5", "+", "y", "mth"),
    # E6  n = q^16 : no further operation
    # E7  r = S (n^2 - n) + (T + 1)(n^2 - 1), with
    #     S = g + q^3 ( e + l q^2 + q^4 ( 2 (e - z lambda) C^4 + Lam (1 + q^4) ) ),
    #     C = 1 + x b^5 + g,  T + 1 = q^3 - b l + l + theta lambda q^3 + (b^5 - 2) q^8
    ("lq2", "*", "l", "q2"), ("S2", "+", "e", "lq2"),
    ("zl", "*", "z", "la"), ("ezl", "-", "e", "zl"), ("t2", "*", 2, "ezl"),
    ("xb5", "*", "x", "b5"), ("c0", "+", "xb5", 1), ("C", "+", "c0", "g"),
    ("C2", "*", "C", "C"), ("C4", "*", "C2", "C2"), ("P1", "*", "t2", "C4"),
    ("q4p1", "+", "q4", 1), ("P2", "*", "Lam", "q4p1"), ("S3", "+", "P1", "P2"),
    ("S3q4", "*", "S3", "q4"), ("Sin", "+", "S2", "S3q4"), ("Sq3", "*", "Sin", "q3"),
    ("S", "+", "g", "Sq3"),
    ("n2", "*", "n", "n"), ("n2n", "-", "n2", "n"), ("SA", "*", "S", "n2n"),
    ("bl", "*", "b", "l"), ("q3bl", "-", "q3", "bl"), ("T1", "+", "q3bl", "l"),
    ("thl", "*", "th", "la"), ("thlq3", "*", "thl", "q3"), ("T2", "+", "T1", "thlq3"),
    ("b5m2", "-", "b5", 2), ("b5m2q8", "*", "b5m2", "q8"), ("T", "+", "T2", "b5m2q8"),
    ("n2m1", "-", "n2", 1), ("TB", "*", "T", "n2m1"), ("R7", "+", "SA", "TB"),
    # E12  a = (w n^2 + 1) r s n^2 ; w n^2, s n^2 and r s n^2 are shared with E8, E10
    ("wn2", "*", "w", "n2"), ("wn2p1", "+", "wn2", 1),
    ("sn2", "*", "s", "n2"), ("rsn2", "*", "r", "sn2"), ("R12", "*", "wn2p1", "rsn2"),
    # E8  p = 2 w s^2 r^2 n^6 = 2 (w n^2) (r s n^2)^2
    ("rsn2sq", "*", "rsn2", "rsn2"), ("wsq", "*", "wn2", "rsn2sq"), ("R8", "*", 2, "wsq"),
    # E9  p^2 k^2 - k^2 + 1 = tau^2, computed as (p^2 - 1) k^2 + 1
    ("p2", "*", "p", "p"), ("p2m1", "-", "p2", 1), ("k2", "*", "k", "k"),
    ("P9", "*", "p2m1", "k2"), ("L9", "+", "P9", 1), ("R9", "*", "tau", "tau"),
    # E10 4 (c - k s n^2)^2 + eta = k^2
    ("ksn2", "*", "k", "sn2"), ("cm", "-", "c", "ksn2"),
    ("cm2", "*", "cm", "cm"), ("f4", "*", 4, "cm2"), ("L10", "+", "f4", "eta"),
    # E11 k = r + 1 + h p - h = r + 1 + h (p - 1)
    ("r1", "+", "r", 1), ("pm1", "-", "p", 1), ("hpm1", "*", "h", "pm1"),
    ("R11", "+", "r1", "hpm1"),
    # E13 c = 2 r + 1 + kappa + phi   (kappa = C_1 of Lemma 2.26)
    ("tr1", "+", "r1", "r"), ("tk", "+", "tr1", "ka"), ("R13", "+", "tk", "phi"),
    # E14 d = b w + c a - 2 c + 4 a gamma - 5 gamma = b w + c (a - 2) + gamma (4 a - 5)
    ("bw", "*", "b", "w"), ("am2", "-", "a", 2), ("cam2", "*", "c", "am2"),
    ("D1", "+", "bw", "cam2"), ("a4", "*", 4, "a"), ("a4m5", "-", "a4", 5),
    ("gam", "*", "ga", "a4m5"), ("R14", "+", "D1", "gam"),
    # E15 d^2 = (a^2 - 1) c^2 + 1
    ("a2", "*", "a", "a"), ("A", "-", "a2", 1), ("c2", "*", "c", "c"),
    ("Ac2", "*", "A", "c2"), ("R15", "+", "Ac2", 1), ("L15", "*", "d", "d"),
    # E16 f^2 = (a^2 - 1) i^2 c^4 + 1 = (a^2 - 1)(i c^2)^2 + 1
    ("ic2", "*", "i", "c2"), ("ic22", "*", "ic2", "ic2"), ("AE", "*", "A", "ic22"),
    ("R16", "+", "AE", 1), ("L16", "*", "f", "f"),
    # E17 (d + o f)^2 = ((a + f^2 (d^2 - a))^2 - 1)(2 r + 1 + j c)^2 + 1
    ("of", "*", "o", "f"), ("dof", "+", "d", "of"), ("L17", "*", "dof", "dof"),
    ("d2ma", "-", "L15", "a"), ("f2d", "*", "L16", "d2ma"), ("G", "+", "a", "f2d"),
    ("G2", "*", "G", "G"), ("G2m1", "-", "G2", 1), ("jc", "*", "j", "c"),
    ("H", "+", "tr1", "jc"), ("H2", "*", "H", "H"), ("P17", "*", "G2m1", "H2"),
    ("R17", "+", "P17", 1),
    # E18 (C1') mu = q + kappa (a - b) + rho (2 a b - b^2 - 1),
    #     with 2 a b - b^2 - 1 = (a^2 - 1) - (a - b)^2
    ("amb", "-", "a", "b"), ("kamb", "*", "ka", "amb"), ("qk", "+", "q", "kamb"),
    ("amb2", "*", "amb", "amb"), ("Mod", "-", "A", "amb2"), ("rM", "*", "rho", "Mod"),
    ("R18", "+", "qk", "rM"),
    # E19 (C2') (a^2 - 1) kappa^2 + 1 = mu^2
    ("ka2", "*", "ka", "ka"), ("Aka2", "*", "A", "ka2"), ("R19", "+", "Aka2", 1),
    ("L19", "*", "mu", "mu"),
    # E20 (C3') kappa = 5^60 + Delta (a - 1)
    ("am1", "-", "a", 1), ("Dam1", "*", "Delta", "am1"), ("R20", "+", "Dam1", K),
]

# Final equality tests (not arithmetic operations): pairs (left name, right name).
EQUALITIES = [
    ("L1", "R1"), ("L2", "R2"), ("L3", "b5"), ("l", "R4"), ("e", "R5"), ("n", "q16"),
    ("r", "R7"), ("p", "R8"), ("L9", "R9"), ("L10", "k2"), ("k", "R11"), ("a", "R12"),
    ("c", "R13"), ("d", "R14"), ("L15", "R15"), ("L16", "R16"), ("L17", "R17"),
    ("mu", "R18"), ("L19", "R19"), ("ka", "R20"),
]

# The modified system, as polynomials (left - right), for the symbolic check.
NAMES = ("x z u y a b c d e f g h i j k l m n o p q r s t w "
         "al ga eta th la tau phi ka mu rho Delta").split()
SYM = {nm: sp.Symbol(nm) for nm in NAMES}
S_ = SYM


def source_residuals() -> list[sp.Expr]:
    x, z, u, y = S_["x"], S_["z"], S_["u"], S_["y"]
    a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, w = (
        S_[v] for v in "a b c d e f g h i j k l m n o p q r s t w".split())
    al, ga, eta, th, la, tau, phi = (S_[v] for v in "al ga eta th la tau phi".split())
    ka, mu, rho, Delta = S_["ka"], S_["mu"], S_["rho"], S_["Delta"]
    return [
        e*l*g**2 + al - (b - x*y)*q**2,
        la + q**4 - (1 + la*b**5),
        th + 2*z - b**5,
        l - (u + t*th),
        e - (y + m*th),
        n - q**16,
        r - ((g + e*q**3 + l*q**5 + (2*(e - z*la)*(1 + x*b**5 + g)**4 + la*b**5
               + la*b**5*q**4)*q**7)*(n**2 - n)
             + (q**3 - b*l + l + th*la*q**3 + (b**5 - 2)*q**8)*(n**2 - 1)),
        p - 2*w*s**2*r**2*n**6,
        p**2*k**2 - k**2 + 1 - tau**2,
        4*(c - k*s*n**2)**2 + eta - k**2,
        k - (r + 1 + h*p - h),
        a - (w*n**2 + 1)*r*s*n**2,
        c - (2*r + 1 + ka + phi),
        d - (b*w + c*a - 2*c + 4*a*ga - 5*ga),
        d**2 - ((a**2 - 1)*c**2 + 1),
        f**2 - ((a**2 - 1)*i**2*c**4 + 1),
        (d + o*f)**2 - (((a + f**2*(d**2 - a))**2 - 1)*(2*r + 1 + j*c)**2 + 1),
        mu - (q + ka*(a - b) + rho*(2*a*b - b**2 - 1)),
        (a**2 - 1)*ka**2 + 1 - mu**2,
        ka - (K + Delta*(a - 1)),
    ]


def run_schedule(schedule, env: dict) -> dict:
    hist = {"+": 0, "-": 0, "*": 0}
    for target, op, left, right in schedule:
        need(target not in env, f"redefined name {target}")
        lv = sp.Integer(left) if isinstance(left, int) else env[left]
        rv = sp.Integer(right) if isinstance(right, int) else env[right]
        env[target] = {"+": lv + rv, "-": lv - rv, "*": lv * rv}[op]
        hist[op] += 1
    return hist


def shared_product_schedule() -> list:
    """Distribute a=(U+1)M and reuse UM in p=2(UM)M: save one product."""
    first = next(i for i, row in enumerate(SCHEDULE) if row[0] == "wn2")
    last = next(i for i, row in enumerate(SCHEDULE) if row[0] == "R8") + 1
    return SCHEDULE[:first] + [
        ("wn2", "*", "w", "n2"), ("sn2", "*", "s", "n2"),
        ("rsn2", "*", "r", "sn2"), ("UM", "*", "wn2", "rsn2"),
        ("R12", "+", "UM", "rsn2"), ("UMM", "*", "UM", "rsn2"),
        ("R8", "*", 2, "UMM"),
    ] + SCHEDULE[last:]


def verify_certificate(schedule=None) -> dict:
    env = dict(SYM)
    schedule = SCHEDULE if schedule is None else schedule
    hist = run_schedule(schedule, env)
    residuals = source_residuals()
    need(len(EQUALITIES) == len(residuals) == 20, "twenty equations expected")
    signs = []
    for (ln, rn), res in zip(EQUALITIES, residuals):
        diff = sp.expand(env[ln] - env[rn])
        if sp.expand(diff - res) == 0:
            signs.append(1)
        elif sp.expand(diff + res) == 0:
            signs.append(-1)
        else:
            raise AssertionError(f"certificate residual {ln} - {rn} differs from the source")
    used = {nm for _, _, l, r in schedule for nm in (l, r) if isinstance(nm, str)}
    used |= {nm for pair in EQUALITIES for nm in pair}
    need(set(NAMES) <= used, "some variable of the system is never used")
    total = sum(hist.values())
    # subtraction t = a - b is certified by the one addition t + b = a
    return {
        "operations": total,
        "straight_line_histogram": hist,
        "additions_and_multiplications_only": {
            "additions": hist["+"] + hist["-"], "multiplications": hist["*"]},
        "equality_tests": len(EQUALITIES),
        "residual_signs": signs,
        "unknowns": 32, "parameters": 4, "equations": 20,
    }


# --------------------------------------------------------------------------
# Part 3.  Generating the numerals from 1.
CONSTANT_SCHEDULE = [
    ("two", "+", 1, 1), ("four", "+", "two", "two"), ("five", "+", "four", 1),
    ("f2", "*", "five", "five"), ("f3", "*", "f2", "five"), ("f6", "*", "f3", "f3"),
    ("f12", "*", "f6", "f6"), ("f15", "*", "f12", "f3"), ("f30", "*", "f15", "f15"),
    ("f60", "*", "f30", "f30"),
]


def verify_constants() -> dict:
    env = {}
    hist = run_schedule(CONSTANT_SCHEDULE, env)
    need(env["two"] == 2 and env["four"] == 4 and env["five"] == 5, "small numerals")
    need(env["f60"] == 5 ** 60, "5^60")
    # exponent literal: 3 * 5^60 < 2^(5^59) is needed for Lemma 2.26 with B = b
    import math
    need(math.log2(3 * 5 ** 60) < 5 ** 59, "3*5^60 < 2^(5^59)")
    return {"operations": sum(hist.values()), "histogram": hist,
            "note": "2 = 1+1, 4 = 2+2, 5 = 4+1, then the addition chain "
                    "1,2,3,6,12,15,30,60 for 5^60"}


def main() -> int:
    results = {"status": "PASS"}
    counts = {
        "JSWW_1976_Theorem_2.12": (count_system(JSWW_1976_THEOREM_2_12), 87),
        "Jones_1978_system_1.3": (count_system(JONES_1978_SYSTEM_1_3), 243),
        "Jones_1980_Theorem_3_without_exponential": (
            count_system(JONES_1980_THEOREM_3_POLYNOMIAL), 100),
    }
    results["indicated_operations"] = {}
    for name, (c, reported) in counts.items():
        c = dict(c); c["reported_by_authors"] = reported
        results["indicated_operations"][name] = c
        print(f"{name}: indicated operations {c['indicated']} "
              f"(+{c['+']}, -{c['-']}, *{c['*']}; {c['pow']} exponentiations not counted); "
              f"reported {reported}")
    need(counts["JSWW_1976_Theorem_2.12"][0]["indicated"] == 87, "1976 count")
    need(counts["Jones_1980_Theorem_3_without_exponential"][0]["indicated"] == 100, "1980 count")
    need(counts["Jones_1978_system_1.3"][0]["indicated"] == 241, "1978 count")

    cert = verify_certificate()
    results["straight_line_certificate"] = cert
    print(f"straight-line certificate: {cert['operations']} operations "
          f"{cert['straight_line_histogram']}, {cert['equality_tests']} equality tests")

    shared = verify_certificate(shared_product_schedule())
    need(shared["operations"] == 128, "shared-product certificate count")
    results["shared_product_certificate"] = shared
    print(f"shared-product certificate: {shared['operations']} operations "
          f"{shared['straight_line_histogram']}, {shared['equality_tests']} equality tests")

    const = verify_constants()
    results["numerals_from_one"] = const
    results["straight_line_certificate_with_numerals_from_one"] = (
        cert["operations"] + const["operations"])
    print(f"numerals from 1: {const['operations']} more operations; total "
          f"{results['straight_line_certificate_with_numerals_from_one']}")

    OUT.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("wrote", OUT.name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
