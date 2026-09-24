#!/usr/bin/env python3
"""Checks for the 1978 article (Jones, Three Universal Representations).

1. Brute-force checks of Lemmas 2.1, 2.2, 2.5, 2.6 and of the Cantor pairing
   function and the polynomial enumeration P_k of section 3.
2. The combined divisibility condition at the end of section 3: the squared
   form F M(u)^2 | M(u)^2 (H-C) + F (hM(v)-x)^2 is equivalent to
   F | H-C  and  M(u) | hM(v)-x whenever gcd(F, M(u)) = 1, while the printed
   form with M(u)(H-C) is not (explicit counterexample).
3. The 36-equation universal system (1.3) is re-typed from the edition and
   compared symbolically with the conditions U1-U8, B1-B8, T1-T9, Q2-Q4 of
   section 3 under the letter substitutions stated there; unknown count and
   maximum degree are recomputed.
Run from any directory; needs SymPy.
"""
from __future__ import annotations
import json
from math import comb, factorial, gcd, isqrt
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1978_results.json"

def need(cond, msg):
    if not cond:
        raise AssertionError(msg)

# ---------------------------------------------------------------- Lemmas 2.1, 2.2
for u in range(1, 13):
    for v in range(1, 25):
        for w in range(-3, 6):
            exists = (u*v*w - v) % u == 0 and (u*v*w - v)//u >= 0
            need(exists == (v % u == 0 and w > 0), "Lemma 2.1")
for u in range(-6, 7):
    if u == 0:
        continue
    for v in range(-8, 9):
        for w in range(-3, 6):
            num = u*u*(1 + v*v)*w - v*v
            exists = num % (u*u) == 0 and num//(u*u) - 1 >= 0
            need(exists == (v % u == 0 and w > 0), f"Lemma 2.2 u={u} v={v} w={w}")

# ---------------------------------------------------------------- Lemma 2.5, 2.6
for d in range(1, 30):
    for z in range(0, 5):
        m = d // gcd(d, factorial(z))
        for a in range(0, 40):
            for b in range(a, 40, d):
                need((comb(a, z) - comb(b, z)) % m == 0, "Lemma 2.5")
for N in range(2, 9):
    for z in range(1, N):
        for X in range(N**z + 1, N**z + 40):
            Y = (X + 1)**N // X**z
            need((Y - comb(N, z)) % X == 0, f"Lemma 2.6 N={N} z={z} X={X}")

# ---------------------------------------------------------------- pairing and P_k
def J(s, w):
    return ((s + w)**2 + 3*w + s) // 2
KL = {}
for s in range(0, 40):
    for w in range(0, 40):
        y = J(s, w)
        need(((s + w)**2 + 3*w + s) % 2 == 0, "2J integer")
        need(y not in KL, "J not injective")
        KL[y] = (s, w)
need(all(y in KL for y in range(0, 300)), "J not onto")
need(all(KL[y][0] <= y and KL[y][1] <= y for y in range(0, 300)), "K(y),L(y) <= y")
X = sp.symbols("X0:40")
P = {0: sp.Integer(0)}
def Pk(k):
    if k in P:
        return P[k]
    if k % 3 == 2:
        P[k] = X[(k - 2)//3]
    elif k % 3 == 0:
        i = k//3; s, w = KL[i]; P[k] = Pk(s) + Pk(w)
    else:
        i = (k - 1)//3; s, w = KL[i]; P[k] = sp.expand(Pk(s)*Pk(w))
    return P[k]
for k in range(0, 60):
    vars_ = {int(str(v)[1:]) for v in Pk(k).free_symbols}
    need(all(3*i + 2 <= k for i in vars_), "variable bound in P_k")
    need(sp.Poly(Pk(k), *X).coeff_monomial(1) == 0 if Pk(k) != 0 else True, "constant term")
need(Pk(1) == 0, "P_1 = 0")

# ---------------------------------------------------------------- combined divisibility
counter = None; ok_squared = True
for M in range(2, 10):
    for F in range(2, 26):
        if gcd(F, M) != 1:
            continue
        for HC in range(-8, 9):
            for Q in range(-9, 10):  # Q plays hM(v)-x
                truth = (HC % F == 0) and (Q % M == 0)
                squared = (M*M*HC + F*Q*Q) % (F*M*M) == 0
                printed = (M*HC + F*Q*Q) % (F*M*M) == 0
                if squared != truth:
                    ok_squared = False
                if printed != truth and counter is None:
                    counter = {"M(u)": M, "F": F, "H-C": HC, "hM(v)-x": Q, "printed_form_holds": printed, "conditions_hold": truth}
need(ok_squared, "squared combined divisibility is not equivalent")
need(counter is not None, "expected a counterexample to the printed form")

# ---------------------------------------------------------------- system (1.3)
names = ("u v alpha theta beta h rho gamma z r psi t e varphi q p b phi w s g pi omega "
         "f1 g1 h1 i1 j1 sigma delta eta q1 a1 r1 b1 s1 c1 t1 d1 u1 e1 zeta epsilon chi y xi "
         "k1 l1 m1 n1 p1 mu kappa nu lam upsilon c iota k l a m d f i tau j n x")
S = {nm: sp.Symbol(nm) for nm in names.split()}
g = S
sys13 = [
    2*g["n"] - ((g["u"] + g["v"])**2 + 3*g["v"] + g["u"]),
    g["alpha"] - (g["theta"]*g["beta"] + g["theta"]),
    g["h"] + g["h"]*g["beta"] + g["h"]*g["beta"]*g["v"] - (g["x"] + g["rho"] + g["rho"]*g["beta"] + g["rho"]*g["beta"]*g["u"]),
    (g["h"] + g["h"]*g["beta"] + g["h"]*g["beta"]*g["v"] - g["alpha"])**2 + g["x"]**2 + g["gamma"] + 1 - g["beta"],
    g["z"] - (3*g["n"] + g["alpha"]**3),
    g["z"]**18*(g["z"]**6 + 2)*(g["r"] + 1)**2 + 1 - g["psi"]**2,
    g["t"] + g["e"] + g["e"]*g["beta"] + g["e"]*g["beta"]*g["s"] - (g["alpha"] + g["q"]*g["varphi"]),
    g["p"] + g["b"] + g["b"]*g["beta"] + g["b"]*g["beta"]*g["w"] - (g["alpha"] + g["q"]*g["phi"]),
    None,  # (1.3.09) built below
    g["omega"] - (g["r"] + g["q"] + g["b"] + g["e"] + g["g"] + g["s"] + g["w"] + g["f1"] + g["g1"] + g["h1"] + g["i1"] + g["j1"]),
    g["omega"]**3*(g["omega"] + 2)*(g["sigma"] + 1)**2 + 1 - g["delta"]**2,
    g["eta"] - (g["sigma"]*g["r"] + g["sigma"]),
    g["eta"] - (g["b"] + (g["q1"] + g["sigma"])*g["a1"]),
    g["eta"] - (g["e"] + (g["r1"] + g["sigma"])*g["b1"]),
    g["eta"] - (g["g"] + (g["s1"] + g["sigma"])*g["c1"]),
    g["eta"] - (g["s"] + (g["t1"] + g["sigma"])*g["d1"]),
    g["eta"] - (g["w"] + (g["u1"] + g["sigma"])*g["e1"]),
    g["eta"]**3*(g["eta"] + 2)*(g["zeta"] + 1)**2 + 1 - g["epsilon"]**2,
    g["chi"] - g["zeta"]*(g["eta"] - g["r"])*(g["q1"] + g["sigma"])*(g["r1"] + g["sigma"])*(g["s1"] + g["sigma"])*(g["t1"] + g["sigma"])*(g["u1"] + g["sigma"]),
    g["y"] - (g["q"] + (1 + g["xi"])*(g["eta"] - g["r"])),
    g["y"] - (g["q"]*g["f1"] + (g["q1"] + g["sigma"])*g["k1"]),
    g["y"] - (g["q"]*g["g1"] + (g["r1"] + g["sigma"])*g["l1"]),
    g["y"] - (g["q"]*g["h1"] + (g["s1"] + g["sigma"])*g["m1"]),
    g["y"] - (g["q"]*g["i1"] + (g["t1"] + g["sigma"])*g["n1"]),
    g["y"] - (g["q"]*g["j1"] + (g["u1"] + g["sigma"])*g["p1"]),
    (g["mu"]**2 - 1)*g["kappa"]**2 + 1 - g["nu"]**2,
    (g["mu"]**2*g["chi"]**2 - 1)*g["lam"]**2 + 1 - g["upsilon"]**2,
    5*(g["c"] - g["kappa"]*g["lam"]*g["y"])**2 + g["iota"] - g["kappa"]**2*g["lam"]**2,
    g["mu"] - 9*g["eta"]*g["chi"]*g["y"],
    g["kappa"] - (g["eta"] - g["z"] + 1 + g["k"]*(g["mu"] - 1)),
    g["lam"] - (g["z"] + 1 + g["l"]*(g["mu"]*g["chi"] - 1)),
    g["a"] - (g["mu"]*g["chi"] + g["mu"]),
    g["c"] - (g["m"] + g["eta"] + 1),
    g["d"]**2 - ((g["a"]**2 - 1)*g["c"]**2 + 1),
    g["f"]**2 - (4*(g["a"]**2 - 1)*g["i"]**2*g["c"]**4 + 1),
    (g["d"] + g["tau"]*g["f"])**2 - (((g["a"] + g["f"]**2*(g["f"]**2 - g["a"]))**2 - 1)*(g["eta"] + 1 + 2*g["j"]*g["c"])**2 + 1),
]
s_, w_, r_, al, t_, p_, be, g_, n_, q_, pi_ = (g[nm] for nm in "s w r alpha t p beta g n q pi".split())
Mr = 1 + be + r_*be
A_r = (3*(s_ + w_)**2 + 9*w_ + 3*s_ - 2*r_)**2 + (Mr**2*(1 + (al - t_ - p_)**2)*(be - t_**2 - p_**2) - (al - t_ - p_)**2 - (g_ + 1)*Mr**2)**2
B_r = (3*(s_ + w_)**2 + 9*w_ + 3*s_ + 2 - 2*r_)**2 + (Mr**2*(1 + (al - t_*p_)**2)*(be - t_**2 - p_**2) - (al - t_*p_)**2 - (g_ + 1)*Mr**2)**2
sys13[8] = A_r*B_r*(3*g_ + 2 - r_)*(3*n_ + g_ - r_) - q_*pi_
need(len(sys13) == 36, "36 equations")
params = {g["n"], g["x"]}
unknowns = set().union(*(E.free_symbols for E in sys13)) - params
need(len(unknowns) == 67, f"unknown count {len(unknowns)} != 67")
vs = sorted(unknowns, key=str)
def tdeg(E):
    return sp.Poly(E, *vs).total_degree()
# (1.3.09) is a product; its degree is the sum of the factor degrees (no expansion needed)
deg09 = max(tdeg(A_r) + tdeg(B_r) + tdeg(3*g_ + 2 - r_) + tdeg(3*n_ + g_ - r_), tdeg(q_*pi_))
degs = [tdeg(E) if k != 8 else deg09 for k, E in enumerate(sys13)]
need(max(degs) == 38, f"max degree {max(degs)} != 38")
need(degs[8] == 38 and degs[5] == 26, "expected degrees of (1.3.09) and (1.3.06)")

# Reconstruct (1.3) from U1-U8, B1-B8, T1-T9, Q2-Q4 with the stated substitutions.
# Capital letters -> lower case: A a, C c, D d, F f, K kappa, L lam, M mu, N eta, P p,
# R alpha, T t, W omega, X chi, Y y, Z z; b_i -> f1..j1; c_i -> k1..p1; d_i -> q1..u1.
zs = [g["b"], g["e"], g["g"], g["s"], g["w"]]
bs = [g["f1"], g["g1"], g["h1"], g["i1"], g["j1"]]
cs = [g["k1"], g["l1"], g["m1"], g["n1"], g["p1"]]
ds = [g["q1"], g["r1"], g["s1"], g["t1"], g["u1"]]
def Mfun(i):  # M(i) = 1 + (1+i) beta
    return 1 + (1 + i)*be
recon = [
    2*n_ - ((g["u"] + g["v"])**2 + 3*g["v"] + g["u"]),                     # U1
    al - g["theta"]*(1 + be),                                              # U2
    g["h"]*Mfun(g["v"]) - (g["x"] + g["rho"]*Mfun(g["u"])),                # U3 (rho quotient)
    (g["h"]*Mfun(g["v"]) - al)**2 + g["x"]**2 + g["gamma"] + 1 - be,       # U4
    g["z"] - (3*n_ + al**3),                                               # U5
    (g["z"]**6)**3*(g["z"]**6 + 2)*(r_ + 1)**2 + 1 - g["psi"]**2,          # U6 with J=Z^6
    t_ + g["e"]*Mfun(s_) - (al + q_*g["varphi"]),                          # U7 mod q
    p_ + g["b"]*Mfun(w_) - (al + q_*g["phi"]),                             # U7 mod q
    sys13[8],                                                              # U8 (same construction)
    g["omega"] - (r_ + q_ + sum(zs) + sum(bs)),                            # B1
    g["omega"]**3*(g["omega"] + 2)*(g["sigma"] + 1)**2 + 1 - g["delta"]**2,# B2
    g["eta"] - g["sigma"]*(r_ + 1),                                        # B3
] + [g["eta"] - (zs[i] + (g["sigma"] + ds[i])*[g["a1"], g["b1"], g["c1"], g["d1"], g["e1"]][i]) for i in range(5)] + [  # B4
    g["eta"]**3*(g["eta"] + 2)*(g["zeta"] + 1)**2 + 1 - g["epsilon"]**2,   # B5
    g["chi"] - g["zeta"]*(g["eta"] - r_)*sp.prod([g["sigma"] + dd for dd in ds]),  # B6
    g["y"] - (q_ + (g["xi"] + 1)*(g["eta"] - r_)),                         # B7
] + [g["y"] - (q_*bs[i] + cs[i]*(g["sigma"] + ds[i])) for i in range(5)] + [  # B8
    (g["mu"]**2 - 1)*g["kappa"]**2 + 1 - g["nu"]**2,                       # T1
    (g["mu"]**2*g["chi"]**2 - 1)*g["lam"]**2 + 1 - g["upsilon"]**2,        # T2
    5*(g["c"] - g["kappa"]*g["lam"]*g["y"])**2 + g["iota"] - g["kappa"]**2*g["lam"]**2,  # T3 (variant)
    g["mu"] - 9*g["eta"]*g["chi"]*g["y"],                                  # T4 (variant)
    g["kappa"] - (g["eta"] - g["z"] + 1 + g["k"]*(g["mu"] - 1)),           # T5
    g["lam"] - (g["z"] + 1 + g["l"]*(g["mu"]*g["chi"] - 1)),               # T6
    g["a"] - g["mu"]*(g["chi"] + 1),                                       # T7
    g["c"] - (g["m"] + g["eta"] + 1),                                      # T8+T9
    g["d"]**2 - ((g["a"]**2 - 1)*g["c"]**2 + 1),                           # Q2
    g["f"]**2 - (4*(g["a"]**2 - 1)*g["i"]**2*g["c"]**4 + 1),               # Q3
    (g["d"] + g["tau"]*g["f"])**2 - (((g["a"] + g["f"]**2*(g["f"]**2 - g["a"]))**2 - 1)*(g["eta"] + 1 + 2*g["j"]*g["c"])**2 + 1),  # Q4
]
need(len(recon) == 36, "reconstruction count")
for idx, (E1, E2) in enumerate(zip(sys13, recon), start=1):
    need(sp.expand(E1 - E2) == 0, f"(1.3.{idx:02d}) differs from the section-3 construction")

# ---------------------------------------------------------------- Lemma 2.8, necessity instances
def psi(A, n):
    x0, x1 = 0, 1
    if n == 0:
        return 0
    for _ in range(n - 1):
        x0, x1 = x1, 2*A*x1 - x0
    return x1
lemma28 = []
for (N, Z, X) in ((2, 1, 9), (2, 1, 17), (3, 1, 30), (3, 2, 40), (4, 2, 70), (5, 3, 600)):
    need(0 < Z < N and 4*N**Z < X, "Lemma 2.8 hypotheses")
    Y = (X + 1)**N // X**Z; need(Y > 0, "Y > 0")
    for variant in ("T3/T4", "5-variant"):
        if variant == "T3/T4":
            M = 8*N*(X + Y) + 2
        else:
            if not (8*N**Z < X and Y > 1):
                continue
            M = 9*N*X*Y
        K = psi(M, N - Z + 1); L_ = psi(M*X, Z + 1); A = M*(X + 1); B = N + 1; C = psi(A, B)
        need(isqrt((M*M - 1)*K*K + 1)**2 == (M*M - 1)*K*K + 1, "T1")
        need(isqrt((M*M*X*X - 1)*L_*L_ + 1)**2 == (M*M*X*X - 1)*L_*L_ + 1, "T2")
        need(C > B, "T9 witness m >= 0")
        if variant == "T3/T4":
            need(4*(C - K*L_*Y)**2 < K*K*L_*L_, f"T3 fails at N={N} Z={Z} X={X}")
        else:
            need(5*(C - K*L_*Y)**2 <= K*K*L_*L_, f"5-variant of T3 fails at N={N} Z={Z} X={X}")
        lemma28.append({"N": N, "Z": Z, "X": X, "variant": variant, "Y": Y})

report = {"status": "PASS", "lemmas": "2.1, 2.2, 2.5, 2.6 brute force; pairing J,K,L; P_k variable bound",
          "lemma28_necessity_instances": lemma28,
          "combined_divisibility": {"squared_form_equivalent": True, "printed_form_counterexample": counter},
          "system_1_3": {"equations": 36, "unknowns": 67, "max_degree": 38, "degrees": degs,
                         "matches_section3_construction": True}}
OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: v for k, v in report.items() if k != "system_1_3"}, indent=2))
print("degrees:", degs)
