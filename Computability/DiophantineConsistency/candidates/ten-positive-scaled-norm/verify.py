#!/usr/bin/env python3
"""Finite audits supporting PROOF.md; writes CHECKS.json.

    python verify.py            all audits (the actual-port bounds take minutes)
    python verify.py --quick    skip the actual-port bound audit

Audits:
  norm       compact F16 equals the product of its 16 conjugate factors (SymPy)
  contracts  circuit rows agree with an independent formula evaluator,
             modulo a 127-bit prime at random points with the ACTUAL ports
  conjugates N = delta^8 Mtot^16 prod(Znum/Mtot - signed roots) at real points
             (exact integers against 4000-digit mpmath, toy ports)
  degree     syntactic bound 928; exact restriction to random lines modulo two
             primes with the actual ports: N has degree exactly 816 with leading
             coefficient omega0^8, and omega = fs - fc has degree 102 with leading
             coefficient omega0, the closed form of PROOF.md Section 8
  kernel     mu-scaled and unscaled Pell kernels with toy q (16 <= q <= 64) and Pell
             values up to 3.7 million bits: ratio bounds, intervals, index moduli,
             both projections, the Archimedean bound; not the actual sizes
  lemmas     composition divisibility and the adjacent-coefficient descent,
             exhaustively on small parameters
  bounds     unconditional separation, the majorant inequalities of Section 5,
             the mask bound R < q^4 + (alpha+2) q^2 and the mu^2 coprimality,
             with the actual ports in the cases b' < 0, b' > 0 and b' = 0
These are finite checks. The universal statements are proved in PROOF.md.
"""
import itertools
import json
import random
import sys
import time
from fractions import Fraction
from math import comb, gcd
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.dont_write_bytecode = True

import build    # noqa: E402
import circuit  # noqa: E402

RESULTS = {}


def require(cond, msg):
    if not cond:
        raise SystemExit("AUDIT FAILED: " + msg)


# ---------------------------------------------------------------- formulas

def formula(env):
    """Registers straight from PROOF.md Section 1 (independent of circuit.rows)."""
    beta, K0, MC, MF = env["beta"], env["K0"], env["MC"], env["MF"]
    j, F, al, i, T, w, Y, n, eta, zeta = (env[x] for x in circuit.WITNESSES)
    J = 2 * j + 1; q = beta * J + 1; C = q - F - al; X = w * q
    k = eta + zeta; c = k * Y + eta; a = Y * (X + 1)
    mu = q * q + 1
    Ap = mu * (a + 2) + 1; Am1 = Ap - 1; Hp = 4 * Ap - 5; Dp = Ap * Ap - 1; ap = Ap - 2
    V0 = X * mu * mu * Y * Y; Dtau = V0 * (V0 + 1) * k * k + 1
    G = (q - 1) * (q - F) + al
    R = G * (q * q - 1) + (MC + q * MF) * J
    e = k - R - 1
    Bt = (K0 + w) * C - F
    I = i * mu * c * c
    Df = 1 + Dp * I * I
    Q = Dp * Dp * I * I
    delta = Q - 1
    Tp = T + al
    bp = c * Tp - R
    V = Df * bp - c
    Dnum = Q * V * V - 1
    Dmain = Dp * c * c + 1
    L = 4 * Am1 * I + bp + c * Tp
    W = 1 + (q - 1) * L
    P1 = q ** 3 * (q - 1)
    Mtot = P1 * mu * mu * Hp
    Z0 = (Mtot * n + P1 * mu * mu * (X + ap * c) + (q - 1) * mu * mu * Hp * Y
          - q ** 3 * mu * mu * Hp * W * Bt - P1 * Hp * e)
    Znum = Z0 + Mtot * V
    fs = delta * Znum ** 2
    fa = delta * Mtot ** 2 * Dtau
    fb = delta * Mtot ** 2 * Df
    fc = Mtot ** 2 * Dnum
    fd = delta * (P1 * mu * mu) ** 2 * Dmain
    return locals()


def F16(s, a, b, c, d):
    sig1 = a + b + c; sig2 = a * b + (a + b) * c; sig3 = a * b * c
    U = s + d; Po = U - sig1; sd = s * d
    Pe = Po * Po + 4 * (sd - sig2)
    Ge = Pe * Pe + 16 * (sd * Po * Po - 4 * sig3 * U)
    Go = Pe * Po - 16 * sig3
    return Ge * Ge - 64 * sd * Go * Go


def formula_N(env):
    r = formula(env)
    return F16(r["fs"], r["fa"], r["fb"], r["fc"], r["fd"])


# ---------------------------------------------------------------- audits

def audit_norm():
    import sympy as sp
    x, a, b, c, d, ra, rb, rc, rd = sp.symbols("x a b c d ra rb rc rd")
    prod = sp.Integer(1)
    for e in itertools.product((1, -1), repeat=4):
        prod *= (x - e[0] * ra - e[1] * rb - e[2] * rc - e[3] * rd)
    poly = sp.Poly(sp.expand(prod), ra, rb, rc, rd)
    direct = 0
    for (pa, pb, pc, pd), coeff in poly.terms():
        require(all(t % 2 == 0 for t in (pa, pb, pc, pd)), "odd root power")
        direct += coeff * a ** (pa // 2) * b ** (pb // 2) * c ** (pc // 2) * d ** (pd // 2)
    compact = F16(x ** 2, a, b, c, d)
    require(sp.expand(direct - compact) == 0, "F16 identity")
    P = sp.Poly(sp.expand(compact), x, a, b, c, d)
    weights = {m[0] + 2 * sum(m[1:]) for m, _ in P.terms()}
    require(weights == {16}, "weighted homogeneity")
    require(P.coeff_monomial(x ** 16) == 1, "x^16 coefficient")
    # Lemma 8.1: F16(s; a, b, s - t, d) = prod over 8 signs of (t + L^2 - 2xL)
    t_ = sp.Symbol("t")
    lhs = sp.expand(F16(x ** 2, a, b, x ** 2 - t_, d))
    prod8 = sp.Integer(1)
    for e in itertools.product((1, -1), repeat=3):
        Lr = e[0] * ra + e[1] * rb + e[2] * rd
        prod8 *= (t_ + Lr ** 2 - 2 * x * Lr)
    p8 = sp.Poly(sp.expand(prod8), ra, rb, rd)
    red = 0
    for (pa, pb, pd), coeff in p8.terms():
        require(pa % 2 == 0 and pb % 2 == 0 and pd % 2 == 0, "odd root power (8.1)")
        red += coeff * a ** (pa // 2) * b ** (pb // 2) * d ** (pd // 2)
    require(sp.expand(lhs - red) == 0, "Lemma 8.1")
    RESULTS["norm"] = {"terms": len(P.terms()), "identity": True, "weighted_degree": 16,
                       "lemma_8_1": True}
    print("norm: F16 identity holds,", len(P.terms()), "terms; Lemma 8.1 holds")


def audit_contracts(ports):
    p = (1 << 127) - 1
    rng = random.Random(20261023)
    source = circuit.rows()
    pm = {k: v % p for k, v in ports.items()}
    names = {"q": "q", "C": "C", "X": "X", "a": "a", "k": "k", "c": "c", "mu": "mu",
             "Am1": "Am1", "Hp": "Hp", "Dp": "Dp", "V0": "V0", "Dtau": "Dtau", "R": "R",
             "e": "e", "Bt": "Bt", "I": "I", "Df": "Df", "Q": "Q", "delta": "delta",
             "Tp": "Tp", "cTR": "bp", "V": "V", "Dnum": "Dnum", "Dmain": "Dmain",
             "L": "L", "W": "W", "Mtot": "Mtot", "Znum": "Znum",
             "fs": "fs", "fa": "fa", "fb": "fb", "fc": "fc", "fd": "fd"}
    for _ in range(12):
        env = dict(pm)
        env.update({v: rng.randrange(1, p) for v in circuit.WITNESSES})
        got = circuit.evaluate(source, env, mod=p)
        want = formula(env)
        for row_name, formula_name in names.items():
            require(got[row_name] % p == want[formula_name] % p, "register contract " + row_name)
        require(got["N"] % p == formula_N(env) % p, "output N")
    RESULTS["contracts"] = {"points": 12, "prime_bits": 127, "ports": "actual",
                            "registers": sorted(names)}
    print("contracts: 12 random points modulo 2^127-1 agree, actual ports")


def audit_conjugates():
    import mpmath as mp
    mp.mp.dps = 4000
    rng = random.Random(77)
    source = circuit.rows()
    worst = mp.mpf(0)
    for trial in range(5):
        env = {"beta": rng.randrange(3, 40, 2), "K0": rng.randrange(1, 50),
               "MC": rng.randrange(1, 30), "MF": rng.randrange(1, 60)}
        env.update({v: rng.randrange(1, 7) for v in circuit.WITNESSES})
        vals = circuit.evaluate(source, env)
        r = formula(env)
        require(r["delta"] > 0 and r["Dnum"] > 0, "positive radicands")
        roots = [mp.sqrt(r["Dtau"]), mp.sqrt(r["Df"]),
                 mp.sqrt(mp.mpf(r["Dnum"]) / r["delta"]), mp.sqrt(r["Dmain"]) / r["Hp"]]
        z = mp.mpf(r["Znum"]) / r["Mtot"]
        prod = mp.mpf(1)
        for e in itertools.product((1, -1), repeat=4):
            prod *= z - sum(ei * ri for ei, ri in zip(e, roots))
        prod *= mp.mpf(r["delta"]) ** 8 * mp.mpf(r["Mtot"]) ** 16
        N = vals["N"]
        require(N != 0, "generic point has N != 0")
        worst = max(worst, abs(prod - N) / abs(N))
    require(worst < mp.mpf(10) ** -3000, "conjugate product identity")
    RESULTS["conjugates"] = {"points": 5, "digits": 4000, "worst_relative_error": mp.nstr(worst, 3)}
    print("conjugates: N = delta^8 Mtot^16 prod(...) at 5 real points, worst rel. error",
          mp.nstr(worst, 3))


def omega_top(env, p):
    """omega0 = 2 Q0 Z00 M0 V00 of PROOF.md Section 8, evaluated modulo p."""
    beta = env["beta"]
    j, F, al, i, T, w, Y, n, eta, zeta = (env[x] for x in circuit.WITNESSES)
    q0 = 2 * beta * j; k0 = eta + zeta
    mu0 = q0 ** 2; a0 = w * q0 * Y
    Dp0 = (mu0 * a0) ** 2; H0 = 4 * mu0 * a0
    I0 = i * mu0 * (k0 * Y) ** 2
    Df0 = Dp0 * I0 ** 2; Q0 = Dp0 ** 2 * I0 ** 2
    L0 = 4 * mu0 * a0 * I0; W0 = q0 * L0
    Bt0 = w * (q0 - F - al)
    M0 = q0 ** 4 * q0 ** 4 * H0
    Z00 = -H0 * q0 ** 4 * q0 ** 3 * W0 * Bt0
    V00 = -Df0 * q0 ** 3 * (q0 - F)
    return 2 * Q0 * Z00 * M0 * V00 % p


def line_degree(values, p):
    cur, diffs = values, []
    for _ in range(len(values)):
        diffs.append(cur[0])
        cur = [(cur[m + 1] - cur[m]) % p for m in range(len(cur) - 1)]
    return max(m for m in range(len(diffs)) if diffs[m]), diffs


def audit_degree(ports):
    source = circuit.rows()
    deg = circuit.syntactic_degrees(source)
    require(deg["N"] == 928, "syntactic bound")
    L = 840
    rng = random.Random(816)
    out = []
    fact816 = 1
    for m in range(2, 817):
        fact816 *= m
    fact102 = 1
    for m in range(2, 103):
        fact102 *= m
    for p in ((1 << 127) - 1, (1 << 89) - 1):
        pm = {k: v % p for k, v in ports.items()}
        for trial in range(2):
            base = {v: rng.randrange(1, p) for v in circuit.WITNESSES}
            dirn = {v: rng.randrange(1, p) for v in circuit.WITNESSES}
            Nvals, wvals = [], []
            for t in range(L + 1):
                env = dict(pm)
                env.update({v: (base[v] + t * dirn[v]) % p for v in circuit.WITNESSES})
                vals = circuit.evaluate(source, env, mod=p)
                Nvals.append(vals["N"])
                wvals.append((vals["fs"] - vals["fc"]) % p)
            dN, diffN = line_degree(Nvals, p)
            dw, diffw = line_degree(wvals[:130], p)
            require(dN == 816, "line degree of N")
            require(dw == 102, "line degree of omega")
            env = dict(pm); env.update(dirn)
            w0 = omega_top(env, p)
            require(diffw[102] * pow(fact102 % p, -1, p) % p == w0, "leading coefficient of omega")
            require(diffN[816] * pow(fact816 % p, -1, p) % p == pow(w0, 8, p),
                    "leading coefficient of N is omega0^8")
            out.append({"prime_bits": p.bit_length(), "degree_N": dN, "degree_omega": dw})
    RESULTS["degree"] = {"syntactic_bound": 928, "exact_degree": 816, "line_tests": out,
                         "top_form": "omega0^8, omega0 = 2 Q0 Z00 M0 V00 (PROOF.md Section 8)",
                         "argument_degrees": {x: deg[x] for x in ("fs", "fa", "fb", "fc", "fd")}}
    print("degree: syntactic 928; 4 actual-port line restrictions give degree 816 with leading"
          " coefficient omega0^8, and omega has degree 102 with leading coefficient omega0")


def pell(A, n):
    """(chi_A(n), psi_A(n)) by binary powering of A + sqrt(A^2-1)."""
    D = A * A - 1
    x, y, bx, by = 1, 0, A, 1
    while n:
        if n & 1:
            x, y = x * bx + D * y * by, x * by + y * bx
        bx, by = bx * bx + D * by * by, 2 * bx * by
        n >>= 1
    return x, y


def audit_kernel():
    cases = []
    for q, R in ((16, 51), (16, 63), (32, 99), (16, 131), (64, 195)):
        require(R % 4 == 3 and 3 * q < R < q ** 4, "kernel case hypotheses")
        r = (R - 1) // 2
        X = 2 ** R
        M = sum(comb(2 * r, r + jj) * X ** jj for jj in range(r + 1))
        theta = sum(Fraction(comb(2 * r, r - jj), X ** jj) for jj in range(1, r + 1))
        require(0 < theta < Fraction(1, 4) and M % 2 == 0, "half-binomial split")
        Y = M // 2
        a = Y * (X + 1)
        xi = Fraction((X + 1) ** (2 * r), X ** r)
        require(xi == M + theta, "xi = M + theta")
        # mu-scaled kernel
        mu = q * q + 1
        Ap = mu * (a + 2) + 1; Hp = 4 * Ap - 5; ap = Ap - 2
        V0 = X * mu ** 2 * Y ** 2; Pp = 2 * V0 + 1
        Dm, c = pell(Ap, R)
        _, k0 = pell(Pp, r + 1)
        k = 2 * k0
        require(xi < Fraction(c, k0) < xi * Fraction(a + 3, a) ** (2 * r), "scaled ratio bounds")
        require(k * Y < c < k * (Y + 1), "scaled interval")
        require((k - R - 1) % (mu * mu) == 0 and k > R + 1, "index excess divisible by mu^2")
        require((Dm - ap * c - pow(2, R, Hp)) % Hp == 0, "projection 2^R")
        require((Dm + ap * c - pow(2, -R, Hp)) % Hp == 0, "projection 2^-R")
        require(q ** 4 * 2 ** (R + 1) * X < Hp, "Archimedean bound q^4 2^(R+1) X < H'")
        g = Dm - X - ap * c
        require(g % Hp == 0 and g > 0, "g positive integer")
        require(Pp > Ap, "P' > A'")
        # unscaled kernel of package 61
        A = a + 2; H = 4 * a + 3; P0 = 2 * X * Y ** 2 + 1; E = X * Y
        Do, co = pell(A, R)
        _, k0o = pell(P0, r + 1)
        ko = 2 * k0o
        require(xi < Fraction(co, k0o) < xi * Fraction(a + 2, a) ** (2 * r), "unscaled ratio bounds")
        require(ko * Y < co < ko * (Y + 1), "unscaled interval")
        require((ko - R - 1) % E == 0 and ko > R + 1, "unscaled index quotient h >= 1")
        go = Do - X - a * co
        require(go % H == 0 and go > 0, "gamma_old positive integer")
        cases.append({"q": q, "R": R, "bits_c": c.bit_length(), "bits_c_old": co.bit_length()})
    RESULTS["kernel"] = {"cases": cases, "checked": [
        "xi < c/k0 < xi (1+3/a)^(2r)", "kY < c < k(Y+1)", "mu^2 | k-R-1", "projections 2^R and 2^-R",
        "q^4 2^(R+1) X < H'", "g > 0", "P' > A'",
        "xi < c_o/k0_o < xi (1+2/a)^(2r)", "unscaled interval", "E | k_o-R-1", "gamma_old > 0"]}
    print("kernel:", len(cases), "toy-q cases pass (mu-scaled and unscaled)")


def audit_lemmas():
    comp = 0
    for A in range(2, 14):
        for p in range(2, 6):
            c = pell(A, p)[1]
            require(pell(A, p * c)[1] % (c * c) == 0, "c^2 | psi(pc)")
            comp += 1
    for mu in (2, 3, 5, 10, 17):
        for base in (1, 2, 3):
            A = mu * base + 1
            for p in (2, 3):
                c = pell(A, p)[1]
                require(pell(A, p * c * mu)[1] % (mu * c * c) == 0, "mu c^2 | psi(pc mu)")
                comp += 1
    desc = 0
    for Q in range(2, 61):
        for V in range(-300, 301):
            num, den = Q * V * V - 1, Q - 1
            if num <= 0:
                continue
            fr = Fraction(num, den)
            a, b = fr.numerator, fr.denominator
            ra, rb = int(a ** 0.5 + 0.5), int(b ** 0.5 + 0.5)
            for x in (ra - 1, ra, ra + 1):
                if x >= 0 and x * x == a:
                    for z in (rb - 1, rb, rb + 1):
                        if z > 0 and z * z == b:
                            require(b == 1, "descent: rational y is integral")
                            desc += 1
    RESULTS["lemmas"] = {"composition_cases": comp, "descent_rational_squares_found": desc,
                         "descent_range": "2<=Q<=60, |V|<=300"}
    print("lemmas: composition", comp, "cases; descent finds", desc, "rational squares, all integral")


def audit_bounds(ports):
    try:
        import gmpy2
        Z, isqrt = gmpy2.mpz, gmpy2.isqrt
    except ImportError:
        from math import isqrt
        Z = int
    P = {k: Z(v) for k, v in ports.items()}

    def regs(v):
        env = dict(P); env.update({x: Z(v[x]) for x in circuit.WITNESSES})
        return formula(env)

    def one(v, label):
        r = regs(v)
        q, Hp, mu = r["q"], r["Hp"], r["mu"]
        require(q % 2 == 0, "q even")
        require(gcd(int(mu * mu), int(q ** 3 * (q - 1) * Hp)) == 1, "mu^2 coprime to q^3 (q-1) H'")
        require(r["R"] < q ** 4 + (r["al"] + 2) * q ** 2, "R < q^4 + (alpha+2) q^2")
        b = r["bp"]
        hi = lambda N_: isqrt(N_) + 1
        t_lo, t_hi = isqrt(r["Dtau"]), hi(r["Dtau"])
        f_lo, f_hi = isqrt(r["Df"]), hi(r["Df"])
        yq = r["Dnum"] // r["delta"]
        y_lo, y_hi = isqrt(yq), isqrt(yq) + 1
        d_hi = hi(r["Dmain"]) // Hp + 1
        if b == 0:
            require(r["V"] == -r["c"] and y_lo >= r["c"] and y_hi <= r["c"] + 1, "b'=0 bracket")
            require(y_lo > d_hi and t_lo > y_hi + d_hi and f_lo > t_hi + y_hi + d_hi, "order d<y<tau<f")
        else:
            require(t_lo > d_hi and f_lo > t_hi + d_hi and y_lo > f_hi + t_hi + d_hi, "order d<tau<f<y")
        At = r["Am1"] * r["I"]
        require(At > (r["V0"] + 1) * r["k"] + 2 * r["c"] + 1, "(5.5.1)")
        require(t_hi + f_hi + 2 * r["c"] + 2 < 3 * At, "(5.6.1)")
        require(r["Df"] < r["Q"] - 1, "Df < Q - 1")
        case = "b'=0" if b == 0 else ("b'>0" if b > 0 else "b'<0")
        print(f"  bounds {label}: {case}, Dnum has {int(r['Dnum']).bit_length()} bits")
        return {"label": label, "case": case, "Dnum_bits": int(r["Dnum"]).bit_length()}

    rng = random.Random(816)
    out = []
    for trial in range(2):
        out.append(one({x: rng.randrange(1, 6) for x in circuit.WITNESSES}, f"random{trial}"))
    v = {x: rng.randrange(1, 6) for x in circuit.WITNESSES}
    r = regs(v)
    v["T"] = int(r["R"] // r["c"]) + 3
    out.append(one(v, "T above R/c"))
    found = None
    for Y in range(1, 40):
        for eta in range(1, 12):
            for zeta in range(1, 12):
                v = {"j": 1, "F": 2, "alpha": 3, "i": 1, "T": 1, "w": 1, "Y": Y, "n": 1,
                     "eta": eta, "zeta": zeta}
                r = regs(v)
                if r["R"] > 0 and r["R"] % r["c"] == 0 and r["R"] // r["c"] > 3:
                    v["T"] = int(r["R"] // r["c"]) - 3      # T' = T + alpha = R/c
                    found = one(v, f"c={int(r['c'])} divides R")
                    break
            if found:
                break
        if found:
            break
    require(found is not None, "a b'=0 instance exists")
    out.append(found)
    RESULTS["bounds"] = {"ports": "actual", "cases": out}


def main():
    t0 = time.time()
    ports = build.load_ports()
    RESULTS["ports"] = {"bound": True, "B": "2^590069",
                        "inequalities": "0<MC<beta, beta<MF<2beta, K0>0, beta odd"}
    audit_norm()
    audit_contracts(ports)
    audit_conjugates()
    audit_degree(ports)
    audit_kernel()
    audit_lemmas()
    if "--quick" in sys.argv[1:]:
        RESULTS["bounds"] = "skipped (--quick)"
    else:
        audit_bounds(ports)
    RESULTS["python_optimize_flag"] = sys.flags.optimize
    print(f"all audits passed in {time.time() - t0:.0f} s")
    if "--quick" not in sys.argv[1:]:
        (HERE / "CHECKS.json").write_text(json.dumps(RESULTS, indent=1) + "\n",
                                          encoding="utf-8", newline="\n")
        print("wrote CHECKS.json")


if __name__ == "__main__":
    main()
