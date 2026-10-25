#!/usr/bin/env python3
"""Finite checks for the six gap-fusion circuits (see PROOF.md for the proofs).

  1. coefficient binding: gzip/raw hashes and the port box of the whole tuple;
  2. every circuit: rows, live rows, operation split, all inputs live, no gate on constants only;
  3. exact total degree along two random lines, modulo 2^127-1 and modulo 2^89-1;
  4. the leading homogeneous form of PROOF.md section 6, against the top coefficient of
     N(t*x) along random rays through the origin;
  5. the expansion identity of section 6 at random points;
  6. Pell trace values used by the auxiliary-index gap (section 3).
Writes CHECKS.json (or the path given by --output).
"""
import gzip, hashlib, json, math, os, random, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
P1 = (1 << 127) - 1
P2 = (1 << 89) - 1
NAMES = ["gap_fusion_scaled", "gap_fusion_scaled_lower_centre", "gap_fusion_scaled_sharp_centre",
         "gap_fusion_direct", "gap_fusion_direct_lower_centre", "gap_fusion_direct_sharp_centre"]
results = {"checks": []}


def check(name, ok, **info):
    results["checks"].append(dict(name=name, ok=bool(ok), **info))
    print(("ok  " if ok else "FAIL"), name, info if info else "")
    if not ok:
        results["failed"] = True


def ports():
    b = json.load(open(os.path.join(HERE, "coefficients", "BINDING.json"), encoding="utf-8"))
    out = {}
    for key, meta in b["ports"].items():
        raw_gz = open(os.path.join(HERE, "coefficients", meta["file"]), "rb").read()
        raw = gzip.decompress(raw_gz)
        check("binding " + key, hashlib.sha256(raw_gz).hexdigest() == meta["gzip_sha256"]
              and hashlib.sha256(raw).hexdigest() == meta["raw_sha256"])
        out[key] = int.from_bytes(raw, "little")
        check("bits " + key, out[key].bit_length() == meta["bits"], bits=out[key].bit_length())
    be, K0, MC, MF = out["beta"], out["K0"], out["MC"], out["MF"]
    check("port box: beta odd, beta>=31, K0>0, 0<MC<beta<MF<2beta",
          be % 2 == 1 and be >= 31 and K0 > 0 and 0 < MC < be < MF < 2 * be)
    return out


def ev(src, env, mod):
    v = dict(env)
    for n, o, x, y in src:
        a = v[x] if isinstance(x, str) else x
        b = v[y] if isinstance(y, str) else y
        v[n] = (a + b if o == "+" else a - b if o == "-" else a * b) % mod
    return v


def line_degree(src, wit, pm, mod, seed, through_origin=False, maxdeg=400):
    rng = random.Random(seed)
    base = {w: (0 if through_origin else rng.randrange(1, mod)) for w in wit}
    dirn = {w: rng.randrange(1, mod) for w in wit}
    vals = []
    for t in range(maxdeg + 2):
        env = {k: v % mod for k, v in pm.items()}
        env.update({w: (base[w] + t * dirn[w]) % mod for w in wit})
        vals.append(ev(src, env, mod)["N"])
    diffs = [vals]
    cur = vals
    deg = 0
    for k in range(1, maxdeg + 2):
        cur = [(cur[i + 1] - cur[i]) % mod for i in range(len(cur) - 1)]
        diffs.append(cur)
        if any(cur):
            deg = k
        else:
            break
    top = diffs[deg][0] * pow(math.factorial(deg) % mod, -1, mod) % mod if deg else vals[0]
    return deg, top, dirn


def leading_form(kind, base, x, pm, mod):
    """Predicted top homogeneous part of N (PROOF.md section 6) at the witness point x."""
    beta = pm["beta"] % mod
    J, F, i, Y, eta, zeta = (x[k] for k in ("J", "F", "i", "Y", "eta", "zeta"))
    q0 = beta * J % mod
    X0 = (x["w"] * q0) % mod if base == "scaled" else (q0 + x["x"]) % mod
    mu0 = q0 * q0 % mod
    A0 = mu0 * Y % mod * X0 % mod
    D0lt = A0 * A0 % mod                       # Delta_0
    H0 = 4 * A0 % mod
    k = (eta + zeta) % mod
    V00 = X0 * mu0 % mod * mu0 % mod * Y % mod * Y % mod
    Dt0 = V00 * V00 % mod * k % mod * k % mod
    c0 = k * Y % mod
    E0 = i * c0 % mod * c0 % mod
    Fs0 = D0lt * Dt0 % mod * E0 % mod * E0 % mod
    delta0 = D0lt * D0lt % mod * Dt0 % mod * E0 % mod * E0 % mod
    R0 = pow(q0, 3, mod) * ((q0 - F) % mod) % mod
    b0 = (-R0) % mod
    Vaux0 = Fs0 * b0 % mod
    P0 = pow(q0, 4 if base == "scaled" else 5, mod)
    M0 = P0 * mu0 % mod * mu0 % mod * H0 % mod
    a0 = Dt0 * Fs0 % mod
    common = delta0 * delta0 % mod * pow(M0, 4, mod) % mod * Vaux0 % mod * Vaux0 % mod
    if kind == "none":
        return (-4 * common * a0) % mod
    if kind == "lower":
        return (-8 * common * A0 % mod * Dt0 % mod * Dt0 % mod * E0 % mod * E0) % mod
    return (4 * common * Dt0 % mod * Dt0 % mod * E0 % mod * E0) % mod


def expansion_identity(src, wit, pm, kind, mod, seed):
    """N = 4 d^2 M^4 V^2 (C^2-a) + 4 d M^2 V C beta + beta^2 - 4 d M^4 a V^2 + 4 d M^4 a,
       beta = d M^2 (C^2-a) - M^2 (V^2-1) + 2 d M (V+C) Z0 + d Z0^2,  Z0 = Z - M (V+C)."""
    rng = random.Random(seed)
    env = {k: v % mod for k, v in pm.items()}
    env.update({w: rng.randrange(1, mod) for w in wit})
    v = ev(src, env, mod)
    d, M, V, Z = v["delta"], v["Mtot"], v["V"], v["Znum"]
    a = v["pair"]
    C = v.get("Cg", 0)
    Z0 = (Z - M * (V + C)) % mod
    ca = (C * C - a) % mod
    M2 = M * M % mod
    beta = (d * M2 % mod * ca - M2 * (V * V - 1) + 2 * d * M % mod * (V + C) % mod * Z0 + d * Z0 % mod * Z0) % mod
    rhs = (4 * d * d % mod * M2 % mod * M2 % mod * V % mod * V % mod * ca
           + 4 * d * M2 % mod * V % mod * C % mod * beta + beta * beta
           - 4 * d * M2 % mod * M2 % mod * a % mod * V % mod * V
           + 4 * d * M2 % mod * M2 % mod * a) % mod
    return v["N"] == rhs


def formula_N(base, kind, x, pm, mod):
    """Independent evaluation of PROOF.md section 1 (not the circuit rows)."""
    beta, K0, MC, MF = (pm[k] % mod for k in ("beta", "K0", "MC", "MF"))
    J, F, al, i, T, Y, n, eta, zeta = (x[k] for k in ("J", "F", "alpha", "i", "T", "Y", "n", "eta", "zeta"))
    q = beta * J + 1
    Cd = q - F - al
    if base == "scaled":
        X = x["w"] * q; g = q - 1; B = (K0 + x["w"]) * Cd - F; P = q**3 * (q - 1); Dlow = 0
    else:
        X = q + x["x"]; g = q * (q - 1); B = (q * K0 + X) * Cd - q * F; P = q**4 * (q - 1); Dlow = (q - 1) * X
    mu = q * q + 1; A = mu * Y * (X + 1) + 1; Delta = A * A - 1; H = 4 * A - 5
    k = eta + zeta; c = k * Y + eta
    V1 = X * mu**2 * Y**2; D = V1 * (V1 + 1) * k * k + 1
    G = (q - 1) * (q - F) + al; R = G * (q * q - 1) + (MC + q * MF) * J; e = k - R - 1
    E = i * c * c; Fs = 1 + Delta * D * E * E; Q = Delta**2 * D * E * E; delta = Q - 1
    b = c * (T + al) - R; V = Fs * b - c; Dnum = Q * V * V - 1
    M = P * mu**2 * H; Kpos = X * (3 * c - 2 * X) + 2
    Gamma = 0 if kind == "none" else ((A - 1) if kind == "lower" else A) * D * E
    Z = P * mu**2 * (H * (n + V + Gamma - b * B) + Kpos) + H * (mu**2 * (g * Y - q**3 * B - Dlow) - P * e)
    a = D * Fs; s_ = delta * Z * Z; u = delta * M * M * a; v = M * M * Dnum
    return ((s_ - v - u) ** 2 - 4 * u * v) % mod


def chi(S, n):
    a, b = 1, S
    for _ in range(n):
        a, b = b, 2 * S * b - a
    return a


def main():
    pm = ports()
    for name in NAMES:
        e = json.load(open(os.path.join(HERE, "equations", name + ".json"), encoding="utf-8"))
        src, wit = e["source"], e["witnesses"]
        need = {"N"}
        for n, o, x, y in reversed(src):
            if n in need:
                need.update(a for a in (x, y) if isinstance(a, str))
        live = [r for r in src if r[0] in need]
        split = dict(sorted(Counter(r[1] for r in live).items()))
        inputs = set(wit) | set(e["fixed_numerals"])
        const_only = [r[0] for r in live if not any(isinstance(a, str) and (a in inputs or a in {s[0] for s in src}) for a in r[2:])]
        check(name + ": counts", len(live) == len(src) == e["operations"] and split == e["operation_breakdown"]
              and all(w in need for w in wit) and not const_only,
              rows=len(src), live=len(live), split=split)
        kind = "none" if e["centre"] == "none" else ("lower" if e["centre"].startswith("(A-1)") else "sharp")
        base = "scaled" if e["base"].startswith("scaled") else "direct"
        for mod, seed in ((P1, 1), (P1, 2), (P2, 3)):
            deg, _, _ = line_degree(src, wit, pm, mod, seed)
            check(f"{name}: exact degree on a random line mod 2^{mod.bit_length()}-1 (seed {seed})",
                  deg == e["exact_degree"], degree=deg)
        for seed in (4, 5):
            deg, top, dirn = line_degree(src, wit, pm, P1, seed, through_origin=True)
            pred = leading_form(kind, base, dirn, pm, P1)
            check(f"{name}: leading homogeneous form matches section 6 (ray seed {seed})",
                  deg == e["exact_degree"] and top == pred and top != 0)
        for seed in (6, 7):
            check(f"{name}: expansion identity of section 6 (seed {seed})",
                  expansion_identity(src, wit, pm, kind, P1, seed))
        rng = random.Random(8)
        agree = True
        for _ in range(4):
            pt = {w: rng.randrange(1, P1) for w in wit}
            env = {k: v % P1 for k, v in pm.items()}; env.update(pt)
            agree &= ev(src, env, P1)["N"] == formula_N(base, kind, pt, pm, P1)
        check(f"{name}: circuit equals an independent evaluation of PROOF.md section 1", agree)
    ok = all(chi(S, 1) == S and chi(S, 3) == S * (4 * S * S - 3) and chi(S, 5) == S * (16 * S**4 - 20 * S**2 + 5)
             and chi(S, 5) // S > 8 * (S * S) ** 2 and all(chi(S, v) % S == 0 for v in range(1, 9, 2))
             and all(chi(S, v) % S != 0 for v in range(0, 9, 2))
             for S in range(2, 60))
    check("Pell traces: chi_S(1)/S=1, chi_S(3)/S=4Q-3, chi_S(5)/S=16Q^2-20Q+5>8Q^2, S|chi_S(v) iff v odd (S<60)", ok)
    results["ok"] = not results.get("failed")
    out = sys.argv[sys.argv.index("--output") + 1] if "--output" in sys.argv else os.path.join(HERE, "CHECKS.json")
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        json.dump(results, f, indent=1)
        f.write("\n")
    print("ALL OK" if results["ok"] else "FAILURES")
    raise SystemExit(0 if results["ok"] else 1)


if __name__ == "__main__":
    main()
