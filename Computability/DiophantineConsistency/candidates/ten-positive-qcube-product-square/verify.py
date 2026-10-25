#!/usr/bin/env python3
"""Finite checks for the two q-cube product-square circuits (PROOF.md gives the proofs).

  1. coefficient binding (gzip and raw hashes, bit lengths) and the port box;
  2. counts, liveness, no gate on constants only;
  3. exact degree on random lines modulo 2^127-1 and 2^89-1;
  4. the transfer identity of section 1:  q^6 * N_new(n', s, ...) = N_133(n' - s, q^3 s, ...),
     at random points, against the pinned parent circuit;
  5. the centre identity of section 2:  Z_new / M_new = Z_133 / M_133 (as Z_new*M_133 = Z_133*M_new);
  6. the leading form of section 3: top(N) = top(Q)*top(Z)^2 (81) or -top(Q)*top(RG)*top(V)^2 (82),
     measured register by register along random rays through the origin;
  7. the syntactic degree bound of every register (sum for *, max for + and -), which must equal
     the measured exact degree of N, so the measured lower bound is also an upper bound;
  8. the transfer identity in exact integers, with small ports in the port box, at points with
     n' - s <= 0 as well as n' - s > 0;
  9. mutation rejection: flipping the sign of the low bracket, or dropping the shift of n,
     breaks the transfer identity.
Writes CHECKS.json (or --output PATH).
"""
import gzip, hashlib, json, math, os, random, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
PARENT_DIR = os.path.join(ROOT, "con-zfc-diophantine-forms", "133-staged-certificates", "compact")
P1, P2 = (1 << 127) - 1, (1 << 89) - 1
CIRCUITS = {"qcube_product_square_81": "equation_84", "qcube_product_square_82": "equation_85"}
res = {"checks": []}


def check(name, ok, **kw):
    res["checks"].append(dict(name=name, ok=bool(ok), **kw))
    print(("ok  " if ok else "FAIL"), name, kw if kw else "")
    if not ok:
        res["failed"] = True


def load_ports():
    b = json.load(open(os.path.join(HERE, "coefficients", "BINDING.json"), encoding="utf-8"))
    out = {}
    for key, m in b["ports"].items():
        gz = open(os.path.join(HERE, "coefficients", m["file"]), "rb").read()
        raw = gzip.decompress(gz)
        out[key] = int.from_bytes(raw, "little")
        check("binding " + key, hashlib.sha256(gz).hexdigest() == m["gzip_sha256"]
              and hashlib.sha256(raw).hexdigest() == m["raw_sha256"] and out[key].bit_length() == m["bits"])
    be, K0, MC, MF = out["beta"], out["K0"], out["MC"], out["MF"]
    check("port box", be % 2 == 1 and be >= 31 and K0 > 0 and 0 < MC < be < MF < 2 * be)
    return out


def ev(src, env, mod):
    v = dict(env)
    for n, o, x, y in src:
        a = v[x] if isinstance(x, str) else x
        b = v[y] if isinstance(y, str) else y
        v[n] = (a + b if o == "+" else a - b if o == "-" else a * b) % mod
    return v


def line(src, wit, pm, mod, rng, origin=False, regs=("N",), maxdeg=800):
    base = {w: (0 if origin else rng.randrange(1, mod)) for w in wit}
    dirn = {w: rng.randrange(1, mod) for w in wit}
    vals = {r: [] for r in regs}
    for t in range(maxdeg + 2):
        env = {k: x % mod for k, x in pm.items()}
        env.update({w: (base[w] + t * dirn[w]) % mod for w in wit})
        v = ev(src, env, mod)
        for r in regs:
            vals[r].append(v[r])
    out = {}
    for r, seq in vals.items():
        cur, dg, diffs = seq, 0, [seq]
        for k in range(1, len(seq)):
            cur = [(cur[i + 1] - cur[i]) % mod for i in range(len(cur) - 1)]
            diffs.append(cur)
            if any(cur):
                dg = k
            else:
                break
        out[r] = (dg, diffs[dg][0] * pow(math.factorial(dg) % mod, -1, mod) % mod)
    return out


def syntactic_degree(src, wit):
    d = {w: 1 for w in wit}
    for n, o, x, y in src:
        a = d.get(x, 0) if isinstance(x, str) else 0
        b = d.get(y, 0) if isinstance(y, str) else 0
        d[n] = a + b if o == "*" else max(a, b)
    return d


def transfer_ok(src, psrc, wit, pm, x, mod=None, shift=True):
    env = dict(pm); env.update(x)
    vn = ev(src, env, mod) if mod else ev_exact(src, env)
    q = vn["q"]
    penv = dict(pm); penv.update({w: x[w] for w in wit if w != "s"})
    penv["Y"] = q ** 3 * x["s"]
    penv["n"] = x["n"] - x["s"] if shift else x["n"]
    if mod:
        penv = {k: v % mod for k, v in penv.items()}
        vp = ev(psrc, penv, mod)
        return pow(q, 6, mod) * vn["N"] % mod == vp["N"], vn["Znum"] * vp["Mtot"] % mod == vp["Znum"] * vn["Mtot"] % mod
    vp = ev_exact(psrc, penv)
    return q ** 6 * vn["N"] == vp["N"], vn["Znum"] * vp["Mtot"] == vp["Znum"] * vn["Mtot"]


def ev_exact(src, env):
    v = dict(env)
    for n, o, x, y in src:
        a = v[x] if isinstance(x, str) else x
        b = v[y] if isinstance(y, str) else y
        v[n] = a + b if o == "+" else a - b if o == "-" else a * b
    return v


def main():
    pm = load_ports()
    for name, pname in CIRCUITS.items():
        e = json.load(open(os.path.join(HERE, "equations", name + ".json"), encoding="utf-8"))
        par = json.load(open(os.path.join(PARENT_DIR, pname + ".json"), encoding="utf-8"))
        src, wit = e["source"], e["witnesses"]
        need = {"N"}
        for n, o, x, y in reversed(src):
            if n in need:
                need.update(a for a in (x, y) if isinstance(a, str))
        regs = {r[0] for r in src}
        const_only = [r[0] for r in src if not any(isinstance(a, str) for a in r[2:])]
        check(name + ": counts", len(src) == e["operations"] and all(r[0] in need for r in src)
              and all(w in need for w in wit) and not const_only
              and dict(sorted(Counter(r[1] for r in src).items())) == e["operation_breakdown"],
              rows=len(src))
        rng = random.Random(1)
        for mod in (P1, P1, P2):
            dg = line(src, wit, pm, mod, rng)["N"][0]
            check(f"{name}: exact degree mod 2^{mod.bit_length()}-1", dg == e["exact_degree"], degree=dg)
        sd = syntactic_degree(src, wit)
        check(f"{name}: syntactic degree bound of N equals the exact degree", sd["N"] == e["exact_degree"],
              bound=sd["N"], registers=dict(Q=sd["Q"], V=sd["V"], RG=sd["RG"], Z=sd["Znum"]))
        rng = random.Random(2)
        ok_t, ok_c = True, True
        for mod in (P1, P2):
            for _ in range(8):
                x = {w: rng.randrange(1, mod) for w in wit}
                a, b = transfer_ok(src, par["source"], wit, {k: v % mod for k, v in pm.items()}, x, mod)
                ok_t &= a; ok_c &= b
        check(f"{name}: transfer identity q^6 N_new(n', s) = N_133(n' - s, q^3 s) (16 points, two primes)", ok_t)
        check(f"{name}: centre identity Z_new/M_new = Z_133/M_133 (16 points, two primes)", ok_c)
        small = {"beta": 31, "K0": 5, "MC": 3, "MF": 33}
        rng = random.Random(6)
        ok_e, signs = True, Counter()
        for _ in range(30):
            x = {w: rng.randrange(1, 6) for w in wit}
            signs["n'-s<=0" if x["n"] <= x["s"] else "n'-s>0"] += 1
            a, b = transfer_ok(src, par["source"], wit, small, x)
            ok_e &= a and b
        check(f"{name}: transfer and centre identities in exact integers, small ports", ok_e and len(signs) == 2,
              points=dict(signs))
        bad = [list(r) for r in src]
        for r in bad:
            if r[0] == "lowsum":
                r[1] = "-"
        x = {w: rng.randrange(1, P1) for w in wit}
        pmp = {k: v % P1 for k, v in pm.items()}
        m1 = not transfer_ok(bad, par["source"], wit, pmp, x, P1)[0]
        m2 = not transfer_ok(src, par["source"], wit, pmp, x, P1, shift=False)[0]
        check(f"{name}: mutations rejected (low-bracket sign; unshifted n)", m1 and m2)
        res.setdefault("equation_sha256", {})[name] = hashlib.sha256(
            open(os.path.join(HERE, "equations", name + ".json"), "rb").read()).hexdigest()
        for seed in (3, 4):
            m = line(src, wit, pm, P1, random.Random(seed), origin=True, regs=("N", "Q", "Znum", "RG", "V"))
            dQ, tQ = m["Q"]; dZ, tZ = m["Znum"]; dR, tR = m["RG"]; dV, tV = m["V"]
            if e["exact_degree"] == dQ + 2 * dZ:
                pred, form = tQ * tZ % P1 * tZ % P1, "Q0*Z0^2"
            else:
                pred, form = (-tQ * tR % P1 * tV % P1 * tV) % P1, "-Q0*RG0*V0^2"
            check(f"{name}: leading form {form} (ray {seed})", m["N"][0] == e["exact_degree"] and m["N"][1] == pred and pred != 0,
                  degrees=dict(N=m["N"][0], Q=dQ, Z=dZ, RG=dR, V=dV))
    res["ok"] = not res.get("failed")
    out = sys.argv[sys.argv.index("--output") + 1] if "--output" in sys.argv else os.path.join(HERE, "CHECKS.json")
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        json.dump(res, f, indent=1)
        f.write("\n")
    print("ALL OK" if res["ok"] else "FAILURES")
    raise SystemExit(0 if res["ok"] else 1)


if __name__ == "__main__":
    main()
