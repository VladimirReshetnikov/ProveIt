"""Compare package 192's oriented companion JSON with its Lean syntax.

Usage: py -I -X utf8 -S -B check_oriented70.py

Parses the `let` chain of `ThirteenOriented70.front13o` and the final
continuation of `expressionAt70o`
(`Lean/DiophantineConsistency/Adm942/ThirteenOriented70.lean`), and the gate
list of `192-pell-centers-fused-bounds/compact13/positive13_oriented.json`
(13 / 70 / 170), into expression trees over the 13 coordinates and the port
leaves (Lean `p 0..3` = JSON beta, K0, MC, MF). Both are normalized modulo
associativity and commutativity of `+` and `*` (with `x ^ n` read as an n-fold
product; subtraction kept binary) and the two output trees must be identical.
The JSON bytes are pinned by SHA-256, the witness order, the operation count
and the exact degree are checked from the JSON (the degree is recomputed by
evaluating the gate list on random rays over a prime field), and every
single-gate operation change is a negative control.
As a further control, the main form's gate `LB = V2*B` substituted for the
companion's `L = cTminusR*V; LB = L*B` must be detected.
This is a finite syntactic check outside Lean.
"""
import ast
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
LEAN = ROOT / "Lean/DiophantineConsistency/Adm942/ThirteenOriented70.lean"
JSON = ROOT / "con-zfc-diophantine-forms/192-pell-centers-fused-bounds/compact13/positive13_oriented.json"
PIN = "f51a42d4a31dd773f131c0cdde31790068257dd6e195bdcee11635b99a7d160d"
PORTS = {"0": "beta", "1": "K0", "2": "MC", "3": "MF"}
WITNESSES = ["J", "F", "alpha", "f", "i", "T", "s", "w", "n", "eta", "zeta", "m", "gamma"]


def norm(t):
    """Normal form: ('+', sorted args) / ('*', sorted args) / ('-', a, b) / leaf."""
    if isinstance(t, tuple) and t[0] in "+*":
        args = []
        for a in t[1:]:
            a = norm(a)
            if isinstance(a, tuple) and a[0] == t[0]:
                args.extend(a[1])
            else:
                args.append(a)
        return (t[0], tuple(sorted(args, key=repr)))
    if isinstance(t, tuple) and t[0] == "-":
        return ("-", norm(t[1]), norm(t[2]))
    return t


def build(src, env):
    src = re.sub(r"Expr\.constant \(p (\d)\)", lambda m: PORTS[m.group(1)], src)
    src = src.replace("^", "**")
    tree = ast.parse(src, mode="eval").body

    def go(n):
        if isinstance(n, ast.BinOp):
            a, b = go(n.left), go(n.right)
            if isinstance(n.op, ast.Add):
                return ("+", a, b)
            if isinstance(n.op, ast.Mult):
                return ("*", a, b)
            if isinstance(n.op, ast.Sub):
                return ("-", a, b)
            if isinstance(n.op, ast.Pow):
                assert isinstance(n.right, ast.Constant)
                return ("*",) + (a,) * n.right.value
        if isinstance(n, ast.Name):
            return env.get(n.id, n.id)
        if isinstance(n, ast.Constant):
            return n.value
        raise ValueError(ast.dump(n))
    return go(tree)


def json_tree(d, source=None):
    env = {w: w for w in d["witnesses"]}
    env.update({k: k for k in d["fixed_numerals"]})
    for name, op, a, b in (source or d["source"]):
        ta = env[a] if isinstance(a, str) else a
        tb = env[b] if isinstance(b, str) else b
        env[name] = (op, ta, tb)
    return env[d["output"]]


def json_degree(d):
    """Upper bound on the total degree in the witnesses (ports and integers have
    degree 0): products add, sums and differences take the maximum."""
    deg = {w: 1 for w in d["witnesses"]}
    deg.update({k: 0 for k in d["fixed_numerals"]})
    for name, op, a, b in d["source"]:
        da = deg[a] if isinstance(a, str) else 0
        db = deg[b] if isinstance(b, str) else 0
        deg[name] = da + db if op == "*" else max(da, db)
    return deg[d["output"]]


def leading_degree(d):
    """Degree of the polynomial restricted to random rays x0 + t*dx over GF(2^61-1),
    read off from Newton forward differences at bound+1 points (the largest order
    with a nonzero difference; orders above the true degree vanish identically).
    The ray degree never exceeds the total degree, so it is a certain lower bound;
    the gate bound may overcount (the leading forms of N1 = D^2 - Delta c^2 cancel).
    If the total degree D exceeded the ray degree, the top form of degree D would
    vanish at the random direction dx, which has probability at most D/(2^61-1) per
    ray (Schwartz-Zippel); three independent rays make this a probabilistic upper
    bound."""
    import random
    P = (1 << 61) - 1
    bound = json_degree(d)
    rng = random.Random(192170)

    def ev(vals):
        env = dict(vals)
        for name, op, a, b in d["source"]:
            x = env[a] if isinstance(a, str) else a
            y = env[b] if isinstance(b, str) else b
            env[name] = (x + y) % P if op == "+" else (x * y) % P if op == "*" else (x - y) % P
        return env[d["output"]]

    best = -1
    for _ in range(3):
        base = {k: rng.randrange(P) for k in d["fixed_numerals"]}
        x0 = {w: rng.randrange(P) for w in d["witnesses"]}
        dx = {w: rng.randrange(P) for w in d["witnesses"]}
        ys = []
        for t in range(bound + 1):
            vals = dict(base)
            vals.update({w: (x0[w] + t * dx[w]) % P for w in d["witnesses"]})
            ys.append(ev(vals))
        # Newton forward differences: the degree is the last nonzero difference.
        cur, deg = ys, -1
        for k in range(bound + 1):
            if cur[0] % P:
                deg = k
            cur = [(cur[i + 1] - cur[i]) % P for i in range(len(cur) - 1)]
            if not cur:
                break
        best = max(best, deg)
    return best, bound


def lean_tree():
    text = LEAN.read_text(encoding="utf-8")
    body = text[text.index("def front13o"):text.index("/-- The oriented 13/70/170 polynomial. -/")]
    body = body[body.index("  let J"):body.index("  final ")]
    env, stmt = {}, ""
    for line in [l for l in body.split("\n") if l.strip()] + ["let END := 0"]:
        s = line.strip()
        if s.startswith("let "):
            if stmt:
                m = re.match(r"let (\w+)(?: : Expr \(Fin 13\))? := (.*)$", stmt)
                name, rhs = m.group(1), m.group(2)
                env[name] = name if rhs.startswith(".var") else build(rhs, env)
            stmt = s
        else:
            stmt += " " + s
    # front13o's continuation arguments, in its order `P Q S f delta gap y t`.
    for key, src in {"P": "tau ^ 2 - ell * (ell + k)", "Q": "D ^ 2 - delta * c ^ 2",
                     "S": "delta * (b * i * c ^ 2)", "gap": "V ^ 2 - y ^ 2"}.items():
        env[key] = build(src, env)
    final_call = text[text.index("  final ", text.index("def front13o")):]
    final_call = final_call[:final_call.index("\n\n")]
    expected_call = ("final (tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) "
                     "(delta * (b * i * c ^ 2)) f delta (V ^ 2 - y ^ 2) y (b * i * c ^ 2)")
    assert " ".join(final_call.split()) == expected_call, final_call
    tail = text[text.index("front13o p fun P Q S f delta gap y _ =>"):]
    final = tail.split("=>", 1)[1].split("\n\n")[0].strip()
    return norm(build(final, env))


def main():
    raw = JSON.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    d = json.loads(raw.decode("utf-8"))
    lean = lean_tree()
    agree = lean == norm(json_tree(d))
    ok = digest == PIN and agree
    ok &= d["witnesses"] == WITNESSES
    ok &= d["operations"] == len(d["source"]) == 70 and d["exact_degree"] == 170
    counts = {op: sum(g[1] == op for g in d["source"]) for op in "*+-"}
    ok &= counts == d["operation_counts"]
    deg, bound = leading_degree(d)
    ok &= deg == 170 <= bound
    caught = 0
    for idx, (name, op, a, b) in enumerate(d["source"]):
        mutated = list(d["source"])
        mutated[idx] = [name, {"+": "*", "*": "+", "-": "+"}[op], a, b]
        caught += norm(json_tree(d, mutated)) != lean
    ok &= caught == len(d["source"])
    # The main form's single gate in place of the companion's two.
    main_src = [g for g in d["source"] if g[0] != "L"]
    main_src = [["LB", "*", "V2", "B"] if g[0] == "LB" else g for g in main_src]
    main_caught = norm(json_tree(d, main_src)) != lean
    ok &= main_caught
    print(f"positive13_oriented.json sha256 {digest} (pinned: {digest == PIN})")
    print(f"witnesses {d['witnesses']} (expected order: {d['witnesses'] == WITNESSES})")
    print(f"operations {d['operations']} = gates {len(d['source'])}, counts {counts}")
    print(f"exact degree: JSON {d['exact_degree']}, gate bound {bound}, ray degree {deg}")
    print(f"negative control: {caught}/{len(d['source'])} single-gate mutations detected")
    print(f"main-form gate (LB = V2*B) substituted: detected {main_caught}")
    print("Lean expressionAt70o and positive13_oriented.json agree modulo AC:", agree)
    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
