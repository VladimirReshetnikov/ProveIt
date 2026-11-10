"""Compare packages 183's and 192's form JSONs with their Lean syntax.

Usage: py -I -X utf8 -S -B check_forms.py

Parses the `let` chain of `ObjectCurrentEquation2011.expressionAt`
(`Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean`) and the gate list
of `183-pell-carrier65/equation/carrier65.json` into expression trees over the
14 coordinates and the port leaves (Lean `p 0..3` = JSON beta, K0, MC, MF),
normalizes both modulo associativity and commutativity of `+` and `*` (with
`x ^ n` read as an n-fold product), and checks that the two output trees are
identical. Subtraction is kept as a binary operation. The same is done for
192's `compact13/positive13_square.json` (13 / 69 / 174) against
`ModelThirteenCarrier.expressionAt69` (`front13` with its final
continuation). Every single-gate operation change is a negative control.
Finally, both packages' port bytes are checked to be the admissible942
payloads that `check_recipe.py` rebuilds from the Lean tile data.
This is a finite syntactic check outside Lean.
"""
import ast
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
LEAN = ROOT / "Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean"
JSON = ROOT / "con-zfc-diophantine-forms/183-pell-carrier65/equation/carrier65.json"
PORTS = {"0": "beta", "1": "K0", "2": "MC", "3": "MF"}


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


LEAN69 = ROOT / "Lean/DiophantineConsistency/ModelThirteenCarrier.lean"
JSON69 = ROOT / "con-zfc-diophantine-forms/192-pell-centers-fused-bounds/compact13/positive13_square.json"
PIN69 = "9574f3db6cfc549d565d278f84d7d9f0a53fec92cdcc05762c95d1e54db49c7c"
PIN = "bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7"


def json_tree(source=None, path=JSON):
    raw = path.read_bytes()
    d = json.loads(raw.decode("utf-8"))
    env = {w: w for w in d["witnesses"]}
    env.update({k: k for k in d["fixed_numerals"]})
    for name, op, a, b in (source or d["source"]):
        ta = env[a] if isinstance(a, str) else a
        tb = env[b] if isinstance(b, str) else b
        env[name] = (op, ta, tb)
    return env[d["output"]], d, hashlib.sha256(raw).hexdigest()


def let_env(lines):
    """Evaluate `let` lines (continuation lines joined) into trees."""
    env, stmt = {}, ""
    for line in lines + ["let END := 0"]:
        s = line.strip()
        if s.startswith("let "):
            if stmt:
                m = re.match(r"let (\w+)(?: : Expr \(Fin 1[34]\))? := (.*)$", stmt)
                name, rhs = m.group(1), m.group(2)
                env[name] = name if rhs.startswith(".var") else build(rhs, env)
            stmt = s
        else:
            stmt += " " + s
    return env


def check69():
    text = LEAN69.read_text(encoding="utf-8")
    body = text[text.index("def front13"):text.index("/-- The 13/69/174 polynomial. -/")]
    body = body[body.index("  let J"):body.index("  final ")]
    env = let_env([l for l in body.split("\n") if l.strip()])
    # front13's continuation arguments, in its order `P Q S f delta gap y t`.
    for key, src in {"P": "tau ^ 2 - ell * (ell + k)", "Q": "D ^ 2 - delta * c ^ 2",
                     "S": "delta * (b * i * c ^ 2)", "gap": "V ^ 2 - y ^ 2"}.items():
        env[key] = build(src, env)
    tail = text[text.index("front13 p fun P Q S f delta gap y _ =>"):]
    final = tail.split("=>", 1)[1].split("\n\n")[0].strip()
    lean = norm(build(final, env))
    js, d, digest = json_tree(path=JSON69)
    ok = digest == PIN69 and lean == norm(js)
    ok &= d["witnesses"] == ["J", "F", "alpha", "f", "i", "T", "s", "w", "n", "eta", "zeta",
                             "m", "gamma"]
    ok &= d["operations"] == len(d["source"]) == 69 and d["exact_degree"] == 174
    caught = 0
    for idx, (name, op, a, b) in enumerate(d["source"]):
        mutated = list(d["source"])
        mutated[idx] = [name, {"+": "*", "*": "+", "-": "+"}[op], a, b]
        caught += norm(json_tree(mutated, JSON69)[0]) != lean
    ok &= caught == len(d["source"])
    print(f"positive13_square.json sha256 {digest} (pinned: {digest == PIN69})")
    print(f"negative control: {caught}/{len(d['source'])} single-gate mutations detected")
    print("Lean expressionAt69 and positive13_square.json agree modulo AC:", ok)
    return ok


def check_ports():
    """Both packages' port bytes are the admissible942 payloads."""
    import gzip
    base = ROOT / "candidates/one-page-admissible942/coefficients"
    names = ["beta", "K", "MC", "MF_source"]
    ref = {n: hashlib.sha256(gzip.open(base / (n + ".bin.gz")).read()).hexdigest() for n in names}
    pkg183 = ROOT / "con-zfc-diophantine-forms/183-pell-carrier65/equation/coefficients"
    ok = all(hashlib.sha256((pkg183 / (n + ".bin")).read_bytes()).hexdigest() == ref[n] for n in names)
    pins192 = (ROOT / "con-zfc-diophantine-forms/192-pell-centers-fused-bounds/compact13/SOURCES.json"
               ).read_text(encoding="utf-8")
    ok192 = all(ref[n] in pins192 for n in names)
    print(f"183 coefficient files = admissible942 payloads: {ok}")
    print(f"192 SOURCES.json pins the admissible942 payload hashes: {ok192}")
    return ok and ok192


def main():
    text = LEAN.read_text(encoding="utf-8")
    body = text[text.index("def expressionAt"):text.index("/-- The current ports")]
    *chain, last = [l for l in body.split("\n")[1:] if l.strip()]
    env = {}
    stmt = ""
    for line in chain + [last]:
        s = line.strip()
        if s.startswith("let ") or line is last:
            if stmt:
                m = re.match(r"let (\w+)(?: : Expr \(Fin 14\))? := (.*)$", stmt)
                name, rhs = m.group(1), m.group(2)
                env[name] = name if rhs.startswith(".var") else build(rhs, env)
            stmt = s
        else:
            stmt += " " + s
    lean = norm(build(last.strip(), env))
    js, d, digest = json_tree()
    ok = digest == PIN and lean == norm(js) and d["witnesses"] == ["J", "F", "alpha", "z", "f", "i", "T", "s", "w",
                                                  "n", "eta", "zeta", "y", "gamma"]
    ok &= d["operations"] == len(d["source"]) == 65 and d["exact_degree"] == 150
    # Negative control: changing any one gate's operation must break agreement.
    caught = 0
    for idx, (name, op, a, b) in enumerate(d["source"]):
        alt = {"+": "*", "*": "+", "-": "+"}[op]
        mutated = list(d["source"])
        mutated[idx] = [name, alt, a, b]
        caught += norm(json_tree(mutated)[0]) != lean
    ok &= caught == len(d["source"])
    print(f"carrier65.json sha256 {digest} (pinned: {digest == PIN})")
    print(f"negative control: {caught}/{len(d['source'])} single-gate mutations detected")
    print("Lean expressionAt and carrier65.json agree modulo AC:", ok)
    ok = check69() and ok
    ok = check_ports() and ok
    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
