"""Compare package 188's two native circuits with their Lean syntax.

Usage: py -I -X utf8 -S -B check_forms.py [DIOPHANTINE_ROOT]

* `native/circuits/q66_d118.json` (14 positive, 66 operations, degree 118) is
  compared with `ModelCarrierCurrent.expressionAt118`
  (`Lean/DiophantineConsistency/ModelCarrierSyntax.lean`);
* `native/circuits/q67_d94.json` (14 positive, 67 operations, degree 94) is
  compared with `Carrier94Syntax.expressionAt94`
  (`Lean/DiophantineConsistency/Carrier94Syntax.lean`).

Both Lean definitions are port-parametric (`p : Fin 4 → ℤ`); Lean `p 0..3`
are the JSON leaves beta, K0, MC, MF, and the Lean coordinate order
`J F alpha z f i T s w n eta zeta y gamma` must equal the JSON witness order.

Two normal forms are used (`x ^ n` is read as an n-fold product throughout):

* **AC**: `+` and `*` flattened and sorted, `-` kept binary (as in
  `research/admissible942-calibration/tools/check_forms.py`);
* **signed sums**: every maximal `+`/`-` cluster becomes a sorted multiset of
  signed summands (`a - b = a + (-1)·b`), products flattened and sorted. No
  distribution and no cancellation of like terms is performed, so this is
  still a gate-level rearrangement, not a ring normalization.

A modular evaluation of both trees at random points with the actual
block-mask2963 ports is a third, semantic check. Every single-gate operation
change of each JSON is a negative control (it must break the signed-sum
equality). Finally the circuits' coefficient binding is checked to name the
block-mask2963 tuple whose payloads `check_recipe.py` rebuilds.
Finite syntactic evidence outside Lean, not a Lean theorem.
"""
import ast
import gzip
import hashlib
import json
import pathlib
import random
import re
import sys

HERE = pathlib.Path(__file__).resolve()


def find_root():
    if len(sys.argv) > 1 and pathlib.Path(sys.argv[1]).is_dir():
        return pathlib.Path(sys.argv[1])
    for cand in (HERE.parents[3] if len(HERE.parents) > 3 else None,):
        if cand is not None and (cand / "Lean/DiophantineConsistency/Carrier94Syntax.lean").exists():
            return cand
    raise SystemExit("cannot locate Computability/DiophantineConsistency")


ROOT = find_root()
LEANDIR = ROOT / "Lean/DiophantineConsistency"
PKG = ROOT / "con-zfc-diophantine-forms/188-pell-orientation-exact-projection/native"
PORTS = {"0": "beta", "1": "K0", "2": "MC", "3": "MF"}
COORDS = ["J", "F", "alpha", "z", "f", "i", "T", "s", "w", "n", "eta", "zeta", "y", "gamma"]
FORMS = [
    # (json, pinned sha256, Lean file, def start, def end, ops, degree)
    ("q66_d118", "0b76726f857821d5a9c08a71999c05b31f1a8e57f4a6f801bb4d4e45bf21826d",
     "ModelCarrierSyntax.lean", "def expressionAt118", "section Eval", 66, 118),
    ("q67_d94", "217460b0edbf6d9f2ea2f6d656cc4250718497c6485cffc3500c6d05e5b2c9a5",
     "Carrier94Syntax.lean", "def expressionAt94", "/-- At the maintained current ports. -/", 67, 94),
]


# ---------------------------------------------------------------- trees

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


def lean_tree(fname, start, end):
    text = (LEANDIR / fname).read_text(encoding="utf-8")
    body = text[text.index(start):]
    body = body[:body.index(end)]
    lines = [l for l in body.split("\n")[1:] if l.strip()]
    stmts = []
    for line in lines:
        indent = len(line) - len(line.lstrip(" "))
        if indent == 2 or not stmts:   # a new body statement; deeper lines continue it
            stmts.append(line.strip())
        else:
            stmts[-1] += " " + line.strip()
    env, coords = {}, []
    for s in stmts[:-1]:
        m = re.match(r"let (\w+)(?: : Expr \(Fin 14\))? := (.*)$", s)
        name, rhs = m.group(1), m.group(2)
        if rhs.startswith(".var"):
            coords.append((int(rhs.split()[1]), name))
            env[name] = name
        else:
            env[name] = build(rhs, env)
    return build(stmts[-1], env), [n for _, n in sorted(coords)]


def json_tree(d, source=None):
    env = {w: w for w in d["witnesses"]}
    env.update({k: k for k in d["fixed_numerals"]})
    for name, op, a, b in (source or d["source"]):
        ta = env[a] if isinstance(a, str) else a
        tb = env[b] if isinstance(b, str) else b
        env[name] = (op, ta, tb)
    return env[d["output"]]


def norm_ac(t):
    if isinstance(t, tuple) and t[0] in "+*":
        args = []
        for a in t[1:]:
            a = norm_ac(a)
            if isinstance(a, tuple) and a[0] == t[0]:
                args.extend(a[1])
            else:
                args.append(a)
        return (t[0], tuple(sorted(args, key=repr)))
    if isinstance(t, tuple) and t[0] == "-":
        return ("-", norm_ac(t[1]), norm_ac(t[2]))
    return t


def norm_signed(t):
    """Signed-sum normal form (no distribution, no cancellation)."""
    if isinstance(t, tuple) and t[0] in "+-":
        terms = []

        def collect(u, sign):
            if isinstance(u, tuple) and u[0] == "+":
                for a in u[1:]:
                    collect(a, sign)
            elif isinstance(u, tuple) and u[0] == "-":
                collect(u[1], sign)
                collect(u[2], -sign)
            else:
                terms.append((sign, norm_signed(u)))
        collect(t, 1)
        return ("S", tuple(sorted(terms, key=repr)))
    if isinstance(t, tuple) and t[0] == "*":
        args = []
        for a in t[1:]:
            a = norm_signed(a)
            if isinstance(a, tuple) and a[0] == "P":
                args.extend(a[1])
            else:
                args.append(a)
        return ("P", tuple(sorted(args, key=repr)))
    return t


def evaluate(t, val, mod):
    if isinstance(t, tuple):
        op = t[0]
        xs = [evaluate(a, val, mod) for a in t[1:]]
        if op == "+":
            return sum(xs) % mod
        if op == "-":
            return (xs[0] - xs[1]) % mod
        r = 1
        for x in xs:
            r = r * x % mod
        return r
    if isinstance(t, int):
        return t % mod
    return val[t] % mod


def payload(name):
    return int.from_bytes(gzip.decompress((PKG / "coefficients" / name).read_bytes()), "big")


def main():
    ok = True
    ports = {"beta": payload("beta.bin.gz"), "K0": payload("K.bin.gz"),
             "MC": payload("MC.bin.gz"), "MF": payload("MF_source.bin.gz")}
    sys.path.insert(0, str(HERE.parent))
    try:
        import check_recipe  # noqa: E402  (same directory)
        rebuilt, _, _ = check_recipe.recipe(check_recipe.coefficients(check_recipe.lean_tiles()))
        same = (rebuilt["beta"], rebuilt["K"], rebuilt["MC"], rebuilt["MF_source"]) == (
            ports["beta"], ports["K0"], ports["MC"], ports["MF"])
        print(f"package 188 payloads == block-mask2963 recipe from WangTiles942.tile: {same}")
        ok &= same
    except ImportError:
        print("check_recipe.py not found next to this file; port rebuild skipped")
    rng = random.Random(20261107)
    mods = [(1 << 61) - 1, 1000000007, 998244353]
    for name, pin, fname, start, end, nops, deg in FORMS:
        raw = (PKG / "circuits" / (name + ".json")).read_bytes()
        d = json.loads(raw.decode("utf-8"))
        digest = hashlib.sha256(raw).hexdigest()
        lean, coords = lean_tree(fname, start, end)
        js = json_tree(d)
        ac = norm_ac(lean) == norm_ac(js)
        signed = norm_signed(lean) == norm_signed(js)
        sem = True
        for mod in mods:
            for _ in range(4):
                val = {w: rng.randrange(1, mod) for w in COORDS}
                val.update({k: v % mod for k, v in ports.items()})
                sem &= evaluate(lean, val, mod) == evaluate(js, val, mod)
        caught = 0
        for idx, (n, op, a, b) in enumerate(d["source"]):
            mutated = list(d["source"])
            mutated[idx] = [n, {"+": "*", "*": "+", "-": "+"}[op], a, b]
            caught += norm_signed(json_tree(d, mutated)) != norm_signed(lean)
        meta = (d["witnesses"] == COORDS == coords and d["fixed_numerals"] == ["beta", "K0", "MC", "MF"]
                and d["operations"] == len(d["source"]) == nops and d["exact_degree"] == deg
                and d["coefficient_binding"]["tuple"] == "one-page-block-mask2963")
        print(f"{name}.json sha256 {digest} (pinned in native/MANIFEST.json: {digest == pin})")
        print(f"  Lean {fname} `{start[4:]}`: coordinates {coords == COORDS}, metadata {meta}")
        print(f"  AC-normal (binary '-') equal: {ac}; signed-sum normal equal: {signed}; "
              f"modular evaluation at 12 random points with the actual ports equal: {sem}")
        print(f"  negative control: {caught}/{len(d['source'])} single-gate mutations detected")
        ok &= digest == pin and meta and signed and sem and caught == len(d["source"])
    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
