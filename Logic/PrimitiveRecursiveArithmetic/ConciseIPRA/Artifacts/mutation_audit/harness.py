"""Mutation search for smaller equivalent stream checkers.

usage: harness.py <control.py> <fixture-dir> [<fixture-dir> ...]

Every single-step AST reduction of the control is run in-process on the fixture streams and
on random mutations of them, and compared with the control (ACCEPT / reject).  Mutants that
never differ are printed with their sizes.  Nothing is written outside this script's output.
"""
import ast, copy, io, json, os, random, sys, tokenize

SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(text):
    tok = sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(text).readline))
    nodes = sum(1 for _ in ast.walk(ast.parse(text)))
    return tok, nodes, len(text.encode())


def run(code, lines):
    if WHOLE:
        lines = ["[" + ",".join(lines) + "]"]
    it = iter(lines)
    out = []

    def inp(*a):
        try:
            return next(it)
        except StopIteration:
            raise EOFError

    def op(*a, **k):
        return io.StringIO("\n".join(lines))

    env = {"input": inp, "open": op, "print": lambda *a, **k: out.append(a), "__name__": "__main__"}
    try:
        exec(code, env)
    except BaseException as e:  # every exception is a rejection
        if isinstance(e, (KeyboardInterrupt, MemoryError)):
            raise
        return False
    return out == [("ACCEPT",)]


class Reducer(ast.NodeTransformer):
    """Apply the k-th applicable reduction; count the applicable ones."""

    def __init__(self, k):
        self.k = k
        self.n = 0

    def pick(self, alts, node):
        for a in alts:
            if self.n == self.k:
                self.n += 1
                return a
            self.n += 1
        return None

    def generic_visit(self, node):
        alts = []
        if isinstance(node, ast.BoolOp):
            for j in range(len(node.values)):
                rest = node.values[:j] + node.values[j + 1:]
                alts.append(rest[0] if len(rest) == 1 else ast.BoolOp(node.op, rest))
        elif isinstance(node, ast.IfExp):
            alts += [node.body, node.orelse,
                     ast.BoolOp(ast.And(), [node.test, node.body]),
                     ast.BoolOp(ast.Or(), [node.test, node.orelse]),
                     ast.BoolOp(ast.And(), [node.test, node.orelse]),
                     ast.BoolOp(ast.Or(), [node.test, node.body])]
        elif isinstance(node, ast.BinOp):
            alts += [node.left, node.right]
        elif isinstance(node, ast.UnaryOp):
            alts += [node.operand]
        elif isinstance(node, ast.Compare):
            alts += [node.left] + list(node.comparators)
            if len(node.ops) > 1:
                for j in range(len(node.ops)):
                    ops = node.ops[:j] + node.ops[j + 1:]
                    for cs in (node.comparators[:j] + node.comparators[j + 1:],):
                        alts.append(ast.Compare(node.left, ops, cs))
                    if j == 0:
                        alts.append(ast.Compare(node.comparators[0], node.ops[1:], node.comparators[1:]))
        elif isinstance(node, ast.Call):
            alts += list(node.args) + [k.value for k in node.keywords]
            for j in range(len(node.args)):
                alts.append(ast.Call(node.func, node.args[:j] + node.args[j + 1:], node.keywords))
            for j in range(len(node.keywords)):
                alts.append(ast.Call(node.func, node.args, node.keywords[:j] + node.keywords[j + 1:]))
            for j in range(len(node.keywords)):
                alts.append(ast.Call(node.func, node.args + [node.keywords[j].value],
                                     node.keywords[:j] + node.keywords[j + 1:]))
        elif isinstance(node, ast.Subscript):
            alts += [node.value]
        elif isinstance(node, ast.Starred) and isinstance(node.ctx, ast.Load):
            alts += [node.value]
        elif isinstance(node, (ast.List, ast.Tuple)) and isinstance(node.ctx, ast.Load):
            for j in range(len(node.elts)):
                alts.append(type(node)(node.elts[:j] + node.elts[j + 1:], ast.Load()))
            if len(node.elts) == 1 and not isinstance(node.elts[0], ast.Starred):
                alts.append(node.elts[0])
        elif isinstance(node, ast.NamedExpr):
            alts += [node.value]
        elif isinstance(node, ast.ListComp):
            alts += [node.elt, node.generators[0].iter]
        elif isinstance(node, ast.Assign) and len(node.targets) > 1:
            for j in range(len(node.targets)):
                alts.append(ast.Assign(node.targets[:j] + node.targets[j + 1:], node.value))
        elif isinstance(node, ast.arguments) and node.defaults:
            for j in range(len(node.defaults)):
                if j == 0:  # only the first default can be dropped syntactically
                    a = copy.copy(node)
                    a.defaults = node.defaults[1:]
                    alts.append(a)
        elif isinstance(node, ast.If):
            alts += [ast.If(ast.Constant(1), node.body, node.orelse)]
        got = self.pick(alts, node)
        if got is not None:
            return ast.copy_location(got, node) if hasattr(node, "lineno") else got
        # statement deletion in bodies
        for field in ("body", "orelse"):
            body = getattr(node, field, None)
            if isinstance(body, list) and len(body) > 1 and all(isinstance(b, ast.stmt) for b in body):
                for j in range(len(body)):
                    if self.n == self.k:
                        self.n += 1
                        new = copy.copy(node)
                        setattr(new, field, body[:j] + body[j + 1:])
                        return new
                    self.n += 1
        return super().generic_visit(node)


def mutants(src):
    tree = ast.parse(src)
    k = 0
    seen = set()
    while True:
        r = Reducer(k)
        new = r.visit(copy.deepcopy(tree))
        if r.n <= k:
            break
        k += 1
        try:
            ast.fix_missing_locations(new)
            text = ast.unparse(new) + "\n"
            compile(text, "<m>", "exec")
        except Exception:
            continue
        if text not in seen:
            seen.add(text)
            yield text


def perturb(lines, rng):
    lines = list(lines)
    if rng.random() < 0.25:
        try:
            vs = [json.loads(l) for l in lines]
        except Exception:
            return lines
        sc = set()
        def col(x):
            if isinstance(x, list):
                for y in x: col(y)
            elif isinstance(x, int): sc.add(x)
        for v in vs: col(v)
        if not sc: return lines
        a = rng.choice(sorted(sc)); b = rng.choice(sorted(sc) + [0, 0, -1, -2, 3, 5])
        first = rng.randrange(len(vs))
        def sub(x):
            if isinstance(x, list): return [sub(y) for y in x]
            return b if x == a and not isinstance(x, bool) else x
        return [json.dumps(sub(v)) if q >= first else l for q, (v, l) in enumerate(zip(vs, lines))]
    j = rng.randrange(len(lines))
    op = rng.randrange(8)
    try:
        v = json.loads(lines[j])
    except Exception:
        return lines

    def paths(x, p=()):
        yield p
        if isinstance(x, list):
            for q, y in enumerate(x):
                yield from paths(y, p + (q,))

    ps = list(paths(v))
    p = rng.choice(ps)

    def get(x, p):
        for q in p:
            x = x[q]
        return x

    def put(x, p, y):
        if not p:
            return y
        z = x
        for q in p[:-1]:
            z = z[q]
        z[p[-1]] = y
        return x

    cur = get(v, p)
    if op == 0 and isinstance(cur, int):
        v = put(v, p, cur + rng.choice([-2, -1, 1, 2]))
    elif op == 1:
        v = put(v, p, rng.choice([0, 1, 2, 3, 4, 5, 7, -1, -2, [], [0], [[]], [0, 0], [3], True, None, 0.5]))
    elif op == 2 and isinstance(cur, list) and cur:
        del cur[rng.randrange(len(cur))]
    elif op == 3 and isinstance(cur, list):
        cur.insert(rng.randrange(len(cur) + 1), rng.choice([0, 3, 5, [], [0], -1]))
    elif op == 4 and len(lines) > 1:
        del lines[j]
        return lines
    elif op == 5:
        lines.insert(j, lines[rng.randrange(len(lines))])
        return lines
    elif op == 6 and len(lines) > 2:
        a, b = rng.randrange(len(lines)), rng.randrange(len(lines))
        lines[a], lines[b] = lines[b], lines[a]
        return lines
    elif op == 7:
        v = put(v, p, [cur])
    lines[j] = json.dumps(v)
    return lines


WHOLE = os.environ.get("WHOLE") == "1"
EXT = ".json" if WHOLE else ".jsonl"


def main():
    control = open(sys.argv[1], encoding="utf-8").read()
    control = ast.unparse(ast.parse(control)) + "\n"
    base = []
    for d in sys.argv[2:]:
        for dp, dn, fn in os.walk(d):
            for f in sorted(fn):
                if f.endswith(EXT) and os.path.getsize(os.path.join(dp, f)) < 20000:
                    txt = open(os.path.join(dp, f), encoding="utf-8").read()
                    if WHOLE:
                        try:
                            v = json.loads(txt)
                        except Exception:
                            continue
                        if not isinstance(v, list) or not v:
                            continue
                        base.append([json.dumps(x) for x in v])
                    else:
                        base.append(txt.split("\n"))
    base = [[l for l in b if l.strip()] for b in base]
    base = [b for b in base if b]
    rng = random.Random(1)
    corpus = list(base)
    pos = [b for b in base if run(control, b)]
    for _ in range(int(os.environ.get("NMUT", "4000"))):
        b = list(rng.choice(pos if rng.random() < 0.8 else base))
        for _ in range(rng.choice([1, 1, 1, 2, 3])):
            b = perturb(b, rng)
        corpus.append(b)
    sys.setrecursionlimit(3000)
    cc = compile(control, "<c>", "exec")
    ref = [run(cc, b) for b in corpus]
    print("control", measure(control), "streams", len(corpus), "accepted", sum(ref), "base", len(base),
          "base accepted", len(pos), flush=True)
    n = 0
    for text in mutants(control):
        n += 1
        try:
            mc = compile(text, "<m>", "exec")
        except Exception:
            continue
        ok = True
        for b, r in zip(corpus, ref):
            if run(mc, b) != r:
                ok = False
                break
        if ok:
            import difflib
            d = [l for l in difflib.unified_diff(control.split(chr(10)), text.split(chr(10)), lineterm="", n=0) if l[:1] in "+-" and l[:3] not in ("+++", "---")]
            print("SURVIVOR", measure(text), " | ".join(x.strip() for x in d), flush=True)
    print("mutants", n)


main()
