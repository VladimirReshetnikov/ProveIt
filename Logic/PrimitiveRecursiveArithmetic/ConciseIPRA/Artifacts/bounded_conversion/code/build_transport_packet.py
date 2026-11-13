"""Build a complete finite certificate for derived crossed transport.

The producer uses named variables; only the standalone checker is trusted.
Its result is an open sequent with three numerical parameters, s, t, r:
    s=t, S(s)=r |- r=S(t).
"""
import importlib.util
import json
from itertools import count
from pathlib import Path

ROOT = Path(__file__).parent
SERIAL = count()


def fresh(prefix):
    return prefix + str(next(SERIAL))


def var(x):
    return ("v", x)


ZERO = ("z",)


def succ(t):
    return ("s", t)


def itr(n, a, u, body):
    return ("i", n, a, u, body)


def eq(a, b):
    return ("=", a, b)


def sel(n, a, b):
    return itr(n, a, fresh("ignored"), b)


def parity(n):
    u = fresh("state")
    return itr(n, ZERO, u, sel(var(u), succ(ZERO), ZERO))


def subst(a, name, value):
    tag = a[0]
    if tag == "v":
        return value if a[1] == name else a
    if tag == "z":
        return a
    if tag in ("s",):
        return (tag, subst(a[1], name, value))
    if tag == "=":
        return eq(subst(a[1], name, value), subst(a[2], name, value))
    if tag == "i":
        _, n, seed, u, h = a
        return itr(subst(n, name, value), subst(seed, name, value), u,
                   h if u == name else subst(h, name, value))
    if tag == "q":
        return a if a[1] == name else (tag, a[1], subst(a[2], name, value))
    if tag == "d":
        return a if name in a[1:3] else (tag, a[1], a[2], subst(a[3], name, value))
    raise ValueError(tag)


def compile_syntax(a, env):
    tag = a[0]
    if tag == "v":
        return [tag, env[::-1].index(a[1])]
    if tag == "z":
        return [tag]
    if tag == "s":
        return [tag, compile_syntax(a[1], env)]
    if tag == "=":
        return [tag, compile_syntax(a[1], env), compile_syntax(a[2], env)]
    if tag == "i":
        return [tag, compile_syntax(a[1], env), compile_syntax(a[2], env),
                compile_syntax(a[4], env + [a[3]])]
    if tag == "q":
        return [tag, compile_syntax(a[2], env + [a[1]])]
    if tag == "d":
        return [tag, compile_syntax(a[3], env + [a[1], a[2]])]
    raise ValueError(tag)


def compile_proof(p, env):
    if not p:
        return []
    tag = p[0]
    if tag == "cv":
        _, redex, depth, branch = p
        return [tag, compile_syntax(redex, env), depth, compile_proof(branch, env)]
    if tag == "vs":
        _, x, t, u, left, right = p
        return [tag, env[::-1].index(x), compile_syntax(t, env),
                compile_syntax(u, env), compile_proof(left, env), compile_proof(right, env)]
    if tag == "qe":
        _, y, body, t, left, right = p
        return [tag, compile_syntax(body, env + [y]), compile_syntax(t, env),
                compile_proof(left, env), compile_proof(right, env)]
    if tag == "de":
        _, x, y, body, b, major, branch = p
        return [tag, compile_syntax(body, env + [x, y]), compile_proof(major, env),
                compile_proof(branch, env + [b])]
    if tag == "di":
        _, t, z, branch = p
        return [tag, compile_syntax(t, env), compile_proof(branch, env + [z])]
    raise ValueError(tag)


def symmetry(theorem):
    left, right, p = theorem
    x, y, b, z = [fresh(v) for v in ("dummy_x", "dummy_y", "dummy_b", "dummy_z")]
    major = ("di", ZERO, z, ())
    branch = ("vs", b, var(b), left, (), p)
    return right, left, ("de", x, y, eq(ZERO, ZERO), b, major, branch)


def change_left(theorem, value, redex, depth):
    left, right, p = theorem
    return value, right, ("cv", redex, depth, p)


def change_right(theorem, value, redex, depth):
    return symmetry(change_left(symmetry(theorem), value, redex, depth))


def head_step(a):
    if a[0] != "i":
        return None
    _, n, seed, u, h = a
    if n == ZERO:
        return seed, 0
    if n[0] == "s":
        return subst(h, u, itr(n[1], seed, u, h)), 0
    result = head_step(n)
    if result is None:
        return None
    return itr(result[0], seed, u, h), result[1] + 1


def path(start, finish):
    steps = []
    current = start
    for _ in range(12):
        if compile_syntax(current, free_environment(current, finish)) == compile_syntax(finish, free_environment(current, finish)):
            return steps
        result = head_step(current)
        if result is None:
            raise AssertionError((current, finish))
        after, depth = result
        assert depth <= 3
        steps.append((current, after, depth))
        current = after
    raise AssertionError("Displayed trace exceeded its fixed budget")


def free_vars(a, bound=frozenset()):
    tag = a[0]
    if tag == "v":
        return set() if a[1] in bound else {a[1]}
    if tag == "z":
        return set()
    if tag == "s":
        return free_vars(a[1], bound)
    if tag == "=":
        return free_vars(a[1], bound) | free_vars(a[2], bound)
    if tag == "i":
        return (free_vars(a[1], bound) | free_vars(a[2], bound) |
                free_vars(a[4], bound | {a[3]}))
    if tag == "q":
        return free_vars(a[2], bound | {a[1]})
    if tag == "d":
        return free_vars(a[3], bound | {a[1], a[2]})
    raise ValueError(tag)


def free_environment(a, b):
    return sorted(free_vars(a) | free_vars(b))


def wrap_equation(theorem, goal):
    """Turn proofs of computed payloads into proofs of raw selector rows."""
    left, right, _ = theorem
    for before, after, depth in reversed(path(goal[1], left)):
        theorem = change_left(theorem, before, before, depth)
    for before, after, depth in reversed(path(goal[2], right)):
        theorem = change_right(theorem, before, before, depth)
    return theorem


def reduce_equation(theorem, goal):
    left, right, _ = theorem
    for before, after, depth in path(left, goal[1]):
        theorem = change_left(theorem, after, before, depth)
    for before, after, depth in path(right, goal[2]):
        theorem = change_right(theorem, after, before, depth)
    return theorem


def build():
    s, t, r = map(var, ("s", "t", "r"))
    x, y, z, b, w, unused, opened = [fresh(v) for v in
                                    ("x", "y", "z", "b", "w", "unused", "opened")]
    # The matrix keeps its bound names consistent throughout instantiation.
    p_y = parity(var(y))
    pi = eq(sel(var(y), ZERO, sel(p_y, var(x), succ(var(x)))),
            sel(var(y), ZERO, sel(p_y, t, r)))
    f = eq(sel(var(y), s, succ(s)), sel(var(y), t, r))

    # Independent equation cases prove F(P(Sz)).
    base = wrap_equation((s, t, ()), subst(f, y, ZERO))
    step = wrap_equation((succ(s), r, ()), subst(f, y, succ(var(w))))
    q_major = ("di", ZERO, w, step[2])
    q_proof = ("de", unused, y, f, opened, q_major, ())
    p_sz = subst(p_y, y, succ(var(z)))
    f_at = subst(f, y, p_sz)
    f_proof = ("qe", y, f, p_sz, q_proof, base[2])
    target = subst(subst(pi, x, s), y, succ(var(z)))
    intro_branch = wrap_equation((f_at[1], f_at[2], f_proof), target)
    major = ("di", s, z, intro_branch[2])

    # Open D Pi; Q's two fixed rows yield S(b)=r and b=t.
    pi_b = subst(pi, x, var(b))
    zero_row = wrap_equation((ZERO, ZERO, ()), subst(pi_b, y, ZERO))
    one, two = succ(ZERO), succ(succ(ZERO))
    row1 = subst(pi_b, y, one)
    row2 = subst(pi_b, y, two)
    row1_proof = ("qe", y, pi_b, one, (), zero_row[2])
    row2_proof = ("qe", y, pi_b, two, (), zero_row[2])
    minor = reduce_equation((row1[1], row1[2], row1_proof), eq(succ(var(b)), r))
    equality = reduce_equation((row2[1], row2[2], row2_proof), eq(var(b), t))
    branch = ("vs", b, t, succ(var(b)), equality[2], minor[2])
    proof = ("de", x, y, pi, b, major, branch)

    env = ["s", "t", "r"]
    return {"variables": len(env),
            "context": [compile_syntax(eq(s, t), env), compile_syntax(eq(succ(s), r), env)],
            "goal": compile_syntax(eq(r, succ(t)), env),
            "proof": compile_proof(proof, env)}


if __name__ == "__main__":
    certificate = build()
    spec = importlib.util.spec_from_file_location("bounded_checker", ROOT / "checker.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.check(certificate)
    target = ROOT / "fixtures" / "transport_packet.json"
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
    print(f"Verified transport packet; {target.stat().st_size} certificate bytes.")
