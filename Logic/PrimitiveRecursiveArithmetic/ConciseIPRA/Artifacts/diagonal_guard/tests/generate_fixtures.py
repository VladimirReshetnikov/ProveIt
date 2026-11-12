"""Untrusted named-syntax certificate producer, independent of the checkers.

The compiled certificates use explicit de Bruijn indices.  Named binders in
this producer are only a convenience for constructing readable derivations;
none of the three standalone kernels imports this module.
"""
from dataclasses import dataclass
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NAMES = itertools.count()


def fresh(prefix="n"):
    return f"{prefix}_{next(NAMES)}"


def S(t):
    return ("s", t)


def I(n, a, u, h):
    return ("i", n, a, u, h)


def Eq(s, t):
    return ("=", s, t)


def Q(y, b):
    return ("q", y, b)


def D(x, y, b):
    return ("d", x, y, b)


def replace(a, variable, image):
    if a == variable:
        return image
    if not isinstance(a, tuple):
        return a
    tag = a[0]
    if tag == "i":
        _, n, seed, u, h = a
        return I(replace(n, variable, image), replace(seed, variable, image),
                 u, h if u == variable else replace(h, variable, image))
    if tag == "q":
        _, y, b = a
        return Q(y, b if y == variable else replace(b, variable, image))
    if tag == "d":
        _, x, y, b = a
        return D(x, y, b if variable in (x, y) else replace(b, variable, image))
    return (tag,) + tuple(replace(b, variable, image) for b in a[1:])


def alpha(a, env=()):
    if a == 0:
        return 0
    if isinstance(a, str):
        return ("bound", env.index(a)) if a in env else ("free", a)
    if a[0] == "i":
        return ("i", alpha(a[1], env), alpha(a[2], env), alpha(a[4], (a[3],) + env))
    if a[0] == "q":
        return ("q", alpha(a[2], (a[1],) + env))
    if a[0] == "d":
        return ("d", alpha(a[3], (a[2], a[1]) + env))
    return (a[0],) + tuple(alpha(x, env) for x in a[1:])


def same(a, b):
    return alpha(a) == alpha(b)


def term(t, env=()):
    if t == 0:
        return ["z"]
    if isinstance(t, str):
        return ["v", env.index(t)]
    if t[0] == "s":
        return ["s", term(t[1], env)]
    _, n, a, u, h = t
    return ["i", term(n, env), term(a, env), term(h, (u,) + env)]


def formula(f, env=()):
    if f[0] == "=":
        return ["=", term(f[1], env), term(f[2], env)]
    if f[0] == "q":
        return ["q", formula(f[2], (f[1],) + env)]
    _, x, y, b = f
    return ["d", formula(b, (y, x) + env)]


@dataclass(frozen=True)
class Proof:
    conclusion: tuple
    node: tuple


def hyp(label, f):
    return Proof(f, ("hyp", label))


def zero(a, u, h):
    return Proof(Eq(I(0, a, u, h), a), ("zero", a, u, h))


def succ(n, a, u, h):
    return Proof(Eq(I(S(n), a, u, h), replace(h, u, I(n, a, u, h))),
                 ("succ", n, a, u, h))


def tr(v, left, right, major, minor):
    assert major.conclusion[0] == "="
    s, t = major.conclusion[1:]
    assert same(minor.conclusion, Eq(replace(left, v, s), replace(right, v, s)))
    return Proof(Eq(replace(left, v, t), replace(right, v, t)),
                 ("tr", v, left, right, major, minor))


def refl(t):
    u, v = fresh("refl_state"), fresh("refl_hole")
    p = zero(t, u, 0)
    return tr(v, v, t, p, p)


def symmetry(p):
    v = fresh("symmetry_hole")
    s, _ = p.conclusion[1:]
    return tr(v, v, s, p, refl(s))


def trans(p, q):
    assert same(p.conclusion[2], q.conclusion[1])
    v = fresh("transitivity_hole")
    return tr(v, p.conclusion[1], v, q, p)


def congruence(v, t, p):
    s, _ = p.conclusion[1:]
    start = replace(t, v, s)
    return tr(v, start, t, p, refl(start))


def qe(t, major, base):
    assert major.conclusion[0] == "q"
    _, y, b = major.conclusion
    assert same(base.conclusion, replace(b, y, 0))
    return Proof(replace(b, y, t), ("qe", t, major, base))


def de(conclusion, major, continuation):
    _, x, y, b = major.conclusion
    eigen, label = fresh("existential"), fresh("closure_hyp")
    q = hyp(label, Q(y, replace(b, x, eigen)))
    body = continuation(eigen, q)
    assert same(body.conclusion, conclusion)
    return Proof(conclusion, ("de", major, eigen, label, q.conclusion, body))


def guarded(b, y):
    return (b[0] == "=" and all(isinstance(t, tuple) and t[0] == "i"
                                  and t[1] == y and t[2] == y for t in b[1:]))


def guard_zero(b, y):
    assert guarded(b, y)
    s, t = (replace(v, y, 0) for v in b[1:])
    p, q = zero(s[2], s[3], s[4]), zero(t[2], t[3], t[4])
    return trans(p, symmetry(q))


def raw_di(x, y, b, witness, mode, step):
    z, label = fresh("successor"), fresh("intro_hyp")
    a = replace(b, x, witness)
    assumption = replace(a, y, z if mode == "progress" else 0)
    h = hyp(label, assumption)
    body = step(z, h)
    assert same(body.conclusion, replace(a, y, S(z)))
    return Proof(D(x, y, b), ("di", x, y, b, witness, z, label, assumption, body))


def case_di(x, y, b, witness, step):
    a = replace(b, x, witness)
    if guarded(a, y):
        return raw_di(x, y, b, witness, "progress", lambda z, _: step(z, guard_zero(a, y)))
    return raw_di(x, y, b, witness, "case", step)


def case_q(y, b, step):
    x = fresh("unused_witness")
    p = case_di(x, y, b, 0, step)
    return de(Q(y, b), p, lambda _x, h: h)


def cases(y, b, target, base, successor):
    assert same(base.conclusion, replace(b, y, 0))
    return qe(target, case_q(y, b, lambda z, _h: successor(z)), base)


def gate(y, s, t):
    return Eq(I(y, 0, "gate_left_state", s), I(y, 0, "gate_right_state", t))


def gate_zero(s, t):
    return trans(zero(0, "gate_left_state", s), symmetry(zero(0, "gate_right_state", t)))


def gate_positive(n, p):
    s, t = p.conclusion[1:]
    left = succ(n, 0, "gate_left_state", s)
    right = succ(n, 0, "gate_right_state", t)
    return trans(left, trans(p, symmetry(right)))


def ungate_positive(n, s, t, p):
    left = succ(n, 0, "gate_left_state", s)
    right = succ(n, 0, "gate_right_state", t)
    return trans(symmetry(left), trans(p, right))


def explode(a, b, contradiction):
    v, u = fresh("counter_hole"), fresh("constant_state")
    p = tr(v, I(v, a, u, b), a, contradiction, zero(a, u, b))
    return trans(symmetry(p), succ(0, a, u, b))


def identity(t):
    return I(t, 0, "identity_state", S("identity_state"))


def diagonal_identity(t):
    return Eq(I(t, t, "diagonal_left_state", identity(t)),
              I(t, t, "diagonal_right_state", t))


def collapse(y, t, target, zero_proof, state):
    """I(y,y;constant t(y))=t(y), given the separate theorem t(0)=0."""
    lhs = I(y, y, state, t)
    matrix = Eq(lhs, t)
    base = trans(zero(0, state, replace(t, y, 0)), symmetry(zero_proof))
    return cases(y, matrix, target, base,
                 lambda z: succ(z, S(z), state, replace(t, y, S(z))))


def identity_step(z, h):
    v = fresh("successor_congruence")
    return trans(succ(z, 0, "identity_state", S("identity_state")),
                 congruence(v, S(v), h))


def guarded_identity_pair():
    x, y = fresh("unused"), fresh("index")
    b = diagonal_identity(y)

    def step(z, h):
        left = collapse(y, identity(y), z, zero(0, "identity_state", S("identity_state")),
                        "diagonal_left_state")
        right = collapse(y, y, z, refl(0), "diagonal_right_state")
        old = trans(symmetry(left), trans(h, right))
        new = identity_step(z, old)
        outer_left = succ(z, S(z), "diagonal_left_state", identity(S(z)))
        outer_right = succ(z, S(z), "diagonal_right_state", S(z))
        return trans(outer_left, trans(new, symmetry(outer_right)))

    return raw_di(x, y, b, 0, "progress", step)


def identity_closure():
    major = guarded_identity_pair()
    y = fresh("identity_index")
    conclusion = Q(y, Eq(identity(y), y))

    def continuation(_eigen, h):
        _, qvar, b = h.conclusion

        def step(z, _base):
            lifted = qe(S(z), h, guard_zero(b, qvar))
            left = succ(z, S(z), "diagonal_left_state", identity(S(z)))
            right = succ(z, S(z), "diagonal_right_state", S(z))
            return trans(symmetry(left), trans(lifted, right))

        return case_q(y, Eq(identity(y), y), step)

    return de(conclusion, major, continuation)


def native_identity_closure():
    y, z, label = fresh("native_index"), fresh("native_successor"), fresh("native_induction_hyp")
    matrix = Eq(identity(y), y)
    assumption = Eq(identity(z), z)
    body = identity_step(z, hyp(label, assumption))
    return Proof(Q(y, matrix), ("qi", y, matrix, z, label, assumption, body))


def nonvacuous_elimination():
    x, y = fresh("witness"), fresh("gate_index")
    a = S(0)
    major = case_di(x, y, gate(y, x, a), a,
                    lambda z, _h: gate_positive(z, refl(a)))
    w, v = fresh("output_witness"), fresh("output_gate_index")
    conclusion = D(w, v, gate(v, w, S(a)))

    def continuation(eigen, h):
        eq = ungate_positive(0, eigen, a, qe(S(0), h, gate_zero(eigen, a)))
        hole = fresh("successor_hole")
        advanced = congruence(hole, S(hole), eq)
        return case_di(w, v, gate(v, w, S(a)), S(eigen),
                        lambda z, _h: gate_positive(z, advanced))

    return de(conclusion, major, continuation)


def compile_proof(p, env=(), context=()):
    tag, *fields = p.node
    if tag == "hyp":
        label, = fields
        for i, (name, f) in enumerate(context):
            if name == label:
                assert same(f, p.conclusion)
                return ["hyp", i]
        raise ValueError(f"Missing assumption {label}")
    if tag == "zero":
        a, u, h = fields
        return ["zero", term(a, env), term(h, (u,) + env)]
    if tag == "succ":
        n, a, u, h = fields
        return ["succ", term(n, env), term(a, env), term(h, (u,) + env)]
    if tag == "tr":
        v, left, right, major, minor = fields
        return ["tr", term(left, (v,) + env), term(right, (v,) + env),
                compile_proof(major, env, context), compile_proof(minor, env, context)]
    if tag == "qe":
        t, major, base = fields
        return ["qe", term(t, env), compile_proof(major, env, context), compile_proof(base, env, context)]
    if tag == "de":
        major, eigen, label, assumption, body = fields
        return ["de", formula(p.conclusion, env), compile_proof(major, env, context),
                compile_proof(body, (eigen,) + env, ((label, assumption),) + context)]
    if tag == "di":
        x, y, b, witness, z, label, assumption, body = fields
        return ["di", formula(b, (y, x) + env), term(witness, env),
                compile_proof(body, (z,) + env, ((label, assumption),) + context)]
    if tag == "qi":
        y, b, z, label, assumption, body = fields
        return ["qi", formula(b, (y,) + env),
                compile_proof(body, (z,) + env, ((label, assumption),) + context)]
    raise ValueError(tag)


def certificate(p, env=(), context=()):
    return {"variables": len(env), "context": [formula(f, env) for _, f in context],
            "goal": formula(p.conclusion, env), "proof": compile_proof(p, env, context)}


def build():
    directory = ROOT / "certificates"
    directory.mkdir(exist_ok=True)
    result = []

    def add(name, p, expected, note, env=(), context=()):
        data = certificate(p, env, context)
        (directory / f"{name}.json").write_text(json.dumps(data, separators=(",", ":")) + "\n")
        result.append({"file": f"{name}.json", "expected": expected, "note": note})

    yes = {"native": True, "diagonal": True, "witness": True}
    add("zero_computation", zero(S(0), "u", S("u")), yes, "State-aware zero computation.")
    add("successor_computation", succ(S(0), S(0), "u", I("u", S("u"), "v", S("v"))),
        yes, "A nested iterator update, with its own bound state.")
    nested = I(S(S(0)), S(0), "u", I("u", S("u"), "v", S("v")))
    add("nested_reflexivity", refl(nested), yes, "Derived equality reflexivity, without a primitive reflexivity rule.")
    add("guarded_progress_used_hypothesis", guarded_identity_pair(),
        {"native": False, "diagonal": True, "witness": True},
        "The induction hypothesis supplies the equality needed by the successor computation; replacing it by the zero instance fails.")
    add("identity_closure", identity_closure(),
        {"native": False, "diagonal": True, "witness": True},
        "Q_y(I(y,0;Su)=y) is derived from a diagonal-guard induction and conditional closure rules.")
    add("identity_at_nested_term", qe(nested, identity_closure(), zero(0, "identity_state", S("identity_state"))),
        {"native": False, "diagonal": True, "witness": True},
        "Closure elimination at a nested numerical iterator.")
    add("native_identity_induction", native_identity_closure(),
        {"native": True, "diagonal": False, "witness": False},
        "The old qi instruction is translated to diagonal-guard induction; it is not a hidden primitive of either seven-rule checker.")
    x, y = fresh("unused"), fresh("index")
    ordinary = raw_di(x, y, Eq(y, S(0)), 0, "case", lambda z, h: explode(S(z), S(0), h))
    add("ordinary_atomic_case_at_zero", ordinary,
        {"native": True, "diagonal": True, "witness": False},
        "The unguarded equation y=1 is introduced by cases at the literal zero witness; the contradictory base is used.")
    x, y, w, v = (fresh(n) for n in ("outer_x", "outer_y", "inner_x", "inner_y"))
    inner = D(w, v, Eq(0, 0))
    add("compound_D_case", case_di(x, y, inner, 0, lambda _z, h: h), yes,
        "A compound D matrix receives its zero instance.")
    qvar = fresh("qvar")
    inner_q = Q(qvar, Eq(qvar, qvar))
    add("compound_Q_case", case_di(x, y, inner_q, 0, lambda _z, h: h), yes,
        "Q is permitted inside D: the public language is the entire native formula grammar.")
    b = Eq(I(0, x, "state", S(x)), x)
    add("capture_avoiding_witness", case_di(x, y, b, nested,
        lambda _z, _h: zero(nested, "state", S(nested))), yes,
        "Substitution of a nested iterator witness beneath the closure and update binders.")
    add("nonvacuous_existential_elimination", nonvacuous_elimination(), yes,
        "The eliminated witness is used in a closure specialization and in the new existential witness.")
    p = "parameter"
    x, y = fresh("guard_x"), fresh("guard_y")
    b = Eq(I(y, y, "left_state", p), I(y, y, "right_state", p))

    def case_step(z, base):
        a0 = replace(b, y, 0)
        hole = fresh("base_hole")
        right_zero = tr(hole, hole, 0, base, zero(0, "left_state", p))
        target = replace(b, y, S(z))
        return tr(fresh("constant_hole"), target[1], target[2], right_zero, refl(target[1]))

    add("guarded_case_recovered", case_di(x, y, b, 0, case_step), yes,
        "An ordinary case proof at a guarded matrix is recovered by explicitly proving its zero instance.", (p,))
    add("guarded_old_case_needs_translation", raw_di(x, y, b, 0, "case", case_step),
        {"native": True, "diagonal": False, "witness": False},
        "The untouched old case certificate uses H(0), so it must be translated to the guarded progress rule.", (p,))
    x, y = fresh("bad_x"), fresh("bad_y")
    add("unguarded_equation_progress_rejected", raw_di(x, y, Eq(identity(y), y), 0, "progress", identity_step),
        {"native": False, "diagonal": False, "witness": True},
        "Atomicity alone does not select progress: the exact diagonal guard is required.")
    (ROOT / "fixtures.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    print(json.dumps(build(), indent=2))
