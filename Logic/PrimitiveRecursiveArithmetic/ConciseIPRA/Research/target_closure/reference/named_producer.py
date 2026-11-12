"""Untrusted named-term producer for the independent typed checkers.

This file never imports a checker or its substitution operations. Names are
compiled to ordinary de Bruijn indices using explicit binder environments.
"""
import copy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def S(t):
    return ("S", t)


def I(n, a, u, h):
    return ("I", n, a, u, h)


def Eq(a, b):
    return ("=", a, b)


def Q(y, b):
    return ("Q", y, b)


def D(x, y, b):
    return ("D", x, y, b)


def te(t, env=()):
    if t == 0:
        return 0
    if isinstance(t, str):
        return ["v", env.index(t)]
    if t[0] == "S":
        return ["s", te(t[1], env)]
    _, n, a, u, h = t
    return ["i", te(n, env), te(a, env), te(h, (u,) + env)]


def fe(f, env=()):
    if f[0] == "=":
        return ["=", te(f[1], env), te(f[2], env)]
    if f[0] == "Q":
        return ["q", fe(f[2], (f[1],) + env)]
    _, x, y, body = f
    return ["d", fe(body, (y, x) + env)]


def zero(a, u, h, env=()):
    return ["zero", te(a, env), te(h, (u,) + env)]


def succ(n, a, u, h, env=()):
    return ["succ", te(n, env), te(a, env), te(h, (u,) + env)]


def tr(hole, matrix, major, minor, env=()):
    return ["tr", fe(matrix, (hole,) + env), major, minor]


def refl(t, env=()):
    p = zero(t, "refl_state", 0, env)
    return tr("refl_hole", Eq("refl_hole", t), p, p, env)


def intro(x, y, matrix, witness, premise, env=()):
    return ["intro", fe(matrix, (y, x) + env), te(witness, env), premise]


def elim(conclusion, major, continuation, env=()):
    return ["elim", fe(conclusion, env), major, continuation]


def identity(y):
    return Eq(I(y, 0, "identity_state", S("identity_state")), y)


def identity_step(z, env):
    lhs = I(S(z), 0, "identity_state", S("identity_state"))
    return tr("step_hole", Eq(lhs, S("step_hole")), ["hyp", 0],
              succ(z, 0, "identity_state", S("identity_state"), env), env)


def progressive_pair(env=()):
    return intro("unused_witness", "index", identity("index"), 0,
                 identity_step("fresh_index", ("fresh_index",) + env), env)


def native_progress(env=()):
    return ["ind", fe(identity("index"), ("index",) + env),
            identity_step("fresh_index", ("fresh_index",) + env)]


def identity_at(n, system="orbit", env=()):
    if system == "native":
        return ["use", te(n, env), native_progress(env),
                zero(0, "identity_state", S("identity_state"), env)]
    inner = ("fresh_witness",) + env
    if system == "witness":
        continuation = ["use", te(n, inner), ["hyp", 0],
                        zero(0, "identity_state", S("identity_state"), inner)]
    else:
        use = ["use", 0, te(n, inner), ["hyp", 0],
               zero(0, "identity_state", S("identity_state"), inner)]
        continuation = tr("iteration_target", identity("iteration_target"),
                          zero(n, "orbit_state", S("orbit_state"), inner),
                          use, inner)
    return elim(identity(n), progressive_pair(env), continuation, env)


def explosion(a, b, env):
    c = lambda v: I(v, a, "constant_state", b)
    c1a = tr("counter_hole", Eq(c("counter_hole"), a), ["hyp", 0],
             zero(a, "constant_state", b, env), env)
    ba = tr("value_hole", Eq("value_hole", a),
            succ(0, a, "constant_state", b, env), c1a, env)
    return tr("reverse_hole", Eq("reverse_hole", b), ba, refl(b, env), env)


def toggle(t):
    return I(t, S(0), "toggle_dummy", 0)


def parity(t):
    return I(t, 0, "parity_state", toggle("parity_state"))


def parity_one(env=()):
    one = S(0)
    first = tr("toggle_input", Eq(parity(one), toggle("toggle_input")),
               zero(0, "parity_state", toggle("parity_state"), env),
               succ(0, 0, "parity_state", toggle("parity_state"), env), env)
    return tr("toggle_result", Eq(parity(one), "toggle_result"),
              zero(one, "toggle_dummy", 0, env), first, env)


def parity_two(env=()):
    one, two = S(0), S(S(0))
    first = tr("toggle_input", Eq(parity(two), toggle("toggle_input")),
               parity_one(env),
               succ(one, 0, "parity_state", toggle("parity_state"), env), env)
    return tr("toggle_result", Eq(parity(two), "toggle_result"),
              succ(0, one, "toggle_dummy", 0, env), first, env)


def open_rule_tests():
    one, two = S(0), S(S(0))
    target = I(one, one, "orbit_state", S("orbit_state"))
    e = lambda y: Eq(parity(y), one)
    use = ["use", te(one), te(one), ["hyp", 0], parity_one()]
    target_two = tr("orbit_seed", Eq(target, S("orbit_seed")),
                    zero(one, "orbit_state", S("orbit_state")),
                    succ(0, one, "orbit_state", S("orbit_state")))
    e_two = tr("orbit_target", e("orbit_target"), target_two, use)
    contradiction = tr("parity_result", Eq("parity_result", one),
                       parity_two(), e_two)
    b = lambda y: D("gate_witness", "gate_index", Eq(
        I("gate_index", 0, "gate_state", y),
        I("gate_index", 0, "gate_state", one)))
    return [
        {"name": "progressive_resource_has_its_full_strength", "scope": 0,
         "context": [fe(Q("index", e("index")))], "goal": fe(Eq(0, one)),
         "proof": contradiction, "expected": True,
         "note": "This is an OPEN sequent, not a proof of contradiction: the progressive parity assumption is false. E(1), the orbit step, and E(2) recover its contradiction. The old base-closure assumption has a false base and would not suffice."},
        {"name": "compound_resource_cannot_be_used_progressively", "scope": 0,
         "context": [fe(Q("index", b("index"))), fe(b(one))],
         "goal": fe(b(target)),
         "proof": ["use", te(one), te(one), ["hyp", 0], ["hyp", 1]],
         "expected": False,
         "note": "B(y) is equivalent to y=1. Both compound premises hold in N, while the illicit target B(2) fails. Eta must force source zero."},
    ]


def package(goal, proof):
    return {"goal": fe(goal), "proof": proof}


def build():
    directory = ROOT / "certificates"
    directory.mkdir(exist_ok=True)
    one, two, three = S(0), S(S(0)), S(S(S(0)))
    cases = []

    def add(name, data, expected, note):
        (directory / (name + ".json")).write_text(json.dumps(data, indent=2) + "\n")
        cases.append({"file": name + ".json", "expected": expected, "note": note})

    all_yes = {s: True for s in ("orbit", "native", "witness")}
    p = zero(one, "state", 0)
    add("zero_computation", package(Eq(I(0, one, "state", 0), one), p), all_yes,
        "The zero equation; no logical axiom is supplied externally.")
    p = succ(0, one, "state", S("state"))
    add("successor_computation", package(Eq(I(one, one, "state", S("state")),
        S(I(0, one, "state", S("state")))), p), all_yes,
        "The successor equation with a state-dependent update.")
    add("derived_reflexivity", package(Eq(two, two), refl(two)), all_yes,
        "Reflexivity derived from computation and equational transport.")
    for system in ("orbit", "native", "witness"):
        add("identity_at_three_" + system, package(identity(three), identity_at(three, system)),
            {system: True}, "An actual use of the induction hypothesis proves I(3,0;Su)=3.")
    goal = D("unused_witness", "index", identity("index"))
    add("atomic_introduction_used_hypothesis", package(goal, progressive_pair()),
        {"orbit": True, "native": False, "witness": True},
        "The progress premise uses the retained equation through transport.")
    for system in ("orbit", "native", "witness"):
        p = native_progress() if system == "native" else elim(
            Q("index", identity("index")), progressive_pair(), ["hyp", 0])
        add("closure_extraction_" + system, package(Q("index", identity("index")), p),
            {system: True}, "Q obtained from an unused existential coordinate, or old QI.")

    target = I(one, one, "orbit_state", S("orbit_state"))
    inner = ("fresh_witness",)
    p = elim(identity(target), progressive_pair(),
             ["use", te(one, inner), te(one, inner), ["hyp", 0],
              identity_at(one, "orbit", inner)])
    add("nonzero_orbit_source", package(identity(target), p), {"orbit": True},
        "The new QE rule uses source 1 and seed 1, not its zero-source specialization.")

    stable = D("inner_x", "inner_y", Eq(0, 0))
    stable_proof = intro("inner_x", "inner_y", Eq(0, 0), 0, refl(0, ("z",)))
    compound = D("outer_x", "outer_y", stable)
    compound_proof = intro("outer_x", "outer_y", stable, 0, ["hyp", 0])
    add("compound_case_introduction", package(compound, compound_proof), all_yes,
        "The compound introduction retains the zero instance, even in the new calculus.")
    use_compound = elim(stable, compound_proof,
        ["use", te(three, ("a",)), te(two, ("a",)), ["hyp", 0], stable_proof])
    add("compound_eta_ignores_source", package(stable, use_compound), {"orbit": True},
        "At a compound matrix eta selects zero despite the supplied argument 3.")

    ordinary_matrix = Eq("index", one)
    old_case = intro("unused", "index", ordinary_matrix, 0,
                     explosion(S("z"), one, ("z",)))
    add("old_atomic_case_is_not_progress", package(D("unused", "index", ordinary_matrix), old_case),
        {"orbit": False, "native": True, "witness": False},
        "Its ordinary conditional reading is true, while its progressive reading is false.")
    boxed = copy.deepcopy(old_case)
    boxed[2] = te(I(0, 0, "box_state", 0))
    add("boxed_old_atomic_case", package(D("unused", "index", ordinary_matrix), boxed),
        {"orbit": False, "native": True, "witness": True},
        "The old witness-dispatched calculus changes mode at a nonliteral zero witness.")

    add("false_equality", package(Eq(0, one), refl(0)), {s: False for s in all_yes},
        "A proof of reflexivity does not prove 0=1.")
    add("wrong_computation_endpoint", package(Eq(I(0, one, "state", 0), 0), zero(one, "state", 0)),
        {s: False for s in all_yes}, "A caller cannot change a computation equation's endpoint.")
    p = identity_at(three)
    bad = copy.deepcopy(p)
    bad[3][3][4] = refl(one, ("fresh_witness",))
    add("wrong_orbit_antecedent", package(identity(three), bad), {"orbit": False},
        "The zero-source orbit rule requires E(0), not an unrelated equation.")
    bad = copy.deepcopy(progressive_pair())
    bad[2] = ["v", 0]
    add("future_witness", package(goal, bad), {s: False for s in all_yes},
        "A DI witness cannot refer to the eigenparameter that the rule will create.")
    bad = ["zero", 0, ["v", 1]]
    add("unbound_iterator_state", package(Eq(0, 0), bad), {s: False for s in all_yes},
        "At the root an iterator body has exactly one bound state slot.")
    bad = elim(Eq(0, 0), progressive_pair(), refl("fresh_witness", ("fresh_witness",)))
    add("existential_eigenvariable_escape", package(Eq(0, 0), bad), {s: False for s in all_yes},
        "The continuation proves a=a; the declared closed conclusion is not its weakening.")
    add("noninteger_variable", {"goal": ["=", 0, 0], "proof": ["zero", 0, ["v", True]]},
        {s: False for s in all_yes}, "Boolean values are not accepted as variable indices.")
    add("negative_hypothesis_index", package(Eq(0, 0), ["hyp", -1]),
        {s: False for s in all_yes}, "Negative Python indexing cannot access an assumption.")
    add("unknown_rule", package(Eq(0, 0), ["axiom", ["=", 0, 0]]),
        {s: False for s in all_yes}, "No caller-supplied axiom or theorem database is available.")
    add("compound_induction_is_not_primitive", package(Q("outer", stable),
        ["ind", fe(stable, ("outer",)), ["hyp", 0]]),
        {s: False for s in all_yes}, "The old progress rule requires a literal equation; the new calculus has no primitive ind instruction.")
    add("compound_transport_is_not_primitive", package(stable,
        ["tr", fe(stable, ("hole",)), refl(0), stable_proof]),
        {s: False for s in all_yes}, "Transport through compound formulas is derived in the paper, not a primitive accepted instruction.")
    add("open_public_goal", {"goal": ["=", ["v", 0], ["v", 0]], "proof": ["hyp", 0]},
        {s: False for s in all_yes}, "The standalone interface requires a closed public goal.")
    add("malformed_instruction", package(Eq(0, 0), ["zero", 0]),
        {s: False for s in all_yes}, "Every instruction has exactly the documented fields.")
    (ROOT / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    (ROOT / "open_sequents.json").write_text(json.dumps(open_rule_tests(), indent=2) + "\n")
    return cases


if __name__ == "__main__":
    build()
