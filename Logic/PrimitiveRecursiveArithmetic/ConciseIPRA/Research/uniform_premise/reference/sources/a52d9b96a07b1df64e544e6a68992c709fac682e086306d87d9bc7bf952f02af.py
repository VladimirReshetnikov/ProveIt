"""Untrusted producer of focused checker regression certificates."""
import copy
import json
from pathlib import Path


def G(a, b):
    return ["g", a, b]


def S(a):
    return G(0, a)


def J(n, h):
    return ["j", n, h]


def E(a, b):
    return ["=", a, b]


def Q(a):
    return ["q", a]


def D(a):
    return ["d", a]


V = lambda n: ["v", n]
P = lambda name: ["p", name]
AX = lambda equation: ["ax", equation]


def reflexivity(t):
    r = G(S(t), 0)
    ax = AX(E(r, t))
    return ["tr", ax, E(V(0), t), ax]


def constant_closure(t):
    target = D(E(t, t))
    major = ["di", target, 0, "z", "case", ["hyp", 0]]
    return ["de", major, "a", Q(E(t, t)), ["hyp", 0]]


def cases():
    records = []

    def add(name, goal, proof, accept=True):
        records.append({"name": name, "accept": accept,
                        "packet": {"goal": goal, "proof": proof}})

    one, two = S(0), S(S(0))
    identity = V(0)
    increment = S(V(0))
    add("G_computation", E(G(S(two), one), two),
        AX(E(G(S(two), one), two)))
    add("J_zero", E(J(0, increment), 0), AX(E(J(0, increment), 0)))
    js = E(J(one, increment), S(J(0, increment)))
    add("J_successor", js, AX(js))
    add("derived_reflexivity", E(two, two), reflexivity(two))
    add("one_iteration_is_one", E(J(one, increment), one),
        ["tr", AX(E(J(0, increment), 0)), E(J(one, increment), S(V(0))), AX(js)])

    eqbody = E(J(V(0), identity), 0)
    target = D(eqbody)
    z = P("z")
    step_goal = E(J(S(z), identity), 0)
    js_step = E(J(S(z), identity), J(z, identity))
    step = ["tr", ["hyp", 0], E(J(S(z), identity), V(0)), AX(js_step)]
    di = ["di", target, 0, "z", "step", step]
    add("literal_equation_progress", target, di)
    final = E(J(two, identity), 0)
    complete = ["de", di, "a", final,
                ["qe", ["hyp", 0], two, AX(E(J(0, identity), 0))]]
    add("equation_induction_at_two", final, complete)

    qzero = Q(E(0, 0))
    add("conditional_closure", qzero, constant_closure(0))
    add("compound_case_intro", D(qzero),
        ["di", D(qzero), 0, "z", "case", ["hyp", 0]])

    # Under 0=1, reverse the equality, collapse S(z) to zero, then to one.
    reverse = ["tr", ["hyp", 0], E(V(0), 0), reflexivity(0)]
    collapse = ["tr", reverse, E(G(V(0), z), 0), AX(E(G(one, z), 0))]
    successor_one = ["tr", ["hyp", 0], E(S(z), V(0)), collapse]
    false_base = D(E(V(0), one))
    false_base_proof = ["di", false_base, 0, "z", "case", successor_one]
    add("atomic_case_with_false_base", false_base, false_base_proof)

    r = G(one, 0)
    motive = Q(E(V(1), V(1)))
    add("transport_under_Q_binder", qzero,
        ["tr", AX(E(r, 0)), motive, constant_closure(r)])

    # Fixed passive parameters and nested numerical binders are both active.
    nested_body = J(V(0), G(V(1), V(0)))
    nested_left = J(one, nested_body)
    previous = J(0, nested_body)
    nested_right = J(previous, G(previous, V(0)))
    add("simultaneous_opening_under_J", E(nested_left, nested_right),
        AX(E(nested_left, nested_right)))

    # DE keeps y under Q; crossing an additional Q must lift its image.
    outer = D(Q(E(V(1), V(1))))
    inner_target = D(E(S(z), S(z)))
    inner_major = ["di", inner_target, 0, "w", "case", ["hyp", 1]]
    inner_closure = ["de", inner_major, "a", Q(E(S(z), S(z))), ["hyp", 1]]
    outer_major = ["di", outer, 0, "z", "case", inner_closure]
    double_closure = Q(Q(E(V(1), V(1))))
    add("DE_lifts_retained_y_under_nested_Q", double_closure,
        ["de", outer_major, "b", double_closure, ["hyp", 0]])

    add("reject_ungated_G_zero_equation", E(G(0, one), 0), AX(E(G(0, one), 0)), False)
    add("reject_wrong_G_projection", E(G(S(two), one), one),
        AX(E(G(S(two), one), one)), False)
    add("reject_wrong_J_zero", E(J(0, identity), one), AX(E(J(0, identity), one)), False)
    add("reject_wrong_J_successor", E(J(one, increment), 0), AX(E(J(one, increment), 0)), False)
    add("reject_compound_progress", D(qzero),
        ["di", D(qzero), 0, "z", "step", ["hyp", 0]], False)
    add("reject_formula_as_term", E(qzero, 0), AX(E(qzero, 0)), False)
    add("reject_term_as_formula", one, AX(one), False)
    add("reject_open_goal", E(V(0), V(0)), ["hyp", 0], False)
    add("reject_unintroduced_parameter", E(P("x"), P("x")), reflexivity(P("x")), False)
    add("reject_boolean_zero", E(False, 0), AX(E(False, 0)), False)
    add("reject_float_zero", E(0.0, 0), AX(E(0.0, 0)), False)
    constant_d = D(E(0, 0))
    add("reject_boolean_hyp_index", constant_d,
        ["di", constant_d, 0, "z", "case", ["hyp", False]], False)
    add("reject_bad_hyp_index", constant_d,
        ["di", constant_d, 0, "z", "case", ["hyp", -1]], False)
    add("reject_escaped_DE_parameter", E(0, 0),
        ["de", di, "a", E(P("a"), P("a")), reflexivity(P("a"))], False)
    reused = ["di", D(qzero), 0, "z", "case",
              ["de", ["di", D(E(0, 0)), 0, "z", "case", ["hyp", 1]],
               "a", qzero, ["hyp", 1]]]
    add("reject_reused_active_eigenparameter", D(qzero), reused, False)
    add("reject_wrong_QE_base", E(0, 0),
        ["qe", constant_closure(0), 0, AX(E(J(0, identity), 0))], False)
    add("reject_unscoped_transport_motive", qzero,
        ["tr", AX(E(r, 0)), Q(E(V(2), V(2))), constant_closure(r)], False)
    add("reject_wrong_transport_minor", E(0, 0),
        ["tr", AX(E(r, 0)), E(V(0), 0), reflexivity(0)], False)
    add("reject_unknown_rule", E(0, 0), ["trust", E(0, 0)], False)

    extra = copy.deepcopy(records[0])
    extra.update(name="reject_extra_packet_field", accept=False)
    extra["packet"]["trusted"] = True
    records.append(extra)
    return records


if __name__ == "__main__":
    destination = Path(__file__).resolve().parents[1] / "tests" / "certificates.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps({"cases": cases()}, indent=2) + "\n")
    print(f"Wrote {len(cases())} focused certificates")
