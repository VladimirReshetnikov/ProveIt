"""Independent deterministic boundary checks for the readable counter kernel.

These cases supplement the written metatheory. They do not prove universal
soundness and are not part of the trusted checker.
"""
from pathlib import Path
import copy
import hashlib
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("counter_checked", ROOT / "checker.py")
K = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(K)


def Z():
    return ["0"]


def V(name):
    return ["v", name]


def S(value):
    return ["S", value]


def R(counter, seed, body, u="u", v="v"):
    return ["R", counter, seed, u, v, body]


def Eq(left, right):
    return ["=", left, right]


def packet(goal, proof, parameters=()):
    return {"parameters": list(parameters), "goal": goal, "proof": proof}


def run():
    cases = []

    def test(name, data, expected):
        output = subprocess.run(
            [sys.executable, str(ROOT / "checker.py")],
            input=json.dumps(data), text=True, capture_output=True, timeout=10)
        accepted = output.returncode == 0 and output.stdout.strip() == "ACCEPT"
        rejected = output.returncode != 0 and output.stdout.strip() == "REJECT"
        assert accepted if expected else rejected, (name, output.returncode,
                                                    output.stdout, output.stderr)
        cases.append({"name": name, "expected": "ACCEPT" if expected else "REJECT",
                      "returncode": output.returncode,
                      "stdout": output.stdout.strip()})

    a, p = V("a"), V("p")
    test("R0_arbitrary_seed", packet(Eq(R(Z(), a, V("u")), S(a)),
                                     {"rule": "R0"}, ("a",)), True)

    # Both bound coordinates occur outside a nested recursor's update.
    # The recursive image must retain the ORIGINAL outer update body.
    h = R(V("u"), V("v"), V("s"), "r", "s")
    rec = R(p, a, h)
    lhs = R(S(p), a, h)
    rhs = R(p, rec, V("s"), "r", "s")
    good_rs = packet(Eq(lhs, rhs), {"rule": "RS"}, ("a", "p"))
    test("RS_counter_and_state_under_nested_R", good_rs, True)
    test("RS_swapped_counter_state", packet(Eq(lhs, R(rec, p, V("s"), "r", "s")),
                                            {"rule": "RS"}, ("a", "p")), False)
    frozen = R(p, a, R(p, V("v"), V("s"), "r", "s"))
    test("RS_frozen_counter_in_recursive_body",
         packet(Eq(lhs, R(p, frozen, V("s"), "r", "s")),
                {"rule": "RS"}, ("a", "p")), False)

    # Shadowing the outer counter name in a nested update must protect
    # that local coordinate, while preserving the outer state in its seed.
    h_shadow = R(V("u"), V("v"), V("u"), "r", "u")
    rec_shadow = R(p, a, h_shadow)
    test("RS_shadowed_update_name",
         packet(Eq(R(S(p), a, h_shadow), R(p, rec_shadow, V("u"), "r", "u")),
                {"rule": "RS"}, ("a", "p")), True)

    capture_body = R(Z(), Z(), V("u"), "p", "w")
    capture_source = R(S(p), Z(), capture_body)
    test("RS_inserted_free_parameter_avoids_same_named_inner_binder",
         packet(Eq(capture_source, R(Z(), Z(), p, "renamed_p", "w")),
                {"rule": "RS"}, ("p",)), True)
    test("RS_naive_capture_of_inserted_parameter_rejected",
         packet(Eq(capture_source, R(Z(), Z(), p, "p", "w")),
                {"rule": "RS"}, ("p",)), False)

    source = R(Z(), Z(), Z())
    one = S(Z())
    left = R(source, Z(), V("u"))
    right = R(one, Z(), V("a"), "a", "b")
    test("CC_alpha_equivalent_updates", packet(Eq(left, right),
                                               {"rule": "CC", "major": {"rule": "R0"}}), True)
    test("CC_seed_change_rejected", packet(Eq(left, R(one, one, V("u"))),
                                           {"rule": "CC", "major": {"rule": "R0"}}), False)
    test("CC_update_role_change_rejected", packet(Eq(left, R(one, Z(), V("v"))),
                                                  {"rule": "CC", "major": {"rule": "R0"}}), False)

    source_eq = Eq(source, one)
    refl_one = {"rule": "RL", "equality": source_eq,
                "major": {"rule": "R0"}, "minor": {"rule": "R0"}}
    test("RL_root_endpoint", packet(Eq(one, one), refl_one), True)
    test("RL_wrong_target", packet(Eq(Z(), one), refl_one), False)

    matrix = Eq(R(Z(), V("x"), V("u")), S(V("x")))
    d = ["D", "x", "y", matrix]
    di = {"rule": "DI", "mode": "case", "witness": a,
          "eigen": "x", "body": {"rule": "R0"}}
    test("DI_alpha_shadowing_is_not_capture", packet(d, di, ("a",)), True)
    bad_di = copy.deepcopy(di)
    bad_di["eigen"] = "a"
    test("DI_eigen_collides_with_available_parameter", packet(d, bad_di, ("a",)), False)
    bad_di = copy.deepcopy(di)
    bad_di["witness"] = V("future")
    bad_di["eigen"] = "future"
    test("DI_witness_cannot_use_new_eigen", packet(d, bad_di, ("a",)), False)
    compound = ["D", "x", "y", ["D", "r", "s", Eq(one, one)]]
    test("DI_compound_progress_rejected",
         packet(compound, {"rule": "DI", "mode": "progress", "witness": Z(),
                           "eigen": "k", "body": {"rule": "hyp", "index": 0}}), False)

    closure = ["Q", "y", Eq(R(Z(), Z(), Z()), one)]
    test("Q_top_level_object_rejected", packet(closure, {"rule": "hyp", "index": 0}), False)
    test("Q_cannot_be_proved_by_computation",
         packet(Eq(source, one), {"rule": "QE", "closure": closure, "target": Z(),
                                 "major": {"rule": "R0"}, "base": {"rule": "R0"}}), False)
    test("future_free_variable_in_goal_rejected",
         packet(Eq(R(Z(), V("future"), Z()), S(V("future"))), {"rule": "R0"}), False)

    qmatrix = Eq(R(Z(), V("y"), Z()), S(V("y")))
    qpaired = ["D", "x", "y", qmatrix]
    qintro = {"rule": "DI", "mode": "case", "witness": Z(),
              "eigen": "z", "body": {"rule": "R0"}}
    quse = {"rule": "QE", "closure": ["Q", "y", qmatrix], "target": a,
            "major": {"rule": "hyp", "index": 0}, "base": {"rule": "R0"}}
    de = {"rule": "DE", "paired": qpaired, "major": qintro,
          "eigen": "d", "body": quse}
    test("DE_introduces_exact_reusable_Q_clause",
         packet(Eq(R(Z(), a, Z()), S(a)), de, ("a",)), True)
    bad_de = copy.deepcopy(de)
    bad_de["eigen"] = "a"
    test("DE_eigen_cannot_equal_retained_parameter",
         packet(Eq(R(Z(), a, Z()), S(a)), bad_de, ("a",)), False)

    # An independent named expected formula checks opening at two nested
    # binder levels, with a witness that itself contains internal binders.
    witness = R(p, Z(), R(V("u"), V("v"), V("s"), "r", "s"))
    target = R(a, Z(), V("v"))
    body = Eq(R(V("y"), V("x"), h), R(V("y"), V("x"), h))
    parsed = K.formula(["D", "x", "y", body], {"a", "p"})
    opened_x = K.substitute(parsed[1], 1, K.term(witness, {"a", "p"}))
    expected_q = K.formula(
        ["Q", "y", Eq(R(V("y"), witness, h), R(V("y"), witness, h))],
        {"a", "p"}, internal=True)
    assert ("Q", opened_x) == expected_q
    opened_y = K.substitute(opened_x, 0, K.term(target, {"a", "p"}))
    expected_body = K.formula(Eq(R(target, witness, h), R(target, witness, h)), {"a", "p"})
    assert opened_y == expected_body
    cases.append({"name": "nested_D_Q_openings_preserve_bound_witnesses", "expected": "MATCH",
                  "result": "MATCH"})

    result = {"status": "PASS", "checker_sha256": hashlib.sha256(
        (ROOT / "checker.py").read_bytes()).hexdigest(), "cases": cases,
        "case_count": len(cases),
        "scope": "Deterministic independent scoping, substitution and rule-boundary checks; not a universal soundness proof."}
    (ROOT / "independent_audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "cases"}, indent=2))


if __name__ == "__main__":
    run()
