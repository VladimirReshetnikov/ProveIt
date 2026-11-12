"""Independent certificate construction and adversarial replay for the canonical kernel.

The expected goals below are constructed explicitly. This generator does not
call the checker's substitution or canonicalization functions. It is untrusted
test/support code and is not part of theorem acceptance.
"""
from __future__ import annotations

import copy
import importlib.util
import json
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "canonical_kernel_under_test", ROOT / "code" / "canonical_checker.py")
KERNEL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(KERNEL)


def S(t):
    return [0, t, 0]


def R(n, a, h):
    return [n, a, h if n != 0 else 0]


ONE = S(0)
TWO = S(ONE)
H = [0, 0]


def W(t):
    """A one-step constant computation whose right side is exactly t."""
    return R(ONE, 0, t)


J = [W(0), 0]
DUMMY_BODY = J
DUMMY_PROOF = ["i", ONE, ["c"]]


@dataclass
class Packet:
    goal: list
    proof: list

    def data(self):
        return {"goal": self.goal, "proof": self.proof}


def refl(t):
    # The sole calculation W(t)=t serves as BOTH local premises.
    return Packet([t, t], ["e", J, [1, t], W(t), t,
                           DUMMY_PROOF, ["c"], ["c"]])


def lift(p, scope, context_length):
    """Insert one unused witness parameter and clause around an old proof.

    Free parameters already present remain fixed. Parameters introduced by
    old subproofs move out one level, as do their local clause indices.
    """
    if type(p) is int:
        return p - 1 if p < -scope else p
    if type(p) is not list:
        return p
    out = [lift(x, scope, context_length) for x in p]
    if p and p[0] == "u" and p[1] >= context_length:
        out[1] += 1
    return out


def transport(eq, minor, fml, target, scope=0, context_length=0):
    s, t = eq.goal
    return Packet(target, ["e", J, fml, s, t, DUMMY_PROOF,
                           lift(eq.proof, scope, context_length),
                           lift(minor.proof, scope, context_length)])


def constant_calc(t):
    return Packet([W(t), t], ["c"])


def hypothesis(goal, index=0):
    return Packet(goal, ["u", index, 0, refl(0).proof])


def progression():
    # E(y): R(y,0;u.Su)=Sy. The step really uses the equation hypothesis.
    body = [R(1, 0, S(1)), S(1)]
    z = -1
    previous = R(z, 0, S(1))
    successor = R(S(z), 0, S(1))
    ih = hypothesis([previous, S(z)])
    calc = Packet([successor, S(previous)], ["c"])
    step = transport(ih, calc, [successor, S(1)],
                     [successor, S(S(z))], scope=1, context_length=1)
    return Packet([body], ["i", 0, step.proof])


def positives():
    examples = {}
    examples["constant_computation"] = constant_calc(0)
    examples["identity_computation"] = Packet([R(ONE, 0, 1), ONE], ["c"])
    examples["nonzero_predecessor_computation"] = Packet(
        [R(TWO, ONE, 1), R(ONE, ONE, 1)], ["c"])
    examples["reflexivity_zero"] = refl(0)
    examples["reflexivity_successor"] = refl(ONE)
    nested = R(ONE, 0, R(1, 0, 1))
    examples["reflexivity_nested_iterator"] = refl(nested)

    c0 = constant_calc(0)
    examples["symmetry_of_computation"] = transport(
        c0, refl(W(0)), [1, W(0)], [0, W(0)])

    # h(v)=R(1,0;u.R(u,0;w.v)). The hole under two binders has index 3.
    hs = R(ONE, 0, R(1, 0, W(0)))
    ht = R(ONE, 0, R(1, 0, 0))
    h_hole = R(ONE, 0, R(1, 0, 3))
    examples["transport_beneath_two_iterators"] = transport(
        c0, refl(hs), [hs, h_hole], [hs, ht])

    # F(v)=D_xy (W(R(y,0;w.v)) = R(y,0;w.v)). The independently
    # constructed template preserves y and the iterator binders at indices
    # 1 and 2; its occurrences of the hole have indices 4 and 5.
    f_hole = [[R(ONE, 0, R(2, 0, 5)), R(1, 0, 4)]]
    f_source = [[R(ONE, 0, R(2, 0, W(0))), R(1, 0, W(0))]]
    f_target = [[R(ONE, 0, R(2, 0, 0)), R(1, 0, 0)]]
    minor = Packet(f_source, ["i", ONE, ["c"]])
    examples["transport_beneath_D_and_iterators"] = transport(
        c0, minor, f_hole, f_target)

    induction = progression()
    examples["equation_progress_uses_hypothesis"] = induction
    target = [R(TWO, 0, S(1)), S(TWO)]
    examples["nontrivial_D_clause_use"] = Packet(
        target, ["e", induction.goal[0], target, W(0), 0,
                 induction.proof, ["c"], ["u", 0, TWO, refl(ONE).proof]])

    # A naming packet whose opened witness b is actually used:
    # B(x,y): R(y,0;u.x)=1. The base is 1=1 and the successor instance
    # at witness 1 is a calculation. Use at y=1 gives W(b)=1;
    # calculation gives W(b)=b; their transport gives b=1.
    name_body = [R(1, 0, 3), ONE]
    name_major = ["i", ONE, ["c"]]
    b = -1
    at_one = Packet([W(b), ONE], ["u", 0, ONE, refl(ONE).proof])
    local_eq = transport(constant_calc(b), at_one, [1, ONE], [b, ONE],
                         scope=1, context_length=1)
    examples["active_witness_discharge"] = Packet(
        [ONE, ONE], ["e", name_body, [1, ONE], b, ONE,
                     name_major, local_eq.proof, local_eq.proof])

    # It is legal for source and target to mention b if the formula template
    # ignores its argument and therefore exports a closed formula.
    examples["local_eigenparameter_in_ignored_source"] = Packet(
        J, ["e", J, J, b, b, DUMMY_PROOF, refl(b).proof, ["c"]])

    # Freshness is checked AFTER canonical substitution. With the hole
    # replaced by 0, the step body containing b is erased canonically.
    f_erased = [R(1, 0, b), ONE]
    examples["eigenparameter_erased_by_canonical_substitution"] = Packet(
        [ONE, ONE], ["e", J, f_erased, 0, 0, DUMMY_PROOF,
                     refl(0).proof, refl(ONE).proof])
    return examples


def negatives(good):
    examples = {}
    examples["false_equation"] = {"goal": [0, ONE], "proof": ["c"]}
    examples["unjustified_reflexivity_opcode"] = {"goal": H, "proof": ["r"]}
    examples["zero_counter_is_not_calculation"] = {
        "goal": [ONE, ONE], "proof": ["c"]}
    examples["wrong_calculation_result"] = {
        "goal": [W(0), ONE], "proof": ["c"]}
    examples["nonsuccessor_counter"] = {
        "goal": [R(W(0), 0, 0), 0], "proof": ["c"]}
    examples["noncanonical_zero_erased_body"] = {
        "goal": [[0, 0, 1], [0, 0, 1]], "proof": ["c"]}
    examples["illscoped_body_cannot_hide_under_zero"] = {
        "goal": [[0, 0, 99], [0, 0, 99]], "proof": ["c"]}
    examples["boolean_as_numeral"] = {"goal": [False, False], "proof": ["c"]}
    examples["loose_bound_variable"] = {"goal": [1, 1], "proof": ["c"]}
    examples["free_parameter_in_public_goal"] = {
        "goal": [-1, -1], "proof": refl(-1).proof}
    examples["empty_context_use"] = {
        "goal": H, "proof": ["u", 0, 0, refl(0).proof]}
    examples["missing_field"] = {"goal": H}
    examples["extra_field"] = {**refl(0).data(), "trusted": True}

    # The goal is closed and well formed, but the e instruction attempts
    # to export b=b. It must fail the final equality/freshness check.
    examples["eigenparameter_escape"] = {
        "goal": H,
        "proof": ["e", J, [1, 1], -1, -1, DUMMY_PROOF,
                  refl(-1).proof, refl(-1).proof]}

    wrong = copy.deepcopy(good["equation_progress_uses_hypothesis"].data())
    wrong["proof"][1] = ONE
    examples["wrong_intro_mode_changes_context"] = wrong

    wrong = copy.deepcopy(good["transport_beneath_two_iterators"].data())
    wrong["proof"][2][1][2][2] = 2
    examples["capture_by_wrong_iterator_hole_index"] = wrong

    wrong = copy.deepcopy(good["transport_beneath_D_and_iterators"].data())
    wrong["proof"][2][0][0][2][2] = 4
    examples["capture_by_wrong_D_hole_index"] = wrong

    wrong = copy.deepcopy(good["nontrivial_D_clause_use"].data())
    wrong["proof"][-1][1] = True
    examples["boolean_clause_index"] = wrong
    return examples


def accepted(data):
    try:
        KERNEL.check(data)
    except Exception as error:
        return False, type(error).__name__
    return True, None


def main():
    good = positives()
    bad = negatives(good)
    results = []
    examples = ROOT / "examples" / "canonical"
    for expected, collection in ((True, good), (False, bad)):
        folder = examples / ("accepted" if expected else "rejected")
        folder.mkdir(parents=True, exist_ok=True)
        for name, entry in collection.items():
            data = entry.data() if isinstance(entry, Packet) else entry
            actual, error = accepted(data)
            results.append({"name": name, "expected_accept": expected,
                            "accepted": actual, "error_type": error})
            (folder / (name + ".json")).write_text(
                json.dumps(data, separators=(",", ":")) + "\n")
    failures = [r for r in results if r["accepted"] != r["expected_accept"]]
    report = {"checker": "code/canonical_checker.py",
              "positive_cases": len(good), "negative_cases": len(bad),
              "passed": not failures, "results": results,
              "scope": "Executable examples and rejection tests; not a formal proof of soundness."}
    evidence = ROOT / "evidence"
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / "canonical_validation.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in
                      ("positive_cases", "negative_cases", "passed")}))
    if failures:
        print(json.dumps(failures, indent=2))
        raise SystemExit(1)


if __name__ == "__main__":
    main()
