# Matched-control tests. The validation/scoping code is identical to C7.
import json
import subprocess
import sys

from compare_checkers import NEW, OLD, ROOT
from m7_control import check
from test_c7 import E, I, S, Z, build_cases, lift


def reflexivity(a, n):
    w = I(Z, a, Z)
    p = ["i0", a, Z]
    return ["x", w, a, n, lift(a, n), p, p]


def control_cases():
    shared_names = {
        "iterator_zero", "iterator_successor",
        "successor_computation_under_nested_binder",
        "unallocated_computation_body_rejected", "boolean_term_rejected",
        "malformed_goal_rejected", "boolean_hypothesis_index_rejected",
        "negative_hypothesis_index_rejected", "extra_instruction_payload_rejected",
        "false_closed_equation_rejected", "unknown_rule_rejected"
    }
    shared = [c for c in build_cases() if c["name"] in shared_names]
    cases = list(shared)

    def add(name, goal, proof, accept):
        cases.append({"name": name, "accept": accept,
                      "certificate": [goal, proof]})

    s = I(Z, Z, Z)
    p = ["i0", Z, Z]
    f, g = I(Z, S(0), Z), S(0)
    minor = ["i0", S(s), Z]
    goal = E(I(Z, S(Z), Z), S(Z))
    transport = ["x", s, Z, f, g, p, minor]
    add("two_varying_endpoints_in_one_transport", goal, transport, True)
    add("two_sided_target_mismatch", E(S(Z), I(Z, S(Z), Z)), transport, False)
    add("right_template_out_of_scope_rejected", goal,
        ["x", s, Z, f, 1, p, minor], False)
    add("right_template_wrong_sort_rejected", goal,
        ["x", s, Z, f, E(0, 0), p, minor], False)

    # Both premises of the forbidden zero-source packet are valid theorems.
    # First produce 0=s by allowed transport along s=0 with source s.
    zero_major = ["x", s, Z, 0, lift(s, 0), p, reflexivity(s, 0)]
    add("premise_for_zero_source_test", E(Z, s), zero_major, True)
    add("reflexivity_for_zero_source_test", E(Z, Z), reflexivity(Z, 0), True)
    add("literal_zero_source_rejected_with_true_premises", E(s, Z),
        ["x", Z, s, 0, Z, zero_major, reflexivity(Z, 0)], False)

    z = 0
    h = S(1)
    iz = I(z, Z, h)
    lhs = I(S(z), Z, h)
    step = ["x", iz, z, lift(lhs, 1), S(1), ["hyp", 0], ["is", z, Z, h]]
    body = E(I(1, Z, S(2)), 1)
    add("DI_progress_uses_induction_hypothesis", ["D", body],
        ["di", Z, step], True)
    add("DI_case_cannot_reuse_progress_hypothesis", ["D", body],
        ["di", S(Z), step], False)
    add("DI_unallocated_witness_rejected", ["D", body],
        ["di", 0, step], False)
    witness = I(Z, S(Z), 0)
    add("DI_case_iterator_witness_binder_shift", ["D", E(0, 0)],
        ["di", witness, reflexivity(I(Z, S(Z), 1), 1)], True)
    add("DI_compound_matrix_cases", ["D", ["D", E(Z, Z)]],
        ["di", Z, ["di", Z, reflexivity(Z, 2)]], True)

    dbody = E(1, 1)
    dp = ["di", Z, reflexivity(S(0), 1)]
    qp = ["de", dbody, dp, ["hyp", 0]]
    add("DE_exports_closure_at_fresh_witness", ["Q", E(0, 0)], qp, True)
    add("QE_specialization", E(S(Z), S(Z)),
        ["qe", E(0, 0), S(Z), qp, reflexivity(Z, 0)], True)
    return cases, sorted(shared_names)


def main():
    c7 = (ROOT / "c7_checker.py").read_text()
    m7 = (ROOT / "m7_control.py").read_text()
    if c7.count(OLD) != 1 or m7 != c7.replace(OLD, NEW):
        raise AssertionError("The matched control differs outside the equality branch")
    cases, shared = control_cases()
    results = []
    for case in cases:
        try:
            check(*case["certificate"])
            accepted = True
        except (ValueError, TypeError, IndexError, RecursionError):
            accepted = False
        if accepted != case["accept"]:
            raise AssertionError((case["name"], accepted, case["accept"]))
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else [])
            command.append(str(ROOT / "m7_control.py"))
            run = subprocess.run(command, input=json.dumps(case["certificate"]),
                                 text=True, capture_output=True)
            observed = run.returncode == 0 and run.stdout.strip() == "ACCEPT"
            if observed != case["accept"]:
                raise AssertionError((case["name"], optimized, run.stderr))
        results.append({"name": case["name"], "expected": case["accept"], "passed": True})
    summary = {"certificate_cases": len(cases),
               "expected_acceptances": sum(c["accept"] for c in cases),
               "direct_checks": len(cases), "subprocess_checks": 2 * len(cases),
               "optimized_mode_checked": True,
               "source_diff_restricted_to_equality_branch": True,
               "byte_identical_shared_certificates": shared,
               "results": results, "formal_verification": False}
    (ROOT / "m7_certificates.json").write_text(json.dumps(cases, indent=2) + "\n")
    (ROOT / "m7_test_results.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "results"}, indent=2))


if __name__ == "__main__":
    main()
