"""Focused independent regressions for the BRep reference checker.

These supplement, rather than repeat, test_checker.py. No proof-assistant
verification is claimed. Run with ordinary Python 3.
"""

import hashlib
import json
from pathlib import Path
import subprocess
import sys

import checker as c


ROOT = Path(__file__).resolve().parent
Z = []
ONE = [[]]


def hyp(i):
    return {"rule": "hyp", "index": i}


def refl(t):
    j = [[], t, 0]
    return {"rule": "brep", "equality": [j, t],
            "major": {"rule": "i0"}, "minor": {"rule": "i0"}}


def sym(s, t, proof):
    return {"rule": "brep", "equality": [s, s],
            "major": refl(s), "minor": proof}


def trans(s, t, u, first, second):
    return {"rule": "brep", "equality": [t, u],
            "major": second, "minor": sym(s, t, first)}


def record(n, context, goal, proof):
    return {"n": n, "context": context, "goal": goal, "proof": proof}


def zero_name(closed):
    """Open a name, extract its actual fresh witness, then discharge it."""
    if closed:
        n, target, context, index = 0, [], [], 0
        matrix = [[0, [], 2], [0, [], []]]
        body = [[0, [], 2], [0, [], []]]
        left0, right0 = [[], [], 1], [[], [], []]
        left1, right1 = [ONE, [], 1], [ONE, [], []]
        major = {"rule": "di", "witness": [],
                 "premise": refl([[0], [], []])}
    else:
        n, target, index = 2, 0, 1
        matrix = [[0, [], 2], [0, [], 3]]
        context = [[matrix]]
        body = [[0, [], 4], [0, [], 2]]
        left0, right0 = [[], [], 3], [[], [], 1]
        left1, right1 = [ONE, [], 3], [ONE, [], 1]
        major = hyp(0)

    # These hand-written expected arrays distinguish old parameters from
    # the freshly appended witness, including beneath the iterator binder.
    assert c.witness_body(matrix, n) == body
    assert c.substitute_formula(body, []) == [left0, right0]
    assert c.substitute_formula(body, ONE) == [left1, right1]

    base = trans(left0, [], right0, {"rule": "i0"},
                 sym(right0, [], {"rule": "i0"}))
    at_one = {"rule": "qe", "body": body, "term": ONE,
              "major": hyp(index), "base": base}
    name_to_right = trans(n, left1, right1,
                          sym(left1, n, {"rule": "is"}), at_one)
    named = trans(n, right1, target, name_to_right, {"rule": "is"})
    branch = {"rule": "brep", "equality": [n, target],
              "major": named, "minor": named}
    proof = {"rule": "de", "matrix": matrix, "major": major,
             "branch": branch}
    return record(n, context, [target, target], proof)


def run():
    positives = {}
    negatives = {}

    # Here the replacement TARGET, not its inserted source, is free variable
    # zero. The iterator's bound variable zero must not match it.
    destination = [[], [], 0]
    wrongly_changed = [[], [], []]
    equality = [[], 0]
    proof = {"rule": "brep", "equality": equality,
             "major": hyp(0), "minor": hyp(1)}
    positives["free_target_does_not_match_bound_variable"] = record(
        1, [equality, [destination, []]], [[], destination], proof)
    negatives["forged_matching_of_bound_variable_to_free_target"] = record(
        1, [equality, [wrongly_changed, []]], [[], destination], proof)

    positives["de_uses_actual_appended_witness"] = zero_name(False)
    positives["closed_zero_name_is_used_and_discharged"] = zero_name(True)
    wrong_witness = json.loads(json.dumps(positives["de_uses_actual_appended_witness"]))
    wrong_witness["proof"]["branch"]["equality"] = [1, 0]
    negatives["de_old_parameter_cannot_replace_new_witness"] = wrong_witness

    # Progress really uses the new parameter at index n=2; the passive
    # arithmetic parameter remains at old index 0 throughout.
    body = [[0, 1, 2], 1]
    positives["qi_keeps_old_parameter_and_uses_new_counter"] = record(
        2, [], [0, 0, body], {"rule": "qi", "premise": {"rule": "is"}})

    outcomes = []
    for expected, records in ((True, positives), (False, negatives)):
        for name, item in records.items():
            accepted = True
            try:
                c.verify(item["n"], item["context"], item["goal"], item["proof"])
            except c.InvalidCertificate:
                accepted = False
            assert accepted == expected, name
            outcomes.append({"name": name, "expected_accept": expected,
                             "accepted": accepted})

    drivers = []
    for optimized in (False, True):
        for name in ("closed_zero_name_is_used_and_discharged",
                     "de_uses_actual_appended_witness"):
            item = positives[name]
            command = [sys.executable] + (["-O"] if optimized else [])
            command += [str(ROOT / "checker.py")]
            result = subprocess.run(command, input=json.dumps(item), text=True,
                                    capture_output=True, timeout=15)
            expected = item["n"] == 0 and item["context"] == []
            assert (result.returncode == 0) == expected, (name, result.stderr)
            assert (result.stdout == "ACCEPT\n") == expected, name
            drivers.append({"name": name, "optimized": optimized,
                            "expected_accept": expected,
                            "returncode": result.returncode})

    fixtures = ROOT / "independent_fixtures"
    fixtures.mkdir(exist_ok=True)
    for category, records in (("positive", positives), ("negative", negatives)):
        for name, item in records.items():
            (fixtures / (category + "_" + name + ".json")).write_text(
                json.dumps(item, indent=2) + "\n", encoding="utf-8")

    report = {
        "all_passed": True,
        "checker_sha256": hashlib.sha256((ROOT / "checker.py").read_bytes()).hexdigest(),
        "positive_sequents": len(positives),
        "negative_certificates": len(negatives),
        "driver_runs": len(drivers),
        "outcomes": outcomes,
        "drivers": drivers,
        "status": "Focused finite implementation tests, not formal verification."
    }
    (ROOT / "independent_audit_results.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    run()
