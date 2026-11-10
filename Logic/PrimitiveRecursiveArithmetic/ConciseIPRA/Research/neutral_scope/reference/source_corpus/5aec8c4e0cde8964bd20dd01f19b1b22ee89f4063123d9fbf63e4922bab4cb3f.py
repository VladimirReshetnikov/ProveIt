"""Match the two complete checkers across their changed G schemas."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def load(name):
    path = ROOT / "code" / (name + ".py")
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    producer = load("make_certificates")
    G, S, J, E, V = producer.G, producer.S, producer.J, producer.E, producer.V
    old, new = load("checker_four_schema"), load("checker")
    doubled_update = S(S(V(0)))
    double = lambda a: J(a, doubled_update)
    one, two = S(0), S(S(0))
    rows = []

    def add(name, equation, expected_old, expected_new):
        rows.append({"name": name, "packet": {"goal": equation, "proof": ["ax", equation]},
                     "old": expected_old, "new": expected_new})

    add("old_odd_gate", E(G(S(double(two)), one), one), True, False)
    add("old_even_gate", E(G(S(S(double(two))), one), two), True, False)
    add("old_odd_zero_counter", E(G(S(double(0)), two), two), True, False)
    add("old_even_zero_counter", E(G(S(S(double(0))), two), 0), True, False)
    add("new_successor_projection", E(G(S(two), one), two), False, True)
    add("old_odd_wrong_endpoint", E(G(S(double(two)), one), 0), False, False)
    add("old_even_wrong_endpoint", E(G(S(S(double(two))), one), one), False, False)
    add("wrong_double_update", E(G(S(J(two, S(V(0)))), one), one), False, False)
    add("wrong_even_double_update", E(G(S(S(J(two, V(0)))), one), two), False, False)
    add("missing_double_constructor", E(G(S(two), one), one), False, False)

    common = {"J_zero", "J_successor", "literal_equation_progress",
              "equation_induction_at_two", "conditional_closure",
              "compound_case_intro", "simultaneous_opening_under_J",
              "DE_lifts_retained_y_under_nested_Q"}
    for case in producer.cases():
        if case["name"] in common or not case["accept"]:
            rows.append({"name": "common_" + case["name"], "packet": case["packet"],
                         "old": case["accept"], "new": case["accept"]})

    results = []
    for row in rows:
        for label, checker, filename in (("old", old, "checker_four_schema.py"),
                                          ("new", new, "checker.py")):
            try:
                accepted = checker.verify(row["packet"])
            except Exception:
                accepted = False
            if accepted != row[label]:
                raise RuntimeError("Matched in-process failure: " + label + "/" + row["name"])
            for optimized in (False, True):
                command = [sys.executable] + (["-O"] if optimized else [])
                command.append(str(ROOT / "code" / filename))
                run = subprocess.run(command, input=json.dumps(row["packet"]), text=True,
                                     capture_output=True, timeout=15)
                wanted = "ACCEPT\n" if row[label] else "REJECT\n"
                passed = run.stdout == wanted and run.returncode == (0 if row[label] else 1)
                if not passed:
                    raise RuntimeError("Matched public failure: " + label + "/" + row["name"])
                results.append({"case": row["name"], "checker": label,
                                "optimized": optimized, "accept": row[label], "passed": True})
    receipt = {"case_pairs": len(rows), "in_process_checks": 2 * len(rows),
               "public_cli_checks": len(results), "failures": 0,
               "cases": rows, "results": results,
               "scope": "Matched schema-boundary tests, not same-theorem-language equivalence."}
    (ROOT / "tests" / "matched_results.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k not in ("cases", "results")}, indent=2))


if __name__ == "__main__":
    main()
