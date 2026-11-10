"""Generate small auditable native certificates and check both complete kernels."""
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
ZERO = "0"
def var(n): return ["v", n]
def gate(a, b): return ["b", a, b]
def suc(a): return gate(ZERO, a)
def num(n):
    result = ZERO
    for _ in range(n): result = suc(result)
    return result
def itr(n, h): return ["j", n, h]
def eq(a, b): return ["=", a, b]
def double(a): return itr(a, suc(suc(var(0))))
def packet(goal, proof): return {"goal": goal, "proof": proof}

def load(path):
    tree = ast.parse(path.read_text())
    assert isinstance(tree.body[-1], ast.Try)
    tree.body.pop()
    ns = {}
    exec(compile(tree, str(path), "exec"), ns)
    return ns

def common_cases():
    body = eq(itr(ZERO, var(1)), ZERO)
    paired_case = ["di", "case", ZERO, -1, ["compute"]]
    q_case = ["de", body, -2, paired_case, ["hyp", 0]]
    ind_body = eq(itr(var(0), var(0)), ZERO)
    z = var(-1)
    left = itr(suc(z), var(0))
    previous = itr(z, var(0))
    step = ["tr", previous, ZERO, eq(left, var(0)), ["hyp", 0], ["compute"]]
    paired_ind = ["di", "ind", ZERO, -1, step]
    q_ind = ["de", ind_body, -2, paired_ind, ["hyp", 0]]
    compound = ["q", eq(ZERO, num(1))]
    positive = [
        ("iterator_zero", packet(eq(itr(ZERO, suc(var(0))), ZERO), ["compute"])),
        ("iterator_successor", packet(eq(itr(num(1), suc(var(0))), suc(itr(ZERO, suc(var(0))))), ["compute"])),
        ("case_introduction", packet(["d", body], paired_case)),
        ("paired_elimination_to_closure", packet(["q", body], q_case)),
        ("closure_elimination", packet(eq(itr(ZERO, num(2)), ZERO), ["qe", body, num(2), q_case, ["compute"]])),
        ("literal_equation_induction", packet(["d", ind_body], paired_ind)),
        ("derived_contextual_induction", packet(eq(itr(num(3), var(0)), ZERO), ["qe", ind_body, num(3), q_ind, ["compute"]])),
        ("compound_case", packet(["d", compound], ["di", "case", ZERO, -1, ["hyp", 0]])),
        ("retained_false_base", packet(["d", eq(ZERO, num(1))], ["di", "case", ZERO, -1, ["hyp", 0]])),
    ]
    negative = [
        ("false_arithmetic", packet(eq(ZERO, num(1)), ["compute"])),
        ("unjustified_hypothesis", packet(eq(ZERO, ZERO), ["hyp", 0])),
        ("free_bound_coordinate", packet(eq(var(0), var(0)), ["compute"])),
        ("free_eigenparameter", packet(eq(var(-1), var(-1)), ["compute"])),
        ("compound_induction_forbidden", packet(["d", compound], ["di", "ind", ZERO, -1, ["hyp", 0]])),
        ("positive_eigenparameter_forbidden", packet(["d", body], ["di", "case", ZERO, 0, ["compute"]])),
        ("capture_in_witness", packet(["d", body], ["di", "case", var(0), -1, ["compute"]])),
        ("wrong_iterator_successor", packet(eq(itr(num(1), suc(var(0))), ZERO), ["compute"])),
        ("malformed_term", packet(eq(["b", ZERO], ZERO), ["compute"])),
        ("extra_rule_fields", packet(eq(itr(ZERO, var(0)), ZERO), ["compute", "ignored"])),
        ("unknown_rule", packet(eq(ZERO, ZERO), ["axiom"])),
        ("boolean_variable_index", packet(eq(var(False), ZERO), ["compute"])),
    ]
    wrong = copy.deepcopy(positive[4][1]); wrong["proof"][2] = num(3)
    negative.append(("wrong_closure_instance", wrong))
    bad_major = copy.deepcopy(positive[6][1]); bad_major["proof"][3] = ["compute"]
    negative.append(("failed_major_must_reject", bad_major))
    # The outer DI authorizes -1; a nested DI may not allocate it again.
    nested = ["d", ["d", body]]
    reused = ["di", "case", ZERO, -1, ["di", "case", ZERO, -1, ["compute"]]]
    negative.append(("eigenparameter_reuse", packet(nested, reused)))
    return [(name, p, True) for name, p in positive] + [(name, p, False) for name, p in negative]

def basis_cases(name):
    a, b = num(2), num(3)
    if name == "new":
        left = gate(suc(a), b)
        good = [("gate_retraction", packet(eq(left, a), ["compute"]), True),
                ("wrong_gate_output", packet(eq(left, b), ["compute"]), False)]
    else:
        left = gate(suc(suc(double(a))), b)
        good = [("gate_seed_branch", packet(eq(gate(suc(double(a)), b), b), ["compute"]), True),
                ("gate_decode_branch", packet(eq(left, a), ["compute"]), True),
                ("wrong_gate_output", packet(eq(left, b), ["compute"]), False),
                ("wrong_doubling_update", packet(eq(gate(suc(itr(a, var(0))), b), b), ["compute"]), False)]
    motive = eq(var(0), a)
    proof = ["tr", left, a, motive, ["compute"], ["compute"]]
    good.append(("derived_equality_reflexivity", packet(eq(a, a), proof), True))
    return good

def main():
    spec = importlib.util.spec_from_file_location("measure", ROOT.parent / "audit_frontier.py")
    measure = importlib.util.module_from_spec(spec); spec.loader.exec_module(measure)
    examples = ROOT / "examples"; examples.mkdir(exist_ok=True)
    profiles = []
    all_cases = []
    receipts = []
    for name in ("new", "old"):
        path = ROOT / (name + "_checker.py")
        ns = load(path)
        cases = common_cases() + basis_cases(name)
        for case_name, p, expected in cases:
            actual = bool(ns["check"](p["goal"], p["proof"]))
            assert actual == expected, (name, case_name, actual, expected)
            relative = name + "_" + case_name + ".json"
            (examples/relative).write_text(json.dumps(p, indent=2) + "\n")
            for optimized in (False, True):
                command = [sys.executable] + (["-O"] if optimized else []) + [str(path)]
                run = subprocess.run(command, input=json.dumps(p), text=True, capture_output=True, timeout=10)
                assert run.stdout == ("ACCEPT\n" if expected else "REJECT\n"), (name, case_name, run)
                assert run.returncode == (0 if expected else 1) and not run.stderr
                receipts.append({"profile": name, "case": case_name, "optimized": optimized,
                                 "expected_accept": expected, "stdout": run.stdout, "exit": run.returncode})
            all_cases.append({"profile": name, "name": case_name, "file": "examples/"+relative,
                              "accept": expected})
        profiles.append({"profile": name, "file": path.name, **measure.measure(path)})
    # Parsing and top-level protocol failures are tested through the public interface.
    for name in ("new", "old"):
        for data in ("{", "[]", "{}", '{"goal":[],"proof":[],"extra":0}'):
            run = subprocess.run([sys.executable, str(ROOT/(name+"_checker.py"))], input=data,
                                 text=True, capture_output=True, timeout=10)
            assert (run.stdout, run.returncode, run.stderr) == ("REJECT\n", 1, "")
            receipts.append({"profile": name, "parser_input": data, "expected_accept": False,
                             "stdout": run.stdout, "exit": run.returncode})
    old, new = profiles[1], profiles[0]
    result = {"profiles": profiles, "saving": {key: old[key]-new[key] for key in
                ("normalized_tokens", "ast_nodes", "normalized_bytes")},
              "in_process_cases": len(all_cases), "public_cli_runs": len(receipts), "failures": 0,
              "cases": all_cases, "public_runs": receipts,
              "limits": "Finite tests supplement the written source proof. Neither source beats the compact native frontier. No proof-assistant verification is claimed."}
    (ROOT/"validation.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({key: result[key] for key in ("profiles", "saving", "in_process_cases", "public_cli_runs", "failures")}, indent=2))

if __name__ == "__main__":
    main()
