"""Meaningful regression tests for rules, scoping, and both proof translations."""
import importlib.util
import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))
import strict_old as old
import strict_q as new
from translate import counts, translate

Z = ["z"]
V = lambda index: ["v", index]
S = lambda term: ["s", term]
E = lambda left, right: ["e", left, right]
I = lambda counter, seed, update: ["i", counter, seed, update]
Q = lambda formula: ["q", formula]
D = lambda formula: ["d", formula]


def numeral(value):
    result = Z
    for _ in range(value):
        result = S(result)
    return result


def reflexivity(term):
    source = ["zero", term, Z]
    return ["tr", E(V(0), new.shift(term)), source, source]


def iteration_step(seed):
    # The free variable 0 is the induction counter; other variables are parameters.
    counter = V(0)
    computation = ["succ", counter, seed, V(0)]
    template = E(I(S(V(1)), new.shift(seed), V(0)), V(0))
    return ["tr", template, ["hyp", 0], computation]


def document(module, proof, parameters=0, context=None):
    context = [] if context is None else context
    return {
        "parameters": parameters,
        "context": context,
        "goal": module.derive(proof, context, parameters),
        "proof": proof,
    }


def main():
    examples = ROOT / "tests" / "certificates"
    examples.mkdir(exist_ok=True)
    records = []
    qcases = {}
    oldcases = {}
    common = {
        "zero": ["zero", S(Z), V(0)],
        "successor_zero": ["succ", Z, S(Z), V(0)],
        "reflexivity": reflexivity(S(S(Z))),
        "d_case": ["case", E(V(0), V(0)), Z, reflexivity(S(V(0)))],
    }
    for name, proof in common.items():
        qcases[name] = document(new, proof)
        oldcases[name] = document(old, proof)

    equation = E(I(V(0), Z, V(0)), Z)
    qproof = ["prog", equation, iteration_step(Z)]
    qcases["closure_progress"] = document(new, qproof)
    qcases["equation_induction"] = document(new,
        ["qe", numeral(3), qproof, ["zero", Z, V(0)]])
    matrix = E(I(V(0), V(1), V(0)), V(1))
    oldcases["witnessed_progress"] = document(old,
        ["prog", matrix, S(Z), iteration_step(S(Z))])
    oldcases["parameter_progress"] = document(old,
        ["prog", matrix, V(0), iteration_step(V(1))], parameters=1)

    # DE actually uses its fresh closure, rather than discarding its premise.
    paired = common["d_case"]
    conclusion = E(S(Z), S(Z))
    branch = ["qe", S(Z), ["hyp", 0], reflexivity(Z)]
    elimination = ["de", conclusion, paired, branch]
    qcases["d_elimination"] = document(new, elimination)
    oldcases["d_elimination"] = document(old, elimination)

    # Formula transport with the changed occurrence below both binders.
    term_equality = ["zero", S(Z), V(0)]
    left = I(Z, S(Z), V(0))
    form = D(Q(E(V(3), V(3))))
    hypothesis = new.instantiate(form, left)
    transported = ["tr", form, term_equality, ["hyp", 0]]
    qcases["transport_beneath_binders"] = document(new, transported, context=[hypothesis])
    oldcases["transport_beneath_binders"] = document(old, transported, context=[hypothesis])

    # A retained context is preserved; review_strict.py additionally uses Hyp1 itself.
    parameter_equation = E(I(V(0), V(1), V(0)), V(1))
    context = [E(V(0), V(0))]
    retained_step = ["tr", E(I(S(V(1)), V(2), V(0)), V(0)),
                     ["hyp", 0], ["succ", V(0), V(1), V(0)]]
    qcases["progress_with_context"] = document(new,
        ["prog", parameter_equation, retained_step], parameters=1, context=context)

    for label, cases, source, target, direction in [
        ("q", qcases, new, old, "q-to-old"),
        ("old", oldcases, old, new, "old-to-q"),
    ]:
        for name, cert in cases.items():
            source.check(cert)
            converted = translate(cert, direction)
            target.check(converted)
            inverse = "old-to-q" if direction == "q-to-old" else "q-to-old"
            roundtrip = translate(converted, inverse)
            source.check(roundtrip)
            before, progress = counts(cert["proof"])
            after, _ = counts(converted["proof"])
            expected = before + (2 if label == "q" else 3) * progress
            if after != expected or cert["goal"] != converted["goal"]:
                raise RuntimeError("translation invariant failed")
            entries = [(label, cert), ("old" if label == "q" else "q", converted)]
            for target_label, item in entries:
                path = examples / f"{label}_{name}_{target_label}.json"
                path.write_text(json.dumps(item, indent=2) + "\n")
                program = ROOT / "code" / f"strict_{target_label}.py"
                for optimized in (False, True):
                    command = [sys.executable] + (["-O"] if optimized else []) + [str(program)]
                    process = subprocess.run(command, input=json.dumps(item), text=True,
                                             capture_output=True, timeout=10)
                    if process.returncode or process.stdout.strip() != "ACCEPT":
                        raise RuntimeError(f"public checker failed: {path}\n{process.stderr}")
            records.append({"name": f"{label}/{name}", "nodes": before,
                            "progress_nodes": progress, "translated_nodes": after})

    controls = []
    wrong_goal = deepcopy(qcases["reflexivity"])
    wrong_goal["goal"] = E(Z, S(Z))
    controls.append(("wrong_conclusion", wrong_goal, new))
    bad_var = deepcopy(qcases["zero"])
    bad_var["proof"][1] = V(0)
    controls.append(("unscoped_seed", bad_var, new))
    boolean_var = deepcopy(qcases["zero"])
    boolean_var["proof"][2] = V(False)
    controls.append(("boolean_variable_index", boolean_var, new))
    negative_hyp = deepcopy(qcases["reflexivity"])
    negative_hyp["proof"] = ["hyp", -1]
    controls.append(("negative_hypothesis", negative_hyp, new))
    compound = {"parameters": 0, "context": [], "goal": Q(Q(E(V(0), V(0)))),
                "proof": ["prog", Q(E(V(0), V(0))), ["hyp", 0]]}
    controls.append(("compound_progress", compound, new))
    bad_de = deepcopy(qcases["d_elimination"])
    bad_de["proof"][1] = E(V(0), V(0))
    controls.append(("escaped_elimination_witness", bad_de, new))
    bad_old = deepcopy(oldcases["witnessed_progress"])
    bad_old["proof"][1] = Q(E(V(0), V(0)))
    controls.append(("old_compound_progress", bad_old, old))
    for name, cert, module in controls:
        try:
            module.check(cert)
        except (ValueError, TypeError, IndexError, KeyError):
            pass
        else:
            raise RuntimeError(f"negative control accepted: {name}")
        program = ROOT / "code" / ("strict_old.py" if module is old else "strict_q.py")
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else []) + [str(program)]
            process = subprocess.run(command, input=json.dumps(cert), text=True,
                                     capture_output=True, timeout=10)
            if process.returncode == 0 or "ACCEPT" in process.stdout:
                raise RuntimeError(f"public negative control accepted: {name}")

    receipt = {
        "positive_derivations": len(records),
        "translation_and_roundtrip_checks": 2 * len(records),
        "positive_cli_runs": 4 * len(records),
        "negative_controls": len(controls),
        "negative_cli_runs": 2 * len(controls),
        "failures": 0,
        "records": records,
        "limitation": "Finite regression evidence; universal equivalence is proved in report.tex.",
    }
    destination = ROOT / "evidence" / "strict_validation.json"
    destination.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: value for key, value in receipt.items() if key != "records"}, indent=2))


if __name__ == "__main__":
    main()
