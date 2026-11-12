"""Regenerate finite certificate, scope, guard, substitution, and size evidence.

These are implementation regressions, not a machine-checked proof of the
metatheorem.  Every acceptance check uses a fresh standalone process and the
same exact output/exit-status contract, both normally and under Python -O.
"""
import ast
import copy
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize
import zlib

import generate_fixtures

ROOT = Path(__file__).resolve().parents[1]
TESTS = ROOT / "tests"
EVIDENCE = ROOT / "evidence"
NAMES = ("native", "diagonal", "witness")
Z = ["z"]
V = ["v", 0]
SV = ["s", V]


def load_kernel(name):
    spec = importlib.util.spec_from_file_location(f"measured_{name}", ROOT / "code" / f"{name}_checker.py")
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def cli(name, c, optimized):
    command = [sys.executable] + (["-O"] if optimized else [])
    command += [str(ROOT / "code" / f"{name}_checker.py")]
    p = subprocess.run(command, input=json.dumps(c), capture_output=True, text=True, timeout=30)
    return {"accepted": p.returncode == 0 and p.stdout == "ACCEPT\n",
            "returncode": p.returncode, "stdout": p.stdout,
            "stderr": p.stderr if p.returncode else ""}


def negative_cases():
    good = json.loads((TESTS / "certificates/nested_reflexivity.json").read_text())
    cases = []

    def change(name, update):
        c = copy.deepcopy(good)
        update(c)
        cases.append((name, c))

    change("boolean_variable_count", lambda c: c.update(variables=True))
    change("negative_variable_count", lambda c: c.update(variables=-1))
    change("floating_variable_count", lambda c: c.update(variables=1.0))
    change("free_variable_in_closed_goal", lambda c: c.update(goal=["=", V, V]))
    change("boolean_variable_index", lambda c: c.update(variables=1, goal=["=", ["v", True], Z]))
    change("boolean_hypothesis_index", lambda c: c.update(context=[c["goal"]], proof=["hyp", False]))
    change("negative_hypothesis_index", lambda c: c.update(context=[c["goal"]], proof=["hyp", -1]))
    change("unknown_rule", lambda c: c.update(proof=["oracle", c["goal"]]))
    change("extra_top_level_field", lambda c: c.update(axioms=[]))
    change("forged_computation_endpoint", lambda c: c.update(goal=["=", Z, ["s", Z]], proof=["zero", Z, Z]))
    change("malformed_instruction", lambda c: c.update(proof=["zero", Z]))
    change("escaping_iterator_state", lambda c: c.update(proof=["zero", Z, ["v", 1]]))
    change("escaping_DI_witness", lambda c: c.update(proof=["di", ["=", V, V], V, ["hyp", 0]]))
    d = json.loads((TESTS / "certificates/compound_D_case.json").read_text())
    change("escaping_DE_conclusion", lambda c: c.update(proof=["de", ["=", V, V], d["proof"], ["hyp", 0]]))
    identity = json.loads((TESTS / "certificates/identity_closure.json").read_text())
    change("wrong_closure_base", lambda c: c.update(goal=["=", Z, Z],
        proof=["qe", Z, identity["proof"], ["zero", ["s", Z], Z]]))
    compound = ["d", ["=", Z, Z]]
    change("forbidden_compound_induction", lambda c: c.update(goal=["q", compound],
        proof=["qi", compound, ["hyp", 0]]))
    attack = {"variables": 1, "context": [["=", V, Z]], "goal": ["q", ["=", V, Z]],
              "proof": ["qi", ["=", V, Z], ["hyp", 1]]}
    cases.append(("induction_context_capture", attack))
    directory = TESTS / "negative_certificates"
    directory.mkdir(exist_ok=True)
    for name, c in cases:
        (directory / f"{name}.json").write_text(json.dumps(c, separators=(",", ":")) + "\n")
    return cases


def random_term(rng, variables, depth, bounded_counter=False):
    if not depth or rng.randrange(5) == 0:
        return ["v", rng.randrange(variables)] if variables and rng.randrange(2) else Z
    if rng.randrange(3) == 0:
        return ["s", random_term(rng, variables, depth - 1, bounded_counter)]
    counter = rng.choice([Z, ["s", Z], ["s", ["s", Z]]]) if bounded_counter else random_term(rng, variables, 0)
    return ["i", counter, random_term(rng, variables, depth - 1, bounded_counter),
            random_term(rng, variables + 1, depth - 1, bounded_counter)]


def guard(a):
    return a[0] == "=" and a[1][:3] == a[2][:3] == ["i", V, V]


def zero_guard(a):
    return a[0] == "=" and a[1][:3] == a[2][:3] == ["i", V, Z]


def guard_regressions(kernel):
    rng = random.Random(20261111)
    counts = {"parameter_substitution": 0, "witness_opening": 0,
              "guarded_inputs": 0, "unguarded_inputs": 0}
    examples = []
    for n in range(1, 5):
        for trial in range(30):
            h, k = random_term(rng, n + 3, 3), random_term(rng, n + 3, 3)
            mode = trial % 6
            if mode == 0:
                b = ["=", ["i", V, V, h], ["i", V, V, k]]
            elif mode == 1:
                b = ["=", ["i", V, ["v", 2], h], ["i", V, ["v", 2], k]]
            elif mode == 2:
                b = ["=", ["i", ["v", 2], V, h], ["i", ["v", 2], V, k]]
            elif mode == 3:
                b = ["=", ["v", 2], ["i", V, V, k]]
            elif mode == 4:
                b = ["q", ["=", random_term(rng, n + 3, 3), random_term(rng, n + 3, 3)]]
            else:
                b = ["d", ["=", random_term(rng, n + 4, 3), random_term(rng, n + 4, 3)]]
            kernel.formula(b, n + 2)
            before = guard(b)
            counts["guarded_inputs" if before else "unguarded_inputs"] += 1
            image = random_term(rng, n - 1, 3)
            after = kernel.sub(["d", b], image)[1]
            kernel.formula(after, n + 1)
            if guard(after) != before:
                raise AssertionError("Diagonal guard changed under parameter substitution")
            counts["parameter_substitution"] += 1
            witness = random_term(rng, n, 3)
            opened = kernel.sub(["q", b], witness)[1]
            kernel.formula(opened, n + 1)
            if guard(opened) != before:
                raise AssertionError("Diagonal guard changed under witness opening")
            counts["witness_opening"] += 1
            if trial < 2 and n == 1:
                examples.append({"matrix": b, "image": image, "substituted": after,
                                 "witness": witness, "opened": opened, "guarded": before})
    b = ["=", ["i", V, ["v", 1], Z], ["i", V, ["v", 1], ["s", Z]]]
    opened = kernel.sub(["q", b], Z)[1]
    if zero_guard(b) or not zero_guard(opened) or guard(b) or guard(opened):
        raise AssertionError("Expected zero-seed guard instability witness was lost")
    counterexample = {"matrix": b, "zero_witness": Z, "opened": opened,
                      "zero_seed_guard_before": zero_guard(b), "zero_seed_guard_after": zero_guard(opened),
                      "diagonal_guard_before": guard(b), "diagonal_guard_after": guard(opened)}
    return {"counts": counts, "examples": examples, "zero_seed_counterexample": counterexample,
            "boundary": "Finite regressions; the report gives the structural preservation-and-reflection proof."}


def evaluate(t, environment):
    if t[0] == "z":
        return 0
    if t[0] == "v":
        return environment[t[1]]
    if t[0] == "s":
        return 1 + evaluate(t[1], environment)
    count = evaluate(t[1], environment)
    value = evaluate(t[2], environment)
    for _ in range(count):
        value = evaluate(t[3], [value] + environment)
    return value


def substitution_regressions(kernel):
    rng = random.Random(20261112)
    total = 0
    for n in range(4):
        for _ in range(20):
            a = random_term(rng, n + 1, 3, bounded_counter=True)
            t = random_term(rng, n, 2, bounded_counter=True)
            environment = [rng.randrange(3) for _ in range(n)]
            left = evaluate(kernel.sub(a, t), environment)
            right = evaluate(a, [evaluate(t, environment)] + environment)
            if left != right:
                raise AssertionError("Capture-free substitution disagrees with independent N semantics")
            total += 1
    return {"checks": total, "mismatches": 0, "budget_skips": 0,
            "boundary": "Independent standard-natural-number evaluation of bounded-counter samples."}


def metrics():
    result = {}
    destination = EVIDENCE / "normalized_gzip9"
    destination.mkdir(exist_ok=True)
    ignored = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
               tokenize.DEDENT, tokenize.COMMENT, tokenize.ENDMARKER}
    for name in NAMES:
        path = ROOT / "code" / f"{name}_checker.py"
        source = path.read_text()
        normalized = ast.unparse(ast.parse(source)) + "\n"
        encoded = normalized.encode()
        compressed = gzip.compress(encoded, compresslevel=9, mtime=0)
        (destination / f"{name}_checker.py.gz").write_bytes(compressed)
        result[path.name] = {"raw_bytes": len(source.encode()), "normalized_bytes": len(encoded),
            "tokens": sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
            "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
            "gzip9_bytes": len(compressed), "sha256": hashlib.sha256(source.encode()).hexdigest()}
    receipt = {"python": sys.version, "zlib": zlib.ZLIB_RUNTIME_VERSION, "metrics": result,
               "protocol": "ast.unparse plus final newline; complete modules including JSON I/O and ACCEPT output; gzip level 9, mtime=0"}
    (EVIDENCE / "checker_metrics.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main():
    EVIDENCE.mkdir(exist_ok=True)
    fixtures = generate_fixtures.build()
    negative = negative_cases()
    outcomes = []
    for row in fixtures:
        certificate = json.loads((TESTS / "certificates" / row["file"]).read_text())
        for name in NAMES:
            for optimized in (False, True):
                outcome = cli(name, certificate, optimized)
                outcome.update(fixture=row["file"], kernel=name, optimized=optimized,
                               expected=row["expected"][name])
                outcomes.append(outcome)
                if outcome["accepted"] != outcome["expected"]:
                    raise AssertionError(f"Certificate mismatch: {outcome}")
    for label, certificate in negative:
        for name in NAMES:
            for optimized in (False, True):
                outcome = cli(name, certificate, optimized)
                outcome.update(fixture=label, kernel=name, optimized=optimized, expected=False)
                outcomes.append(outcome)
                if outcome["accepted"]:
                    raise AssertionError(f"Invalid certificate accepted: {outcome}")
    kernel = load_kernel("diagonal")
    guard_evidence = guard_regressions(kernel)
    substitution_evidence = substitution_regressions(kernel)
    measured = metrics()
    translated = subprocess.run([sys.executable, str(TESTS / "test_translation.py")],
                                capture_output=True, text=True, timeout=60)
    if translated.returncode:
        raise RuntimeError("Proof-translation regression failed:\n" + translated.stdout + translated.stderr)
    translation = json.loads((EVIDENCE / "translation_tests.json").read_text())
    translation_cli = 2 * sum("normal_and_optimized_cli" in x for x in translation["cases"])
    translation_module = translation["checker_executions"] - translation_cli
    (EVIDENCE / "guard_substitution.json").write_text(json.dumps(guard_evidence, indent=2) + "\n")
    (EVIDENCE / "semantic_substitution.json").write_text(json.dumps(substitution_evidence, indent=2) + "\n")
    summary = {"named_fixtures": len(fixtures), "negative_fixtures": len(negative),
               "standalone_cli_checks": len(outcomes), "optimized_cli_checks": sum(x["optimized"] for x in outcomes),
               "mismatches": 0, "guard_checks": guard_evidence["counts"],
               "semantic_substitution": substitution_evidence,
               "translation_cases": translation["certificate_cases"],
               "translation_direct_module_checks": translation_module,
               "translation_cli_checks": translation_cli,
               "total_cli_checks": len(outcomes) + translation_cli,
               "boundary": "Finite regression evidence. The mathematical equivalence is a written proof, not proof-assistant verification."}
    (EVIDENCE / "checker_validation.json").write_text(json.dumps({"summary": summary, "outcomes": outcomes}, indent=2) + "\n")
    total_guard = guard_evidence["counts"]["parameter_substitution"] + guard_evidence["counts"]["witness_opening"]
    latex = (
        f"The reproducible implementation checks used {len(fixtures)} named proof fixtures and "
        f"{len(negative)} additional malformed or scope-attack fixtures. Every fixture ran against "
        "all three standalone checkers, both normally and under \\texttt{python -O}: "
        f"{len(outcomes)} processes in total, with zero mismatches. The positive fixtures include "
        "a diagonal-guard induction whose hypothesis is used, the derived identity closure "
        "$Q_y(I(y,0;u.Su)=y)$, nonvacuous existential elimination, compound $Q$ and $D$ matrices, "
        "and a nested capture-avoiding witness. Expected rejections distinguish ordinary atomic "
        "cases from progress, reject a premature eigenvariable, and reject unrestricted compound induction.\n\n"
        f"There were also {total_guard} finite checks of guard preservation and reflection "
        "under parameter substitution or witness opening, together with an explicit counterexample "
        "to stability of the older zero-seed guard. Independent standard-natural-number evaluation "
        f"confirmed {substitution_evidence['checks']} capture-free term substitutions, with no mismatches or budget skips. "
        "These tests check the implementation and boundary conditions; they do not replace the written metatheory.\n")
    (EVIDENCE / "validation_summary.tex").write_text(latex)
    print(json.dumps({"validation": summary, "metrics": measured["metrics"]}, indent=2))


if __name__ == "__main__":
    main()
