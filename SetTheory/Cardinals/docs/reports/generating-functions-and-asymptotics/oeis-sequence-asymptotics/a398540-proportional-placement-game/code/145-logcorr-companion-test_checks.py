#!/usr/bin/env python3
"""Isolated, deterministic adversarial tests; no assert statements.

Run with both python -I test_checks.py and python -I -O test_checks.py.
"""

import copy
from fractions import Fraction
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("report145_checks", HERE / "checks.py")
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load checks.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)


class TestFailure(Exception):
    pass


def require(condition, message):
    if not condition:
        raise TestFailure(message)


def expect_error(call, description):
    try:
        call()
    except checks.CheckError:
        return
    raise TestFailure("accepted forbidden case: " + description)


def at(value, path):
    for item in path:
        value = value[item]
    return value


def replace(value, path, new):
    if not path:
        return new
    parent = at(value, path[:-1])
    parent[path[-1]] = new
    return value


def objects(value, path=()):
    if type(value) is dict:
        yield path, value
        for key, child in value.items():
            yield from objects(child, path + (key,))
    elif type(value) is list:
        for index, child in enumerate(value):
            yield from objects(child, path + (index,))


def integer_paths(value, path=()):
    if type(value) is int:
        yield path
    elif type(value) is dict:
        for key, child in value.items():
            yield from integer_paths(child, path + (key,))
    elif type(value) is list:
        for index, child in enumerate(value):
            yield from integer_paths(child, path + (index,))


def main():
    require(sys.flags.isolated == 1, "run this suite with python -I")
    base = json.loads((HERE / "fixture.json").read_text(encoding="utf-8"))
    counts = {"positive": 0, "semantic_mutations": 0, "structural_rejections": 0,
              "output_guards": 0, "cli_checks": 0}
    with tempfile.TemporaryDirectory(prefix="report145-test-") as temporary:
        tmp = Path(temporary)
        fixture = tmp / "candidate.json"

        def reject(value, category="structural_rejections"):
            fixture.write_text(json.dumps(value), encoding="utf-8")
            expect_error(lambda: checks.verify(fixture), category)
            counts[category] += 1

        def reject_raw(text):
            fixture.write_text(text, encoding="utf-8")
            expect_error(lambda: checks.verify(fixture), "invalid JSON encoding or values")
            counts["structural_rejections"] += 1

        expected_receipt = checks.verify(HERE / "fixture.json")
        require(expected_receipt["status"] == "passed", "baseline did not pass")
        require(expected_receipt["first_correction"] == "1/4", "wrong first coefficient")
        require(expected_receipt["logarithmic_correction"] == "-7/540", "wrong logarithmic coefficient")
        require(expected_receipt["B2_rational_part"] == "-59/12960", "wrong rational part of B2")
        require(expected_receipt["ratio_second_coefficient"] == "-3/8", "wrong second ratio coefficient")
        require(expected_receipt["ratio_difference_leading_coefficient"] == "-1/2", "wrong ratio difference coefficient")
        counts["positive"] += 1
        fixture.write_text(json.dumps(base, sort_keys=True, separators=(",", ":")), encoding="utf-8")
        require(checks.verify(fixture) == expected_receipt, "canonical receipt depends on JSON formatting")
        counts["positive"] += 1

        # Every rational scalar is mutated to a different canonical value.
        fraction_paths = [path for path, obj in objects(base) if set(obj) == {"numerator", "denominator"}]
        for path in fraction_paths:
            old = at(base, path)
            new = Fraction(old["numerator"], old["denominator"]) + 1
            changed = replace(copy.deepcopy(base), path, {"numerator": new.numerator, "denominator": new.denominator})
            reject(changed, "semantic_mutations")

        # Mutate inverse monomial positions while retaining a structurally
        # canonical, sorted list. Remove each term; inject an additional term.
        terms_path = ("inverse_residual", "terms")
        for index in range(len(at(base, terms_path))):
            changed = copy.deepcopy(base)
            del at(changed, terms_path)[index]
            reject(changed, "semantic_mutations")
        changed = copy.deepcopy(base)
        changed["inverse_residual"]["terms"].insert(0, {"t": 1, "log": 0, "lambda_inverse": 0, "k": 0,
                                                        "coefficient": {"numerator": 1, "denominator": 1}})
        reject(changed, "semantic_mutations")
        for index in range(len(at(base, terms_path))):
            exponent_names = ("t", "log", "lambda_inverse", "k")
            for name in exponent_names:
                changed = copy.deepcopy(base)
                terms = at(changed, terms_path)
                term = terms[index]
                other_keys = {tuple(item[key] for key in exponent_names)
                              for i, item in enumerate(terms) if i != index}
                old_value = term[name]
                found = False
                for new_value in range(1 if name == "t" else 0, 5):
                    term[name] = new_value
                    if new_value != old_value and tuple(term[key] for key in exponent_names) not in other_keys:
                        found = True
                        break
                require(found, "could not construct canonical exponent mutation")
                terms.sort(key=lambda item: tuple(item[key] for key in exponent_names))
                reject(changed, "semantic_mutations")

        # Close the schema at every object level, not just at its root.
        for path, obj in objects(base):
            changed = copy.deepcopy(base)
            at(changed, path)["unexpected"] = None
            reject(changed)
            for key in obj:
                changed = copy.deepcopy(base)
                del at(changed, path)[key]
                reject(changed)
            reject(replace(copy.deepcopy(base), path, []))

        # bool is an int subclass in Python; every integer slot must reject it.
        for path in integer_paths(base):
            reject(replace(copy.deepcopy(base), path, True))
            reject(replace(copy.deepcopy(base), path, False))
            reject(replace(copy.deepcopy(base), path, 1.0))
            reject(replace(copy.deepcopy(base), path, "1"))
        for path in fraction_paths:
            old = at(base, path)
            for denominator in (0, -old["denominator"]):
                reject(replace(copy.deepcopy(base), path + ("denominator",), denominator))
            reject(replace(copy.deepcopy(base), path, {"numerator": 2 * old["numerator"], "denominator": 2 * old["denominator"]}))
        for bad in (None, True, [], "fixture", 1):
            reject(bad)
        for bad in (None, {}, True, "terms"):
            reject(replace(copy.deepcopy(base), terms_path, bad))
        reject(replace(copy.deepcopy(base), ("schema",), "report145-exact-v3"))
        reject(replace(copy.deepcopy(base), ("inverse_residual", "order"), 3))
        changed = copy.deepcopy(base)
        changed["inverse_residual"]["terms"].reverse()
        reject(changed)
        changed = copy.deepcopy(base)
        changed["inverse_residual"]["terms"].insert(0, copy.deepcopy(changed["inverse_residual"]["terms"][0]))
        reject(changed)
        reject(replace(copy.deepcopy(base), terms_path + (0, "coefficient"), {"numerator": 0, "denominator": 1}))
        for slot in ("t", "log", "lambda_inverse", "k"):
            for bad in (-1, 5):
                reject(replace(copy.deepcopy(base), terms_path + (0, slot), bad))
        for bad in ("NaN", "Infinity", "-Infinity", "1e999", "1.25"):
            reject_raw(json.dumps(base).replace('"order": 4', '"order": ' + bad))
        reject_raw('{"schema":"report145-exact-v2","schema":"report145-exact-v2"}')
        reject_raw(json.dumps(base).replace('"numerator": 1, "denominator": 3', '"numerator": 1, "numerator": 1, "denominator": 3', 1))
        reject_raw('{"schema":')
        reject_raw(json.dumps(base) + "\n{}")
        reject_raw(" " * 65537)
        fixture.write_bytes(b"\xff")
        expect_error(lambda: checks.verify(fixture), "invalid UTF-8")
        counts["structural_rejections"] += 1
        expect_error(lambda: checks.verify(tmp / "missing.json"), "missing fixture")
        counts["structural_rejections"] += 1

        # Verify all stated output guards and that refused targets stay intact.
        ordinary = tmp / "new-receipt.json"
        checks.write_new_file(ordinary, "new\n")
        require(ordinary.read_text() == "new\n", "receipt content differs")
        counts["output_guards"] += 1
        expect_error(lambda: checks.write_new_file(ordinary, "overwrite"), "existing file")
        require(ordinary.read_text() == "new\n", "existing file changed")
        counts["output_guards"] += 1
        existing_dir = tmp / "directory"
        existing_dir.mkdir()
        expect_error(lambda: checks.write_new_file(existing_dir, "overwrite"), "existing directory")
        counts["output_guards"] += 1
        target_link = tmp / "target-link"
        target_link.symlink_to(ordinary)
        expect_error(lambda: checks.write_new_file(target_link, "overwrite"), "target symlink")
        require(ordinary.read_text() == "new\n", "symlink referent changed")
        counts["output_guards"] += 1
        broken_link = tmp / "broken-link"
        broken_link.symlink_to(tmp / "missing-target")
        expect_error(lambda: checks.write_new_file(broken_link, "create"), "dangling target symlink")
        require(not (tmp / "missing-target").exists(), "dangling symlink referent created")
        counts["output_guards"] += 1
        parent_link = tmp / "parent-link"
        parent_link.symlink_to(existing_dir, target_is_directory=True)
        expect_error(lambda: checks.write_new_file(parent_link / "unsafe.json", "create"), "symlink parent")
        require(not (existing_dir / "unsafe.json").exists(), "wrote through symlink parent")
        counts["output_guards"] += 1
        for bad in ("", str(tmp) + "/", str(tmp) + "/directory/../escape", str(tmp) + "/bad\x00name", str(tmp / "absent" / "new.json")):
            expect_error(lambda bad=bad: checks.write_new_file(bad, "create"), "invalid output path")
            counts["output_guards"] += 1
        nested = existing_dir / "nested.json"
        checks.write_new_file(nested, "nested\n")
        require(nested.read_text() == "nested\n", "ordinary nested write failed")
        counts["output_guards"] += 1

        # An independent process in the same isolation/optimization mode must
        # produce exactly the same receipt, then reject overwrite and mutation.
        command = [sys.executable, "-I"]
        if sys.flags.optimize:
            command.append("-O")
        command.append(str(HERE / "checks.py"))
        result = subprocess.run(command, capture_output=True, text=True, check=False)
        require(result.returncode == 0 and result.stderr == "", "baseline CLI failed")
        require(json.loads(result.stdout) == expected_receipt, "CLI receipt differs")
        counts["cli_checks"] += 1
        receipt_file = tmp / "cli-receipt.json"
        result2 = subprocess.run(command + ["--receipt", str(receipt_file)], capture_output=True, text=True, check=False)
        require(result2.returncode == 0 and result2.stdout == result.stdout, "CLI receipt creation failed")
        require(receipt_file.read_text() == result.stdout, "receipt file differs from stdout")
        counts["cli_checks"] += 1
        refused = subprocess.run(command + ["--receipt", str(receipt_file)], capture_output=True, text=True, check=False)
        require(refused.returncode == 1 and refused.stdout == "" and refused.stderr.startswith("CHECK FAILED:"), "CLI did not reject overwrite cleanly")
        counts["cli_checks"] += 1
        changed = copy.deepcopy(base)
        changed["coefficients"]["logarithmic"] = {"numerator": -1, "denominator": 1}
        fixture.write_text(json.dumps(changed), encoding="utf-8")
        rejected_receipt = tmp / "must-not-exist.json"
        refused = subprocess.run(command + ["--fixture", str(fixture), "--receipt", str(rejected_receipt)], capture_output=True, text=True, check=False)
        require(refused.returncode == 1 and refused.stdout == "" and refused.stderr.startswith("CHECK FAILED:"), "CLI accepted semantic mutation")
        require(not rejected_receipt.exists(), "failed verification created a receipt")
        counts["cli_checks"] += 1

    output = {"schema": "report145-test-receipt-v2", "status": "passed",
              "isolated": True, "optimized": bool(sys.flags.optimize),
              "counts": counts, "total_cases": sum(counts.values())}
    sys.stdout.write(json.dumps(output, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (TestFailure, checks.CheckError) as exc:
        sys.stderr.write("TEST FAILED: " + str(exc) + "\n")
        sys.exit(1)
