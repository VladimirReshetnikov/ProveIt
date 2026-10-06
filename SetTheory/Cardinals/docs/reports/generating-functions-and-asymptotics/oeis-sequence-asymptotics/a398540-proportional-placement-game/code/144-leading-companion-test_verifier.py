#!/usr/bin/env python3
"""Deterministic adversarial tests. Run with python -I, with or without -O."""
import sys
if not sys.flags.isolated:
    raise SystemExit("Refusing non-isolated startup. Run: python -I test_verifier.py")

import copy
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import tempfile
from fractions import Fraction

HERE = Path(__file__).resolve().parent
V = runpy.run_path(str(HERE / "verify_certificate.py"), run_name="verified_absolute_source")
require = V["require"]
Error = V["VerificationError"]
tests = []


def passed(name):
    require(name not in tests, "Duplicate test name")
    tests.append(name)


def rejects(name, operation):
    try:
        operation()
    except (Error, OSError):
        passed(name)
        return
    raise Error("Rejected-input test unexpectedly passed: " + name)


def mutate(data, path, value):
    result = copy.deepcopy(data)
    node = result
    for part in path[:-1]:
        node = node[part]
    node[path[-1]] = value
    return result


def set_digest(data):
    data["vector_sha256"] = V["vector_digest"](data["probabilities"])
    return data


def main():
    fixture = HERE / "fixtures" / "rate_certificate.json"
    tracked = [HERE / "verify_certificate.py", HERE / "test_verifier.py", fixture]
    source_hashes = {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in tracked}
    data, raw = V["load_fixture"](fixture)
    expected = V["generate_certificate"]()
    V["validate_fixture"](data, expected)
    require(V["canonical_json_bytes"](data) == raw, "Bundled fixture bytes are not canonical")
    passed("fresh_two_route_recomputation_and_canonical_fixture")

    def reject_data(name, changed):
        rejects(name, lambda: V["validate_fixture"](changed, expected))

    # Closed fields at every object level.
    for where in ((), ("parameters",), ("certificate_values",), ("checks",)):
        label = "root" if not where else where[0]
        changed = copy.deepcopy(data)
        node = changed if not where else changed[where[0]]
        node["unknown_field"] = 0
        reject_data("unknown_field_" + label, changed)
        changed = copy.deepcopy(data)
        node = changed if not where else changed[where[0]]
        del node[next(iter(node))]
        reject_data("missing_field_" + label, changed)

    # Duplicate names are rejected at parse time, including identical values.
    for field in ("schema", "m", "upper_auxiliary_bound", "known_prefix_matches"):
        token = json.dumps(field).encode("ascii") + b":"
        replacement = json.dumps(field).encode("ascii") + b': null, ' + token
        duplicate = raw.replace(token, replacement, 1)
        require(duplicate != raw, "Duplicate-field test did not modify bytes")
        rejects("duplicate_field_" + field, lambda duplicate=duplicate: V["parse_fixture"](duplicate))

    integer_paths = [("last_probability_index",), ("number_of_probabilities",),
                     ("parameters", "m"), ("parameters", "N"),
                     ("parameters", "square_root_lower_scale"),
                     ("square_root_floors", 0),
                     ("checks", "polynomial_weights_checked_with_reflections")]
    for index, path in enumerate(integer_paths):
        reject_data("boolean_is_not_integer_%d" % index, mutate(data, path, True))
        reject_data("string_is_not_integer_%d" % index, mutate(data, path, "101"))
        reject_data("negative_integer_%d" % index, mutate(data, path, -1))

    for field, value in data["checks"].items():
        if type(value) is bool:
            reject_data("integer_is_not_boolean_" + field, mutate(data, ("checks", field), 1))
            reject_data("false_check_" + field, mutate(data, ("checks", field), False))

    malformed_rationals = ["", "1", "1/0", "01/1", "1/01", "A/1", "0x1/1",
                           "+1/1", "-1/1", "1/-1", "1/1 ", " 1/1", "1 /1",
                           "2/2", "0/2", "1/1\n", "1.0/1", "1/1/1", True, 1, None]
    for index, value in enumerate(malformed_rationals):
        reject_data("malformed_rational_%d" % index, mutate(data, ("probabilities", 0), value))
    for path in (("parameters", "strict_lower_bound"), ("prefix", 0),
                 ("certificate_values", "upper_left_hand_side")):
        reject_data("malformed_rational_at_" + "_".join(map(str, path)), mutate(data, path, "2/2"))

    for token in (b"100.0", b"1e2", b"NaN", b"Infinity", b"-Infinity"):
        changed = raw.replace(b'"last_probability_index": 100', b'"last_probability_index": ' + token, 1)
        require(changed != raw, "Noninteger JSON test did not modify bytes")
        rejects("forbidden_json_number_" + token.decode("ascii"), lambda changed=changed: V["parse_fixture"](changed))
    for index, malformed in enumerate((b"true", b"[]", b"{}", b"\xff", b"{", b"{} {}")):
        rejects("invalid_root_or_encoding_%d" % index, lambda malformed=malformed: V["parse_fixture"](malformed))
    rejects("fixture_size_limit", lambda: V["parse_fixture"](b" " * (V["MAX_FIXTURE_BYTES"] + 1)))

    # Rehashing the entire mutated fixture does not make its semantics valid.
    for index in (0, 5, 37, 100):
        changed = copy.deepcopy(data)
        value = V["decode_rational"](changed["probabilities"][index], "test")
        changed["probabilities"][index] = V["encode_rational"](value + Fraction(1, value.denominator))
        if index < len(changed["prefix"]):
            changed["prefix"][index] = changed["probabilities"][index]
        set_digest(changed)
        require(hashlib.sha256(V["canonical_json_bytes"](changed)).hexdigest()
                != hashlib.sha256(raw).hexdigest(), "Mutation must alter fixture hash")
        reject_data("semantic_probability_mutation_with_updated_vector_and_file_hash_%d" % index, changed)

    changes = [(("schema",), "report144-placement-rate-certificate-v2"),
               (("last_probability_index",), 99), (("number_of_probabilities",), 100),
               (("parameters", "m"), 100), (("parameters", "N"), 102),
               (("parameters", "square_root_lower_scale"), 10 ** 11),
               (("parameters", "kernel_upper_bound"), "2/1"),
               (("parameters", "strict_lower_bound"), V["encode_rational"](Fraction(263, 500))),
               (("parameters", "strict_upper_bound"), V["encode_rational"](Fraction(633, 1000))),
               (("square_root_floors", 33), data["square_root_floors"][33] + 1),
               (("certificate_values", "lower_right_hand_side"), "0/1"),
               (("certificate_values", "upper_left_hand_side"), "1/1"),
               (("certificate_values", "upper_auxiliary_bound"), "60/1"),
               (("prefix", 1), "2/1"), (("vector_serialization",), "changed"),
               (("vector_sha256",), "0" * 64),
               (("checks", "polynomial_weights_checked_with_reflections"), 2551)]
    for index, (path, value) in enumerate(changes):
        reject_data("semantic_field_mutation_%d" % index, mutate(data, path, value))
    for name in ("probabilities", "prefix", "square_root_floors"):
        reject_data("truncated_array_" + name, mutate(data, (name,), data[name][:-1]))
        reject_data("extended_array_" + name, mutate(data, (name,), data[name] + data[name][:1]))
        reject_data("wrong_array_type_" + name, mutate(data, (name,), {}))

    secure_output_supported = (os.open in os.supports_dir_fd and hasattr(os, "O_DIRECTORY")
                               and hasattr(os, "O_NOFOLLOW"))
    output_checks = "passed" if secure_output_supported else "unsupported_platform_fails_closed"
    with tempfile.TemporaryDirectory(prefix="report144-test-") as temporary:
        root = Path(temporary).resolve()
        if secure_output_supported:
            output_dir = root / "output"
            output_dir.mkdir()
            written = V["write_output"](str(output_dir), expected)
            require(written == output_dir / V["OUTPUT_FILENAME"], "Unexpected output path")
            require(written.read_bytes() == raw, "Written certificate differs")
            passed("exact_output_in_explicit_resolved_directory")
            rejects("existing_output_not_overwritten", lambda: V["write_output"](str(output_dir), expected))
            require(written.read_bytes() == raw, "Existing output was modified")
            outside = root / "outside"
            outside.mkdir()
            (root / "directory_link").symlink_to(outside, target_is_directory=True)
            rejects("symlink_output_directory_escape", lambda: V["write_output"](str(root / "directory_link"), expected))
            (outside / "nested").mkdir()
            rejects("symlink_ancestor_directory_escape", lambda: V["write_output"](str(root / "directory_link" / "nested"), expected))
            rejects("parent_traversal_escape", lambda: V["write_output"](str(output_dir / ".." / "outside"), expected))
            rejects("missing_output_directory", lambda: V["write_output"](str(root / "missing"), expected))
            rejects("empty_output_directory", lambda: V["write_output"]("", expected))
            rejects("source_tree_output_forbidden", lambda: V["write_output"](str(HERE), expected))
            rejects("fixture_tree_output_forbidden", lambda: V["write_output"](str(HERE / "fixtures"), expected))
            sentinel = outside / "sentinel.txt"
            sentinel.write_bytes(b"unchanged\n")
            links = root / "file_links"
            links.mkdir()
            (links / V["OUTPUT_FILENAME"]).symlink_to(sentinel)
            rejects("symlink_output_file_escape", lambda: V["write_output"](str(links), expected))
            require(sentinel.read_bytes() == b"unchanged\n", "Symlink target changed")
            (links / V["OUTPUT_FILENAME"]).unlink()
            os.link(sentinel, links / V["OUTPUT_FILENAME"])
            rejects("hardlink_output_file_not_overwritten", lambda: V["write_output"](str(links), expected))
            require(sentinel.read_bytes() == b"unchanged\n", "Hardlink target changed")
        else:
            rejects("unsupported_secure_output_fails_closed", lambda: V["write_output"](str(root), expected))

        # Both startup modes face poisoned current and script directories plus
        # PYTHONPATH/PYTHONHOME. -I must prevent code execution before or during imports.
        poison = root / "poisoned_startup"
        poison.mkdir()
        marker = root / "injection_was_executed"
        malicious = ("with open(" + repr(str(marker)) + ", 'w') as stream: stream.write('bad')\n"
                     "raise RuntimeError('Injected module executed')\n")
        for module in ("sitecustomize", "usercustomize", "json", "math", "fractions", "hashlib",
                       "pathlib", "argparse", "re", "os"):
            (poison / (module + ".py")).write_text(malicious, encoding="utf-8")
        copied = poison / "verify_certificate.py"
        shutil.copyfile(HERE / "verify_certificate.py", copied)
        environment = dict(os.environ)
        environment.update(PYTHONPATH=str(poison), PYTHONHOME=str(poison), PYTHONSTARTUP=str(poison / "sitecustomize.py"))
        summaries = []
        for optimized in (False, True):
            command = [sys.executable, "-I"] + (["-O"] if optimized else [])
            command += [str(copied), "--fixture", str(fixture)]
            completed = subprocess.run(command, cwd=poison, env=environment,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
            require(completed.returncode == 0,
                    "Isolated hostile-startup run failed: " + completed.stderr.decode("utf-8", "replace"))
            require(not marker.exists(), "Startup or local module injection executed")
            result = json.loads(completed.stdout)
            require(result["all_mandatory_checks_passed"] is True, "Subprocess checks did not pass")
            require(result["vector_sha256"] == V["EXPECTED_VECTOR_SHA256"], "Subprocess digest mismatch")
            summaries.append(completed.stdout)
            passed("hostile_startup_isolation_optimized" if optimized else "hostile_startup_isolation_normal")
        require(summaries[0] == summaries[1], "Normal and optimized verification outputs differ")
        passed("normal_and_optimized_results_identical")
        # -S prevents startup hooks in this deliberately nonisolated refusal test.
        refused = subprocess.run([sys.executable, "-S", str(HERE / "verify_certificate.py")],
                                 cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        require(refused.returncode != 0 and b"Refusing non-isolated startup" in refused.stderr,
                "Nonisolated startup was not refused")
        passed("nonisolated_startup_refused_before_optional_imports")

    require(source_hashes == {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in tracked},
            "Source or fixture changed during tests")
    passed("source_and_fixture_files_unchanged")
    print(json.dumps({
        "schema": "report144-placement-rate-test-receipt-v1",
        "optimization_level": sys.flags.optimize,
        "isolated_startup": bool(sys.flags.isolated),
        "all_tests_passed": True,
        "test_count": len(tests),
        "secure_output_checks": output_checks,
        "source_sha256": source_hashes,
        "vector_sha256": V["EXPECTED_VECTOR_SHA256"],
        "tests": tests,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Error, OSError) as exc:
        print("Tests failed: " + str(exc), file=sys.stderr)
        raise SystemExit(1)
