#!/usr/bin/env python3
"""Replay the package's finite evidence with Python's standard library.

The frozen source census parses programs as data; it does not execute them.
Only the explicitly selected checkers and the small counterexample generator
are executed. These finite checks do not prove mathematical metatheorems.
"""
import ast
import base64
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tokenize
import zlib


ROOT = Path(__file__).resolve().parent
IGNORED_TOKENS = {
    tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT, tokenize.NEWLINE,
    tokenize.NL, tokenize.ENDMARKER, tokenize.ENCODING,
}
EXPECTED_METRICS = {
    "reference/checkers/tokens_record.py": (253, 280, 599),
    "reference/checkers/ast_record.py": (257, 275, 607),
    "reference/checkers/bytes_506.py": (267, 303, 506),
    "code/checker_505.py": (266, 301, 505),
    "code/checker_502.py": (269, 301, 502),
    "code/checker_readable.py": (605, 700, 2629),
    "illustrations/checker_packed.py": (18, 19, 459),
    "illustrations/incumbent_506_packed.py": (18, 19, 459),
    "tests/counterexample/no_initial_open.py": (250, 277, 596),
}
PROGRAMS = {
    "control_506": "reference/checkers/bytes_506.py",
    "candidate_505": "code/checker_505.py",
    "candidate_502": "code/checker_502.py",
    "readable": "code/checker_readable.py",
    "packed_candidate": "illustrations/checker_packed.py",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def write_json(relative, value):
    destination = ROOT / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


class StripDocstrings(ast.NodeTransformer):
    def visit(self, node):
        node = super().visit(node)
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
                if not node.body and not isinstance(node, ast.Module):
                    node.body.append(ast.Pass())
        return node


def measure(relative):
    raw = (ROOT / relative).read_bytes()
    tree = StripDocstrings().visit(ast.parse(raw.decode("utf-8")))
    normalized = ast.unparse(ast.fix_missing_locations(tree)) + "\n"
    parsed = ast.parse(normalized)
    triple = (
        sum(token.type not in IGNORED_TOKENS for token in
            tokenize.generate_tokens(io.StringIO(normalized).readline)),
        sum(1 for _ in ast.walk(parsed)),
        len(normalized.encode("utf-8")),
    )
    require(triple == EXPECTED_METRICS[relative],
            f"Metric mismatch for {relative}: {triple}; "
            f"expected {EXPECTED_METRICS[relative]}. "
            "Exact measurements use CPython 3.12.14.")
    return {
        "file": relative,
        "significant_tokens": triple[0],
        "ast_nodes": triple[1],
        "normalized_bytes": triple[2],
        "source_bytes": len(raw),
        "source_sha256": sha256(raw),
        "normalized_sha256": sha256(normalized.encode("utf-8")),
        "eligible_positive_checker": relative != "tests/counterexample/no_initial_open.py",
        "included_in_direct_checker_frontier": not relative.startswith("illustrations/")
            and relative != "tests/counterexample/no_initial_open.py",
        "role": ("deliberately_unsound_negative_control"
                 if relative == "tests/counterexample/no_initial_open.py"
                 else "fully_validated_public_interface"
                 if relative == "code/checker_readable.py"
                 else "packed_accounting_illustration"
                 if relative.startswith("illustrations/")
                 else "compact_protocol_checker"),
    }


def verify_packed_payloads():
    pairs = {
        "illustrations/checker_packed.py": "code/checker_502.py",
        "illustrations/incumbent_506_packed.py": "reference/checkers/bytes_506.py",
    }
    receipts = []
    for packed, expanded in pairs.items():
        tree = ast.parse((ROOT / packed).read_text(encoding="utf-8"))
        literal = tree.body[1].value.args[0].args[0].args[0].value
        require(type(literal) is str, "Packed source must contain a fixed string")
        wrapper = ast.parse("import zlib, base64\nexec(zlib.decompress(base64.b85decode("
                            + repr(literal) + ")))\n")
        require(ast.dump(tree) == ast.dump(wrapper),
                "Packed source does not have exactly the stated fixed-data loader")
        compressed = base64.b85decode(literal)
        recovered = zlib.decompress(compressed)
        original = (ROOT / expanded).read_bytes()
        require(recovered == original, "Packed payload differs from " + expanded)
        receipts.append({
            "packed_file": packed, "expanded_file": expanded,
            "packed_source_sha256": sha256((ROOT / packed).read_bytes()),
            "expanded_source_sha256": sha256(original),
            "encoded_characters": len(literal), "compressed_bytes": len(compressed),
            "expanded_bytes": len(recovered), "exact_payload_identity": True,
            "exact_stated_loader_ast": True,
        })
    return {
        "zlib_version": zlib.ZLIB_VERSION,
        "zlib_runtime_version": zlib.ZLIB_RUNTIME_VERSION,
        "files": receipts,
        "same_packed_metrics_for_incumbent_and_candidate": True,
        "packed_metrics": {"significant_tokens": 18, "ast_nodes": 19, "normalized_bytes": 459},
        "is_mathematical_axiom_reduction": False,
        "claim": "Both fixed packed files beat the previous raw numerical thresholds; the matched packed comparison is a tie.",
    }


def replay_census():
    census = ROOT / "reference/census"
    process = subprocess.run(
        [sys.executable, str(census / "reproduce_audit.py")],
        cwd=ROOT, capture_output=True, timeout=60,
    )
    require(process.returncode == 0,
            "Frozen census replay failed:\n" + process.stderr.decode("utf-8", "replace"))
    receipt = json.loads(process.stdout)
    provenance = json.loads((ROOT / "evidence/SOURCE_PROVENANCE.json").read_text())
    inventory = json.loads((census / "all_py_inventory.json").read_text())
    verified = provenance["research_tree_verification"]
    inventory_trees = {row["package"]: row["tree"] for row in inventory}
    fetched_trees = {row["package"]: row["tree"] for row in verified["packages"]}
    require(inventory_trees == fetched_trees and len(inventory_trees) == 90,
            "The frozen census package trees do not match the retrieved Research tree")
    require(not any(row["truncated"] for row in inventory),
            "A frozen package inventory was truncated")
    require(len({row["tree_sha"] for row in verified["snapshots"]}) == 1,
            "Pinned repository Research trees differ")
    for row in provenance["frozen_reference_files"]:
        raw = (ROOT / row["local_path"]).read_bytes()
        require(sha256(raw) == row["sha256"],
                "Frozen reference changed: " + row["local_path"])
    receipt.update({
        "all_90_package_trees_match": True,
        "same_research_tree_at_both_pinned_commits": True,
        "research_tree_sha": verified["verified_tree_sha"],
        "scope": "Frozen Research Python corpus; all source blobs parsed, none executed",
        "inherited_census_commit": provenance["inherited_census_commit"],
        "inspected_commit": provenance["inspected_commit"],
        "source_provenance_sha256": sha256((ROOT / "evidence/SOURCE_PROVENANCE.json").read_bytes()),
        "limitation": "The census's 256/276/506 envelope predates the separately measured incoming token/AST records.",
    })
    return receipt


def run_checker(job):
    role, relative, case, raw, expected, optimized, group = job
    command = [sys.executable]
    if optimized:
        command.append("-O")
    command.append(str(ROOT / relative))
    try:
        result = subprocess.run(command, input=raw, cwd=ROOT,
                                capture_output=True, timeout=10)
    except subprocess.TimeoutExpired:
        return {
            "case": case, "program": role, "file": relative,
            "optimized": optimized, "group": group,
            "expected": expected, "accepted": False,
            "timeout": True, "matches_expected": False,
        }
    accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
    stderr = result.stderr.decode("utf-8", "replace").splitlines()
    return {
        "case": case, "program": role, "file": relative,
        "optimized": optimized, "group": group,
        "expected": expected, "accepted": accepted,
        "exit_code": result.returncode,
        "stdout": result.stdout.decode("utf-8", "replace"),
        "last_stderr_line": stderr[-1][:240] if stderr else "",
        "matches_expected": accepted == expected,
    }


def regenerate_counterexample():
    directory = ROOT / "tests/counterexample"
    certificate = directory / "future_scope_attack.json"
    raw = certificate.read_bytes()
    require(sha256(raw) == "2a8b02b8fb6136ead81ea1e31028cb696889c76cd6e3879a49ba0e54ab661b61",
            "Counterexample certificate changed")
    require(len(json.loads(raw)) - 1 == 17, "Expected 17 counterexample proof packets")
    with tempfile.TemporaryDirectory(prefix="ipra-counterexample-") as temporary:
        copied = Path(temporary) / "make_scope_attack.py"
        shutil.copyfile(directory / "make_scope_attack.py", copied)
        process = subprocess.run([sys.executable, str(copied)],
                                 cwd=temporary, capture_output=True, timeout=10)
        require(process.returncode == 0, "Counterexample generator failed")
        require(copied.with_name("future_scope_attack.json").read_bytes() == raw,
                "Counterexample generator did not reproduce the supplied certificate")
    return raw


def validate():
    expectations = json.loads((ROOT / "tests/fixtures/expected.json").read_text())
    fixture_directory = ROOT / "tests/fixtures"
    require({file.name for file in fixture_directory.glob("*.json") if file.name != "expected.json"}
            == {row["file"] for row in expectations["fixtures"]},
            "Fixture inventory differs from fixed expectations")
    jobs = []
    for row in expectations["fixtures"]:
        raw = (fixture_directory / row["file"]).read_bytes()
        require(sha256(raw) == row["sha256"], "Fixture changed: " + row["file"])
        for optimized in (False, True):
            for role, relative in PROGRAMS.items():
                jobs.append((role, relative, row["file"], raw,
                             row["expected"]["candidate_502" if role == "packed_candidate" else role],
                             optimized, "inherited_fixture"))
    for row in expectations["readable_type_rejection_cases"]:
        certificate = json.loads((fixture_directory / row["base_fixture"]).read_text())
        if row["mutation"] == "unused_prefix":
            certificate.insert(0, row["value"])
        elif row["mutation"] == "public_goal":
            certificate[-1] = row["value"]
        else:
            raise RuntimeError("Unknown type-rejection mutation")
        raw = (json.dumps(certificate) + "\n").encode("utf-8")
        for optimized in (False, True):
            jobs.append(("readable", PROGRAMS["readable"], row["name"], raw,
                         False, optimized, "exact_json_type_rejection"))
    attack = regenerate_counterexample()
    scope_programs = {
        **PROGRAMS,
        "sound_tokens_253": "reference/checkers/tokens_record.py",
        "deliberately_unsound_250": "tests/counterexample/no_initial_open.py",
    }
    for optimized in (False, True):
        for role, relative in scope_programs.items():
            jobs.append((role, relative, "future_scope_attack.json", attack,
                         role == "deliberately_unsound_250", optimized,
                         "scope_counterexample"))
    with ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(run_checker, jobs))
    failures = [row for row in results if not row["matches_expected"]]
    by_case = {(row["case"], row["program"], row["optimized"]): row["accepted"]
               for row in results if row["group"] == "inherited_fixture"}
    differences = []
    for row in expectations["fixtures"]:
        for optimized in (False, True):
            values = {role: by_case[(row["file"], role, optimized)]
                      for role in ("control_506", "candidate_505", "candidate_502")}
            if len(set(values.values())) != 1:
                differences.append({"case": row["file"], "optimized": optimized,
                                    "acceptance": values})
            if row["canonical_contract"]:
                require(by_case[(row["file"], "readable", optimized)] == values["candidate_502"],
                        "Readable/compact mismatch within the common canonical contract")
    require({row["case"] for row in differences}
            == set(expectations["documented_compact_difference"]),
            "Unexpected compact acceptance difference")
    report = {
        "fixture_files": len(expectations["fixtures"]),
        "canonical_contract_fixtures": sum(row["canonical_contract"] for row in expectations["fixtures"]),
        "canonical_positive_fixtures": sum(row["canonical_contract"] and row["expected"]["candidate_502"]
                                           for row in expectations["fixtures"]),
        "checker_processes": len(results),
        "generator_processes": 1,
        "ordinary_and_optimized": True,
        "processes_by_group": {group: sum(row["group"] == group for row in results)
                               for group in ("inherited_fixture", "exact_json_type_rejection",
                                             "scope_counterexample")},
        "accepted_processes": sum(row["accepted"] for row in results),
        "rejected_processes": sum(not row["accepted"] for row in results),
        "expected_unsound_control_acceptances": sum(row["program"] == "deliberately_unsound_250"
                                                   and row["accepted"] for row in results),
        "mismatches": failures,
        "documented_compact_differences": differences,
        "scope_counterexample": {
            "certificate_bytes": len(attack), "certificate_sha256": sha256(attack),
            "proof_packets": 17, "generator_reproduces_exact_bytes": True,
            "goal": json.loads(attack)[-1],
            "ordinary_reading": "There exists x such that x = S(x)",
            "negative_control_is_not_a_valid_new_checker": True,
        },
        "limits": [
            "Finite tests support implementation claims; they do not prove soundness, completeness, or bi-interpretability.",
            "The compact checkers deliberately lack the readable companion's exact public syntax/type validation.",
            "The deliberately unsound 250-token program is included only as a negative control and is excluded from the positive frontier.",
        ],
        "results": results,
    }
    write_json("evidence/validation.json", report)
    require(not failures, f"Unexpected checker outcomes: {len(failures)}; see evidence/validation.json")
    return report


def main():
    run_metadata = {
        "python": sys.version,
        "python_version": sys.version.split()[0],
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "warnings": ([] if sys.version.split()[0] == "3.12.14" else
                     ["Exact published measurements were made with CPython 3.12.14."]),
    }
    measurements = [measure(relative) for relative in EXPECTED_METRICS]
    packing = verify_packed_payloads()
    write_json("evidence/packing.json", {**run_metadata, **packing})
    write_json("evidence/metrics.json", {
        **run_metadata,
        "method": "Strip genuine nested docstrings; ast.unparse plus LF; reparse; count non-layout tokens, all AST nodes, and UTF-8 bytes.",
        "files": measurements,
        "frontier_comparison_class": "Direct unpacked checkers; packed illustrations are reported separately.",
        "previous_coordinate_envelope": {"significant_tokens": 253, "ast_nodes": 275, "normalized_bytes": 506},
        "new_coordinate_envelope": {"significant_tokens": 253, "ast_nodes": 275, "normalized_bytes": 502},
        "minima_attained_by_different_programs": True,
        "one_direct_program_below_all_previous_coordinates": False,
        "packed_illustrations_below_all_previous_raw_coordinates": True,
        "candidate_improves_matched_packed_control": False,
        "absolute_minimality_claimed": False,
    })
    census = replay_census()
    write_json("evidence/census_replay.json", {**run_metadata, **census})
    validation = validate()
    validation.update(run_metadata)
    write_json("evidence/validation.json", validation)
    print(json.dumps({
        "status": "all expected finite checks passed",
        "python": run_metadata["python_version"],
        "verified_frozen_blobs": census["verified_git_blobs"],
        "verified_frozen_paths": census["verified_repository_paths"],
        "checker_processes": validation["checker_processes"],
        "counterexample_generator_reproduced": True,
        "unexpected_outcomes": len(validation["mismatches"]),
        "new_empirical_coordinate_envelope": [253, 275, 502],
        "requested_mathematical_simplification_target_achieved": False,
        "packed_illustration_metrics": [18, 19, 459],
        "matched_packed_comparison": "tie",
    }, indent=2))


if __name__ == "__main__":
    main()
