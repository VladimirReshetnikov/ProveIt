"""Audit the pinned ten-ZIP corpus without downloading or executing it.

Usage: python3 audit_corpus.py /path/to/the/ten/zip/files

Archive Git-blob identities and exact byte sizes are checked against
corpus_manifest.json. Every .py member is measured, duplicate byte strings
are recorded, and every occurrence receives an explicit functional role.
The role policy is a documented source audit, not an automatic proof of
soundness or of a theory's equivalence to iPRA. Only source size and source
identity are mechanically established here. No checker tests are rerun.
"""
from pathlib import Path, PurePosixPath
import argparse
import ast
import collections
import hashlib
import importlib.util
import json
import platform
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent
FIELDS = ("normalized_tokens", "ast_nodes", "normalized_bytes")
OLD_ENVELOPE = dict(zip(FIELDS, (287, 323, 738)))
NEW_ENVELOPE = dict(zip(FIELDS, (285, 322, 703)))


def load_measure():
    path = ROOT / "reference/source_measure.py"
    spec = importlib.util.spec_from_file_location("source_measure", path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def classify(relative):
    """Functional roles, after inspecting the pinned corpus's source files."""
    path = PurePosixPath(relative)
    name = path.name
    parts = path.parts
    checker_names = {
        "checker.py", "all_starts_checker.py", "choice_checker.py",
        "old_checker.py", "new_checker.py", "baseline_checker.py",
        "checker_four_schema.py", "scalar_sc_checker.py", "qe_restricted.py",
        "compact.py", "compact_new.py", "explicit_failure.py", "readable.py",
        "choice_tokens.py", "choice_structure.py",
    }
    if (name in checker_names or name.startswith("kernel") or
        ("reference" in parts and name != "source_measure.py") or
        ("comparison" in parts and name.startswith("old_")) or
        ("compact_controls" in parts and name in {"tokens.py", "structure.py", "bytes.py"})):
        return ("standalone_proof_checker",
                "Contains its own JSON input/verdict driver, syntax handling and native inference checks. "
                "Includes arithmetic candidate presentations and inherited controls; classifying the "
                "source boundary does not certify every associated mathematical claim.")
    if name in {"build.py", "package.py"}:
        return ("artifact_build_or_packaging",
                "Builds the report or distributable archive; does not implement a standalone proof checker.")
    if name == "verify_archive.py":
        return ("archive_integrity_verifier",
                "Checks payload file sizes and hashes against a manifest; checks no arithmetic or logical inference.")
    if name == "fetch_snapshot.py":
        return ("source_retrieval_support",
                "Retrieves a pinned repository snapshot; not part of any complete inference checker.")
    if name in {"source_measure.py", "measure_sources.py", "measure_complete_sources.py",
                "audit_corpus.py", "audit_frontier.py", "audit_sources.py"}:
        return ("source_measurement_or_corpus_audit",
                "Measures or inventories other source programs; does not check user proofs itself.")
    if name in {"produce.py", "producer.py", "qe_producer.py", "make_fixtures.py",
                "make_certificates.py", "compile_focused.py", "translate_uniform.py", "convert.py"}:
        return ("certificate_producer_or_translator",
                "Produces or translates proof data; an independent complete checker is still needed.")
    if name == "arithmetic.py":
        return ("standard_number_model_and_term_builders",
                "Its own documentation explicitly identifies a standard-number evaluator and term builders, "
                "not an iPRA proof checker or a universal equivalence proof.")
    if name in {"verify.py", "reproduce.py"}:
        return ("verification_or_reproduction_driver",
                "Invokes or compares separately supplied checkers/tests and may measure them; "
                "the omitted checker dependencies cannot be credited as a complete standalone kernel.")
    if (name.startswith(("test_", "validate", "check_", "verify_", "audit_", "reproduce_")) or
        name in {"focused.py", "replay.py"}):
        return ("regression_test_or_numerical_diagnostic",
                "Runs finite examples, substitutions, model computations, or checker comparisons; "
                "not a standalone checker for arbitrary iPRA proofs.")
    raise ValueError("Unclassified pinned source: " + relative)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("zip_directory", nargs="?", type=Path, default=Path("sources"))
    parser.add_argument("--manifest", type=Path, default=ROOT / "corpus_manifest.json")
    parser.add_argument("--output", type=Path, default=ROOT / "evidence/current_corpus_audit.json")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    measure = load_measure()
    receipts, occurrences, unique = [], [], {}
    extensions = collections.Counter()
    with tempfile.TemporaryDirectory(prefix="ipra-corpus-audit-") as temporary:
        scratch = Path(temporary) / "source.py"
        for entry in manifest["files"]:
            path = args.zip_directory / entry["name"]
            raw = path.read_bytes()
            git_blob = hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest()
            if len(raw) != entry["size"] or git_blob != entry["sha"]:
                raise ValueError("Pinned archive identity mismatch: " + entry["name"])
            receipt = {
                "archive": entry["name"], "repository_path": entry["path"],
                "bytes": len(raw), "expected_bytes": entry["size"],
                "git_blob_sha1": git_blob, "expected_git_blob_sha1": entry["sha"],
                "sha256": hashlib.sha256(raw).hexdigest(), "identity_verified": True,
                "python_occurrences": 0, "member_count": 0,
            }
            with zipfile.ZipFile(path) as archive:
                for info in archive.infolist():
                    if info.is_dir():
                        continue
                    receipt["member_count"] += 1
                    extensions[PurePosixPath(info.filename).suffix] += 1
                    if info.filename.endswith(".zip"):
                        raise ValueError("Unexpected nested ZIP requires an explicit audit policy")
                    if not info.filename.endswith(".py"):
                        continue
                    receipt["python_occurrences"] += 1
                    data = archive.read(info)
                    digest = hashlib.sha256(data).hexdigest()
                    relative = info.filename.split("/", 1)[-1]
                    role, reason = classify(relative)
                    if digest not in unique:
                        scratch.write_bytes(data)
                        metrics = measure.metrics(scratch)
                        parsed = ast.parse(data.decode("utf-8"))
                        imports = [ast.unparse(node) for node in ast.walk(parsed)
                                   if isinstance(node, (ast.Import, ast.ImportFrom))]
                        unique[digest] = {
                            "sha256": digest, "metrics": metrics, "imports": imports,
                            "roles": [], "occurrences": [],
                        }
                    item = unique[digest]
                    if role not in item["roles"]:
                        item["roles"].append(role)
                    reference = {"archive": entry["name"], "member": info.filename}
                    item["occurrences"].append(reference)
                    row = {**reference, "relative_member": relative, "sha256": digest,
                           "role": role, "role_reason": reason, **item["metrics"]}
                    row["strictly_below_old_envelope_coordinates"] = [
                        field for field in FIELDS if row[field] < OLD_ENVELOPE[field]]
                    row["at_or_below_old_envelope_coordinates"] = [
                        field for field in FIELDS if row[field] <= OLD_ENVELOPE[field]]
                    row["strictly_below_new_envelope_coordinates"] = [
                        field for field in FIELDS if row[field] < NEW_ENVELOPE[field]]
                    if role == "standalone_proof_checker":
                        text = data.decode("utf-8")
                        if not all(s in text for s in ("json", "ACCEPT", "REJECT")):
                            raise ValueError("Unexpected checker-interface boundary: " + str(reference))
                    occurrences.append(row)
            receipts.append(receipt)
    checker_rows = [row for row in occurrences if row["role"] == "standalone_proof_checker"]
    minimum = {field: min(row[field] for row in checker_rows) for field in FIELDS}
    if minimum != OLD_ENVELOPE:
        raise ValueError("Measured checker envelope differs from the claimed pinned envelope: " + str(minimum))
    role_counts = collections.Counter(row["role"] for row in occurrences)
    eligible = [item for item in unique.values()
                if any(field in row["at_or_below_old_envelope_coordinates"]
                       for row in occurrences if row["sha256"] == item["sha256"] for field in FIELDS)]
    contenders = [{**item, "classification_notes": [
        {"role": row["role"], "reason": row["role_reason"]}
        for row in occurrences if row["sha256"] == item["sha256"]][:1]}
        for item in eligible]
    result = {
        "repository": manifest["repository"], "commit": manifest["commit"],
        "python": platform.python_version(), "network_access_performed": False,
        "checker_programs_executed": False,
        "archive_count": len(receipts), "total_archive_bytes": sum(x["bytes"] for x in receipts),
        "all_archive_identities_verified": all(x["identity_verified"] for x in receipts),
        "total_file_members": sum(x["member_count"] for x in receipts),
        "extension_occurrence_counts": dict(sorted(extensions.items())),
        "python_occurrence_count": len(occurrences), "distinct_python_byte_strings": len(unique),
        "role_occurrence_counts": dict(sorted(role_counts.items())),
        "standalone_checker_occurrences": len(checker_rows),
        "distinct_standalone_checker_byte_strings": len({row["sha256"] for row in checker_rows}),
        "old_complete_checker_coordinate_envelope": minimum,
        "new_checkpoint_coordinate_envelope": NEW_ENVELOPE,
        "old_minimum_attainers": {
            field: [{"archive": row["archive"], "member": row["member"], "sha256": row["sha256"],
                     **{f: row[f] for f in FIELDS}} for row in checker_rows if row[field] == minimum[field]]
            for field in FIELDS},
        "all_sources_at_or_below_any_old_frontier_coordinate": contenders,
        "occurrences_strictly_below_any_new_envelope_coordinate": [
            row for row in occurrences if row["strictly_below_new_envelope_coordinates"]],
        "archive_identity_receipts": receipts, "all_python_occurrences": occurrences,
        "all_distinct_python_sources": list(unique.values()),
        "classification_policy": (
            "Every Python member is measured. Functional roles are the documented source audit encoded in "
            "classify(), not an automated semantic classifier. Every source at or below any reported old "
            "frontier coordinate is included explicitly, with its exclusion or inclusion reason. "
            "Standalone checker classification covers complete native candidates and controls; the "
            "coordinate-attaining source variants have the inherited full-iPRA equivalence arguments. "
            "No claim of certifying all metatheory in all archives, or of an implementation-independent "
            "lower bound, is made. The frontier is restricted to complete Python sources with the stated "
            "public interface, using the unchanged whole-module normalizer."),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in (
        "archive_count", "total_archive_bytes", "all_archive_identities_verified", "total_file_members",
        "python_occurrence_count", "distinct_python_byte_strings", "standalone_checker_occurrences",
        "distinct_standalone_checker_byte_strings", "role_occurrence_counts",
        "old_complete_checker_coordinate_envelope")}, indent=2))


if __name__ == "__main__":
    main()
