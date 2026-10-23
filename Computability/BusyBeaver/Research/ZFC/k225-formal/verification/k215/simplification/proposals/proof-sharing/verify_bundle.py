#!/usr/bin/env python3
"""Offline integrity checks for saved component evidence, not proof replay.

Uses only the Python standard library and paths relative to this file.  No
compiler, network connection, original checkout, or retained proof object is
used.  Receipt commands and object hashes describe the recorded runs; checking
them here does not re-execute those runs or establish the full ZFC endpoint.
"""

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


ROOT = Path(__file__).resolve().parent
PIN = "cbf94cb552a3b49509e0eee80e7455d4eb5974c6"
LEAN_COMMIT = "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
ALLOWED_LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def local(base, name):
    require(isinstance(name, str) and name and "\\" not in name,
            "Invalid relative path: {!r}".format(name))
    parts = PurePosixPath(name)
    require(not parts.is_absolute() and ".." not in parts.parts,
            "Path escapes packet: " + name)
    return base.joinpath(*parts.parts)


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def valid_hash(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value)


def bind(path, expected, size=None):
    require(valid_hash(expected), "Invalid SHA256 for " + str(path))
    require(path.is_file(), "Missing file: " + str(path))
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == expected,
            "SHA256 mismatch: " + str(path.relative_to(ROOT)))
    if size is not None:
        require(len(data) == size, "Byte count mismatch: " + str(path))


def inventory(base):
    return {p.relative_to(base).as_posix()
            for p in base.rglob("*") if p.is_file()}


def check_manifest(base):
    manifest = read_json(base / "MANIFEST.json")
    require(isinstance(manifest, dict), "Manifest must be a path mapping")
    expected = set(manifest)
    observed = inventory(base) - {"MANIFEST.json"}
    require(expected == observed,
            "Manifest membership mismatch in {}: missing={}, extra={}".format(
                base.name, sorted(expected - observed), sorted(observed - expected)))
    for name, entry in manifest.items():
        if isinstance(entry, str):
            bind(local(base, name), entry)
        else:
            bind(local(base, name), entry["sha256"], entry["bytes"])
    return len(manifest)


def check_lean_log(path):
    text = path.read_text(encoding="utf-8")
    require("sorryAx" not in text and "native_decide" not in text
            and "error:" not in text and "uses 'sorry'" not in text,
            "Rejected content in accepted Lean log: " + str(path))
    for profile in re.findall(r"depends on axioms: \[([^\]]*)\]", text):
        axioms = {a.strip() for a in profile.split(",") if a.strip()}
        require(axioms <= ALLOWED_LEAN_AXIOMS,
                "Unexpected axiom profile in " + str(path))


def check_expected_profiles(base, profiles):
    for item in profiles:
        text = local(base, item["log"]).read_text(encoding="utf-8")
        expected = "'{}' depends on axioms: [{}]".format(
            item["theorem"], ", ".join(item["axioms"]))
        require(expected in text, "Missing assumption report: " + item["theorem"])


def check_runtime(meta):
    base = ROOT / "lean-runtime"
    manifest_count = check_manifest(base)
    vendor = read_json(base / "vendor_manifest.json")
    require(vendor["commit"] == PIN and len(vendor["files"]) == 11,
            "Runtime vendor scope/pin mismatch")
    for row in vendor["files"]:
        bind(local(base, row["path"]), row["sha256"])
    objects, sources = {}, {}
    for phase, count, target in [
        ("runtime", 12, "BusyBeaver.ZFC.KLeftFrame215"),
        ("paths", 2, "BusyBeaver.ZFC.KLeftFramePaths215"),
    ]:
        receipt = read_json(base / "evidence" / phase / "receipt.json")
        require(receipt["status"] == "PASS" and len(receipt["records"]) == count,
                "Runtime receipt status/count mismatch: " + phase)
        require(receipt["target"] == target
                and receipt["full_zfc_endpoint_rebuilt"] is False,
                "Runtime receipt scope mismatch")
        require("4.32.0" in receipt["toolchain"]
                and LEAN_COMMIT in receipt["toolchain"], "Runtime compiler mismatch")
        for row in receipt["records"]:
            module, source = row["module"], row["source"]
            require(module not in objects and row["returncode"] == 0,
                    "Duplicate or rejected runtime compilation: " + module)
            relative = module.replace(".", "/") + ".lean"
            require(source["rel"] == relative, "Runtime source/module mismatch")
            candidates = [local(base, relative), local(base / "vendor", relative)]
            matches = [p for p in candidates if p.is_file()]
            require(len(matches) == 1, "Ambiguous runtime source: " + module)
            bind(matches[0], source["sha256"])
            sources[relative] = source["sha256"]
            require(row["command"][-1] == relative and "-o" in row["command"],
                    "Runtime command/source mismatch")
            log = base / "evidence" / phase / "logs" / (module + ".log")
            bind(log, row["log_sha256"])
            check_lean_log(log)
            require(set(row["import_objects"]) == set(source["project_imports"]),
                    "Runtime imported-object key mismatch: " + module)
            for dependency, digest in row["import_objects"].items():
                require(objects.get(dependency) == digest,
                        "Runtime imported-object receipt mismatch: " + dependency)
            require(valid_hash(row["object_sha256"]), "Invalid recorded object hash")
            objects[module] = row["object_sha256"]
    require(len(objects) == 14, "Expected fourteen distinct runtime/path modules")
    summary = read_json(base / "evidence/validation_summary.json")
    require(summary["repository_pin"] == PIN
            and summary["status"] == "PASS_COMPONENTS"
            and summary["fresh_unique_modules"] == 14
            and summary["full_zfc_endpoint_rebuilt"] is False,
            "Runtime validation-summary mismatch")
    for name, digest in summary["source_sha256"].items():
        require(sources.get(name) == digest, "Runtime summary/source mismatch")
    bind(base / "evidence/executed_build.py", summary["executed_driver_sha256"])
    finite = read_json(base / "assignment_audit.json")
    for key in ("status", "source_leaves", "template_uses"):
        require(finite[key] == meta["finite_audit"][key],
                "Runtime finite-audit summary mismatch: " + key)
    require(summary["local_templates_checked"] == 35
            and summary["local_symbolic_operations"] == 444
            and summary["universal_source_actions_checked"] == 35,
            "Runtime template scope mismatch")
    check_expected_profiles(base, meta["assumption_reports"])
    print("PASS lean-runtime: 12 runtime + 2 path-action source/log bindings; "
          "imported-object receipt chain; {} manifest entries".format(manifest_count))


def check_scheduler(meta):
    base = ROOT / "lean-scheduler"
    source_manifest = read_json(base / "sources.json")
    require(source_manifest["commit"] == PIN
            and len(source_manifest["modules"]) == 17, "Scheduler source scope mismatch")
    source_hashes = {}
    for row in source_manifest["modules"]:
        require(row["path"] not in source_hashes, "Duplicate scheduler source")
        bind(local(base / "sources", row["path"]), row["sha256"], row["bytes"])
        source_hashes[row["path"]] = row["sha256"]
    generic = read_json(base / "evidence/generic_verification.json")
    require(generic["source_commit"] == PIN
            and generic["compiler"]["commit"] == LEAN_COMMIT
            and len(generic["invocations"]) == 2, "Generic scheduler scope mismatch")
    require({r["stdout_stderr"] for r in generic["invocations"]}
            == {"CofinalScheduler.log", "BoundedScheduler.log"},
            "Generic scheduler invocation coverage mismatch")
    for invocation in generic["invocations"]:
        require(invocation["exit_code"] == 0, "Rejected generic scheduler invocation")
        source_name = invocation["stdout_stderr"][:-4] + ".lean"
        require(invocation["command"].endswith(" " + source_name),
                "Generic scheduler command/source mismatch")
        check_lean_log(local(base / "evidence", invocation["stdout_stderr"]))
    for name, row in generic["files"].items():
        if name.endswith(".olean"):
            require(valid_hash(row["sha256"]) and row["bytes"] > 0,
                    "Invalid historical generic object metadata")
        else:
            folder = "sources" if name.endswith(".lean") else "evidence"
            bind(local(base / folder, name), row["sha256"], row["bytes"])
    concrete = read_json(base / "evidence/concrete_final_verification.json")
    require(concrete["commit"] == PIN and concrete["status"] == "PASS_COMPONENT"
            and len(concrete["records"]) == 15, "Concrete scheduler scope mismatch")
    require("4.32.0" in concrete["version"] and LEAN_COMMIT in concrete["version"],
            "Concrete scheduler compiler mismatch")
    require(concrete["history"]["failed_output_excluded"] is True,
            "Scheduler failed attempt was not excluded")
    for name, digest in concrete["kernel_inputs"].items():
        require(source_hashes.get(name + ".lean") == digest,
                "Scheduler generic/concrete source binding mismatch")
    require(set(concrete["kernel_inputs"]) == {"CofinalScheduler", "BoundedScheduler"},
            "Unexpected scheduler generic inputs")
    observed = set()
    for row in concrete["records"]:
        relative = row["module"].replace(".", "/") + ".lean"
        require(relative not in observed and row["exit_code"] == 0,
                "Duplicate or rejected concrete scheduler compilation")
        observed.add(relative)
        require(source_hashes.get(relative) == row["source_sha256"],
                "Scheduler receipt/source manifest mismatch: " + relative)
        require(row["command"][-1] == relative and "-o" in row["command"],
                "Scheduler command/source mismatch")
        log = local(base / "evidence", row["stdout_stderr"])
        bind(log, row["log_sha256"])
        check_lean_log(log)
        require(valid_hash(row["object_sha256"]), "Invalid recorded scheduler object hash")
    require(observed == set(source_hashes) - {"CofinalScheduler.lean", "BoundedScheduler.lean"},
            "Scheduler concrete compilation coverage mismatch")
    bind(base / "evidence/check_concrete.executed.py", concrete["executed_driver_sha256"])
    check_expected_profiles(base, meta["assumption_reports"])
    print("PASS lean-scheduler: 2 generic + 15 concrete source/log bindings; "
          "17 source-manifest entries; failed attempt excluded")


def check_rocq(meta):
    base = ROOT / "rocq-locality"
    manifest_count = check_manifest(base)
    receipt = read_json(base / "evidence/final/receipt.json")
    require(receipt["expected_repository_pin"] == PIN
            and receipt["status"] == "PASS_COMPONENT"
            and len(receipt["inputs"]) == 10 and len(receipt["checks"]) == 11,
            "Rocq scope/status mismatch")
    require("version 8.18.0" in receipt["toolchain"]
            and "OCaml 4.14.1" in receipt["toolchain"], "Rocq toolchain mismatch")
    inputs = set()
    for row in receipt["inputs"]:
        relative = row["build_path"]
        require(relative not in inputs, "Duplicate Rocq source input")
        inputs.add(relative)
        path = (local(base / "deps", relative) if "repo_path" in row
                else local(base, row["local_path"]))
        bind(path, row["sha256"], row["bytes"])
    compiled = set()
    for row in receipt["checks"]:
        require(row["exit_code"] == 0, "Rejected Rocq process receipt")
        bind(local(base / "evidence/final", row["log"]), row["log_sha256"])
        if "source" in row:
            require(row["source"] not in compiled
                    and row["command"][0] == "coqc"
                    and row["command"][-1] == row["source"],
                    "Rocq compilation/source mismatch")
            compiled.add(row["source"])
    require(compiled == inputs, "Rocq compiled-source coverage mismatch")
    audit = receipt["checks"][-1]
    command = audit["command"]
    require("source" not in audit and command[0] == "coqchk"
            and command[-1] == "Runtime215Locality"
            and not any(a in command for a in ("-admit", "-norec")),
            "Unexpected recursive coqchk target/options")
    require(set(receipt["objects"]) == {n[:-2] + ".vo" for n in inputs},
            "Rocq historical object coverage mismatch")
    require(all(valid_hash(h) for h in receipt["objects"].values()),
            "Invalid historical Rocq object hash")
    for item in meta["assumption_reports"]:
        source = local(base, item["source"]).read_text(encoding="utf-8")
        text = local(base, item["log"]).read_text(encoding="utf-8")
        require(text.count("Closed under the global context") == len(item["theorems"])
                and "Axioms:" not in text, "Unexpected Rocq new-theorem assumption report")
        for theorem in item["theorems"]:
            require("Print Assumptions " + theorem + "." in source,
                    "Missing Rocq assumption-report command: " + theorem)
    print("PASS rocq-locality: 10 source/log bindings + recursive coqchk receipt; "
          "5 closed new-theorem reports; {} manifest entries".format(manifest_count))


def main():
    for path in ROOT.rglob("*"):
        require(not path.is_symlink(), "Symlink is outside the portable packet policy: " + str(path))
        require(not path.name.endswith((".olean", ".olean.private", ".olean.server",
                    ".ilean", ".vo", ".vos", ".vok", ".glob", ".pyc", ".o", ".so")),
                "Compiled proof/build artifact is bundled: " + str(path.relative_to(ROOT)))
        if any(component in path.relative_to(ROOT).parts for component in
               ("lean-runtime", "lean-scheduler", "rocq-locality")):
            require(path.suffix != ".aux" and path.name != ".coq-native",
                    "Proof build artifact is bundled: " + str(path.relative_to(ROOT)))
    verification = read_json(ROOT / "VERIFICATION.json")
    require(verification["status"] == "PASS_SAVED_EVIDENCE"
            and verification["repository"]["commit"] == PIN
            and verification["full_zfc_endpoint_rebuilt"] is False
            and verification["fresh_compilation_performed_by_this_verifier"] is False
            and verification["accepted_compiler_records"] == 41
            and verification["accepted_additional_recursive_kernel_check_records"] == 1,
            "Top-level verification scope mismatch")
    for name, digest in verification["receipt_bindings"].items():
        bind(local(ROOT, name), digest)
    require(len(verification["receipt_bindings"]) == 5, "Expected five accepted receipts")
    components = verification["components"]
    check_runtime(components["lean-runtime"])
    check_scheduler(components["lean-scheduler"])
    check_rocq(components["rocq-locality"])
    if (ROOT / "MANIFEST.json").is_file():
        print("PASS top-level MANIFEST.json: {} files".format(check_manifest(ROOT)))
    else:
        print("NOT PRESENT: top-level MANIFEST.json; final whole-bundle manifest check skipped")
    print("PASS saved-evidence integrity: 41 accepted compiler records and 1 recursive "
          "coqchk record, with no compiled proof objects bundled")
    print("No proof assistant was run by this verifier. Historical object hashes are "
          "receipt metadata; omitted objects cannot be rehashed here. No full ZFC "
          "endpoint rebuild or completed production integration is claimed.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        raise SystemExit(1)
