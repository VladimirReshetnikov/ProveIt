#!/usr/bin/env python3
"""Verify delivery integrity and accepted source/log bindings; does not run a kernel."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: str) -> dict:
    return json.loads((ROOT / path).read_text())


def main() -> None:
    require(__debug__, "Run without -O; the finite census uses assertions.")
    manifest = load("MANIFEST.json")
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        require(not relative.is_absolute() and ".." not in relative.parts, "Unsafe manifest path")
        path = ROOT / relative
        require(path.is_file(), f"Missing artifact: {relative}")
        require(path.stat().st_size == entry["bytes"], f"Size mismatch: {relative}")
        require(digest(path) == entry["sha256"], f"Hash mismatch: {relative}")

    lean = load("lean/evidence/receipt.json")
    require(lean["all_passed"] and lean["fresh_compilation"], "Lean check did not pass freshly")
    require(not lean["full_K215_endpoint_rebuilt"], "Unexpected full-endpoint claim")
    require(len(lean["modules"]) == 29, "Unexpected Lean closure size")
    for module in lean["modules"]:
        require(module["exit_code"] == 0 and not module["unexpected_axioms"],
                f"Unaccepted Lean result: {module['module']}")
        require(digest(ROOT / "lean" / module["source"]) == module["source_sha256"],
                f"Lean receipt/source mismatch: {module['module']}")
        require(digest(ROOT / "lean/evidence" / module["log"]) == module["log_sha256"],
                f"Lean receipt/log mismatch: {module['module']}")
    for source in load("lean/source-pins.json")["sources"]:
        require(digest(ROOT / "lean" / source["path"]) == source["sha256"],
                f"Lean source pin mismatch: {source['path']}")

    rocq = load("rocq/evidence/verification.json")
    require(rocq["status"] == "PASS_CLOSED_ISOLATED_KERNEL", "Rocq component did not pass")
    require(not rocq["full_machine_endpoint_rebuilt"], "Unexpected full-endpoint claim")
    for flag in ["current_lean_core_reproduced_byte_for_byte", "legacy_nat_renderings_unchanged",
                 "compiled_client_byte_identical_to_baseline"]:
        require(rocq[flag], f"Generator/client check failed: {flag}")
    for module, expected in rocq["source_sha256"].items():
        if module == "Baseline/DomRho8.v":
            path = ROOT / "rocq/reference/original_DomRho8.v"
        elif module in {"K215F/DominatedImplication.v", "K215F/DomRho8.v"}:
            path = ROOT / "rocq/coq" / Path(module).name
        else:
            path = ROOT / "rocq/reference" / module
        require(digest(path) == expected, f"Rocq receipt/source mismatch: {module}")
    for command in rocq["commands"]:
        require(command["exit_code"] == 0, f"Rocq command failed: {command['label']}")
        require(digest(ROOT / "rocq/evidence" / command["log"]) == command["log_sha256"],
                f"Rocq receipt/log mismatch: {command['label']}")
    by_label = {item["label"]: item for item in rocq["commands"]}
    for label, count in [("K215F-DominatedImplication", 3), ("K215F-DomRho8", 4),
                         ("K215F-ThmDom", 1)]:
        require(by_label[label]["closed_reports"] >= count, f"Missing closed reports: {label}")
    kernel_log = (ROOT / "rocq/evidence/coqchk-new-client.log").read_text()
    for line in ["Axioms: <none>", "Constants/Inductives relying on type-in-type: <none>",
                 "Constants/Inductives relying on unsafe (co)fixpoints: <none>",
                 "Inductives whose positivity is assumed: <none>"]:
        require(line in kernel_log, f"Missing recursive kernel context check: {line}")
    baseline_bytes = (ROOT / "baseline/DomRho8.v").stat().st_size
    proposal_bytes = sum((ROOT / "rocq/coq" / name).stat().st_size
                         for name in ["DominatedImplication.v", "DomRho8.v"])
    require((baseline_bytes, proposal_bytes) == (22673, 15638), "Source-size comparison changed")

    audit = load("evidence/ksim_contract_audit.json")
    require(digest(ROOT / "baseline/KSim.lean") == audit["baseline_sha256"], "KSim baseline mismatch")
    require(digest(ROOT / "lean/src/BusyBeaver/ZFC/KSim.lean") == audit["candidate_sha256"],
            "KSim reviewed candidate mismatch")
    require(len(audit["definitions"]) == 15 and all(x["same_body_and_type"] for x in audit["definitions"]),
            "Executable-definition audit failed")
    require(len(audit["theorem_explicit_statements"]) == 22 and
            all(x["same_explicit_statement"] for x in audit["theorem_explicit_statements"]),
            "Explicit theorem-statement audit failed")

    from audit_snapshot import audit as source_audit
    require(source_audit() == load("evidence/census.json"), "Finite source census mismatch")
    result = subprocess.run([sys.executable, str(ROOT / "evidence/decoder_prefix_census.py")],
                            text=True, capture_output=True, check=True)
    require(json.loads(result.stdout) == load("evidence/decoder_prefix_census.json"),
            "Decoder prefix witness census mismatch")
    summary = {
        "status": "PASS_DELIVERY_INTEGRITY_AND_RECEIPT_BINDINGS",
        "files_checked": len(manifest["files"]),
        "lean_modules_in_accepted_fresh_receipt": 29,
        "rocq_accepted_receipt": rocq["status"],
        "rocq_proof_bytes_before": baseline_bytes,
        "rocq_proof_bytes_after": proposal_bytes,
        "checked_literal_suffix_branches": 2,
        "total_source_branches": 6176,
        "full_endpoint_rebuilt": False,
        "kernel_invoked_by_this_script": False,
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
