#!/usr/bin/env python3
"""Read-only independent residual-coverage/source/receipt audit.

No Lean compiler and no repository generator is invoked. Saved receipts are
compared to current source, object, and log bytes where those are available.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
import re
from pathlib import Path


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    location = ap.add_mutually_exclusive_group(required=True)
    location.add_argument("--work", type=Path, help="Original build workspace, including .olean objects; verify their bytes too.")
    location.add_argument("--packet", type=Path, help="Portable packet with src/evidence/integration; verify saved source and log bindings, without claiming an object replay.")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--require-complete", action="store_true")
    a = ap.parse_args()
    repo = a.repo.resolve()
    work = (a.work or a.packet).resolve()
    require_objects = a.work is not None
    baseline = repo / "Computability/BusyBeaver/Lean/BusyBeaver/ZFC"
    current = work / "src/BusyBeaver/ZFC"
    ptext = (baseline / "KSource215Program.lean").read_text()
    nodes = {}
    for match in re.finditer(r"^  \| (\d+) => (.*)$", ptext, re.M):
        parts = re.findall(r"\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?", match[2])
        assert len(parts) == 2
        nodes[int(match[1])] = tuple((kind, int(argument) if argument else None) for kind, argument in parts)
    match = re.search(r"def p215 : Program := ⟨p215Nodes, (\d+), (\d+)⟩", ptext)
    assert match
    root, nnodes = map(int, match.groups())
    assert len(nodes) == nnodes
    leaves = []
    codes = {"inc": "CI", "decnz": "CD", "brk": "CB", "cont": "CC", "halt": "CH"}
    def walk(node: int, prefix: str, fuel: int) -> None:
        assert fuel > 0
        for bit, edge in enumerate(nodes[node]):
            kind, argument = edge
            path = prefix + str(bit)
            if kind == "node":
                walk(argument, path, fuel - 1)
            else:
                leaves.append([path, codes[kind], argument])
    walk(root, "", nnodes + 1)
    literal_sites = json.loads((repo / "Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json").read_text())
    assert leaves == literal_sites
    counts = Counter(row[1] for row in leaves)
    guard_count = len(leaves) + counts["CD"]
    block_targets = []
    batch_hashes = {}
    source_groups = {"baseline_batches": 0, "residual_batches": 0}
    for i in range(9):
        name = f"KSites215Batch{i:03d}.lean"
        after = name.replace("KSites", "KResidualSites")
        old = (baseline / name).read_text()
        new = (current / after).read_text()
        pattern = r"theorem block_(\d+)\s*:\s*([\s\S]*?) := by"
        old_types = re.findall(pattern, old)
        new_types = re.findall(pattern, new)
        assert len(old_types) == len(new_types)
        for (n, old_type), (m, new_type) in zip(old_types, new_types):
            assert n == m
            assert old_type.replace("KSim.checkEdge tm215", "KResidual215.residualTest tm215") == new_type
            block_targets.append(int(n))
        assert new.count("decide +kernel") == len(new_types)
        source_groups["baseline_batches"] += len(old.encode())
        source_groups["residual_batches"] += len(new.encode())
        batch_hashes[after] = sha(new.encode())
    assert block_targets == list(range(105))
    old_facade = (baseline / "KSites215.lean").read_text()
    new_facade = (current / "KResidualSites215.lean").read_text()
    def root_proof(text: str) -> str:
        return text[text.index("theorem all_sites"):text.index("theorem covered")]
    assert root_proof(old_facade).replace("KSim.checkEdge tm215", "KResidual215.residualTest tm215") == root_proof(new_facade)
    old_files = ["KSim", "KSites215"] + [f"KSites215Batch{i:03d}" for i in range(9)]
    new_files = ["KSim", "KResidual215", "KResidualSites215"] + [f"KResidualSites215Batch{i:03d}" for i in range(9)]
    runtime_source_metrics = {}
    for label, folder, files in [("baseline", baseline, old_files), ("residual", current, new_files)]:
        data = [(folder / (name + ".lean")).read_bytes() for name in files]
        runtime_source_metrics[label] = {
            "files": files,
            "file_count": len(files),
            "bytes": sum(len(content) for content in data),
            "lines": sum(len(content.decode().splitlines()) for content in data),
        }
    runtime_source_metrics["increase_bytes"] = runtime_source_metrics["residual"]["bytes"] - runtime_source_metrics["baseline"]["bytes"]
    runtime_source_metrics["increase_lines"] = runtime_source_metrics["residual"]["lines"] - runtime_source_metrics["baseline"]["lines"]
    runtime_source_metrics["scope"] = "KSim plus site batches and facade, adding new KResidual215; excludes unchanged imported providers and explicit audit client. Not a full endpoint closure measurement."

    # Recover the complete focused closure from the reviewed source, rather
    # than trusting the implementing agent's dependency list.
    closure: dict[str, list[str]] = {}
    builtin_imports: set[str] = set()
    def visit(module: str) -> None:
        if module in closure or module in builtin_imports:
            return
        source = work / "src" / Path(module.replace(".", "/")).with_suffix(".lean")
        if not source.is_file():
            assert module == "Init" or module.startswith(("Init.", "Std.", "Lean."))
            builtin_imports.add(module)
            return
        imports = []
        for line in source.read_text().splitlines():
            if re.match(r"^import\s", line):
                imports.extend(line.split()[1:])
        closure[module] = imports
        for dependency in imports:
            visit(dependency)
    visit("BusyBeaver.ZFC.KResidualAudit")

    inherited = {}
    for module in sorted(closure):
        name = module.rsplit(".", 1)[1]
        if name.startswith("KResidual") or name == "KSim":
            continue
        old = (baseline / (name + ".lean")).read_bytes()
        new = (current / (name + ".lean")).read_bytes()
        inherited[name] = {"sha256": sha(new), "matches_maintained_source": new == old}
        assert new == old
    semantic_proposal = repo / "Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/semantic-coverage/lean/candidate/BusyBeaver/ZFC/KSim.lean"
    assert semantic_proposal.read_bytes() == (current / "KSim.lean").read_bytes()

    receipts = {}
    pending = []
    problems = []
    named_axiom_profiles = {}
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    for module in sorted(closure):
        short = module.rsplit(".", 1)[1]
        evidence = work / "evidence" / (module + ".json")
        if not evidence.is_file():
            pending.append(module)
            continue
        row = json.loads(evidence.read_text())
        source = current / (short + ".lean")
        log = work / "evidence" / (module + ".log")
        obj = work / "build/BusyBeaver/ZFC" / (short + ".olean")
        checks = {
            "returncode_zero": row["returncode"] == 0,
            "source_hash_matches": row["source_sha256"] == sha(source.read_bytes()),
            "log_hash_matches": row["log_sha256"] == sha(log.read_bytes()),
            "recorded_object_digest_present": isinstance(row.get("object_sha256"), str) and len(row["object_sha256"]) == 64,
            "object_hash_matches": obj.is_file() and row.get("object_sha256") == sha(obj.read_bytes()) if require_objects else None,
            "no_sorry_axiom_in_log": "sorryAx" not in log.read_text(),
        }
        if any(value is False for value in checks.values()):
            problems.append(module)
        module_profiles = {}
        for match in re.finditer(r"'([^']+)'\s+(?:depends on axioms:\s*\[([\s\S]*?)\]|does not depend on any axioms)", log.read_text()):
            axioms = sorted(x.strip() for x in match[2].split(",")) if match[2] else []
            assert set(axioms) <= allowed_axioms
            assert match[1] not in named_axiom_profiles or named_axiom_profiles[match[1]] == axioms
            named_axiom_profiles[match[1]] = axioms
            module_profiles[match[1]] = axioms
        receipts[module] = {"checks": checks, "source_sha256": row["source_sha256"], "compiler_seconds": row.get("compiler_seconds"), "elapsed_seconds": row.get("seconds"), "log": log.read_text()}
    expected_audit_reports = ["concrete_counts", "old_simulation_api", "residual_simulation_api", "rejects_empty"]
    audit_reports_complete = all("SetTheory.BusyBeaver.ZFC.KResidualAudit." + name in named_axiom_profiles for name in expected_audit_reports)
    if not pending and not audit_reports_complete:
        problems.append("MISSING_EXPECTED_RUNTIME_AUDIT_REPORTS")
    complete_status = "PASS_CURRENT_SOURCE_OBJECT_LOG_BINDINGS" if require_objects else "PASS_SAVED_SOURCE_LOG_BINDINGS_NO_OBJECT_REPLAY"
    status = complete_status if not pending and not problems else "PENDING_COMPILATION" if not problems else "FAIL_BINDINGS"
    integration = work / "integration"
    endpoint_old = (baseline / "KEndpoint215.lean").read_text()
    endpoint_new = (integration / "KEndpoint215.lean.proposal").read_text()
    endpoint_signatures = {}
    for name in ["blank_halts_iff_zfc_refutation", "nonhalting_iff_zfc_consistency"]:
        pattern = r"theorem " + name + r"\s*:\s*([\s\S]*?) :="
        old_sig = re.search(pattern, endpoint_old)
        new_sig = re.search(pattern, endpoint_new)
        assert old_sig and new_sig
        equal = old_sig[1].split() == new_sig[1].split()
        assert equal
        endpoint_signatures[name] = {"type_preserved": equal, "type": " ".join(new_sig[1].split())}
    endpoint_proposal = {
        "status": "SOURCE_REVIEWED_NOT_COMPILED",
        "public_endpoint_types": endpoint_signatures,
        "files": {p.name: sha(p.read_bytes()) for p in sorted(integration.glob("*.lean.proposal"))},
        "patch_sha256": sha((integration / "endpoint-UNCHECKED.patch").read_bytes()),
        "mathematical_review": "Existing dense blank equivalence, positive semantic simulation, deterministic boot transport, C222/ZF calibration, and constructible-choice refutation equivalence are composed without new premises on the concrete endpoint.",
    }
    result = {
        "status": status,
        "scope": "Read-only mathematical/source coverage check and current artifact hashes; no additional proof compilation." if require_objects else "Read-only mathematical/source coverage check and saved source/log bindings; no compiled objects inspected and no proof compilation.",
        "object_bytes_independently_checked": require_objects,
        "fresh_focused_closure_modules_including_audit_client": len(closure),
        "fresh_focused_project_modules_excluding_audit_client": len(closure) - 1,
        "fresh_focused_audit_clients": 1,
        "current_import_graph": closure,
        "builtin_import_roots": sorted(builtin_imports),
        "unchanged_baseline_providers": len(inherited),
        "semantic_coverage_module_exactly_matches_prior_proposal": True,
        "literal_program_nodes": nnodes,
        "literal_program_root": root,
        "literal_source_leaf_count": len(leaves),
        "literal_guard_count": guard_count,
        "literal_operation_counts": dict(counts),
        "decoded_nodes_exactly_match_sites215_json": True,
        "all_105_original_block_targets_preserved_except_checker": True,
        "all_original_root_joins_preserved_except_checker": True,
        "all_105_blocks_use_kernel_decide": True,
        "batch_source_bytes": source_groups,
        "runtime_source_metrics": runtime_source_metrics,
        "inherited_sources": inherited,
        "residual_batch_source_hashes": batch_hashes,
        "current_receipts": receipts,
        "named_axiom_profiles": named_axiom_profiles,
        "named_axiom_union": sorted({axiom for axioms in named_axiom_profiles.values() for axiom in axioms}),
        "expected_four_runtime_audit_reports_present": audit_reports_complete,
        "pending_modules": pending,
        "binding_failures": problems,
        "full_zfc_endpoint_rebuilt": False,
        "endpoint_integration_proposal": endpoint_proposal,
    }
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k:v for k,v in result.items() if k not in ["current_receipts", "residual_batch_source_hashes", "inherited_sources", "current_import_graph", "named_axiom_profiles"]}, indent=2))
    if problems or (a.require_complete and pending):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
