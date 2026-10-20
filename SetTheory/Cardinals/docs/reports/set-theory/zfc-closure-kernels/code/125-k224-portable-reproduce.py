#!/usr/bin/env python3
"""Offline reconstruction and mathematical-certificate replay for K224.

The default reconstructs both machines and replays the finite source, fold,
startup, and logical checks, then audits the retained final runtime cases.
--full freshly rederives all 6,238 final runtime cases. --full-baseline also
requests fresh K225 and K226 runtime replays from the pinned upstream driver;
combine both flags to freshly replay all three runtimes. No network is used,
and no mode claims a new proof-assistant kernel build.

Requires Python 3.10+ with assertions enabled. All writes are confined to the
required, initially empty output directory outside this portable packet.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import time
import zipfile


ROOT = Path(__file__).resolve().parent
UPSTREAM_ZIP = "vendor/K225_Construction_2026-10-19.zip"
UPSTREAM_SHA = "75b58ce7b5840ef3a3158341f7cf1e601aab67d19ab147d96cf37d1186cb6cbc"
UPSTREAM_FOLDER = "K225_Construction_2026-10-19"
SOURCE_OUTPUTS = (
    "candidate225.k.tm", "candidate225.tm", "sites225.json",
    "construction.json", "macro_certificates.json", "bootstrap225.json",
    "helper_before_reassociation.json", "emitter_contract.json",
)
MACHINE_OUTPUTS = (
    "candidate224.k.tm", "candidate224.tm", "candidate224.legacy.tm",
    "sites.json", "renumbering224.json", "construction224.json",
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def safe_relative(name):
    need(isinstance(name, str) and name and "\\" not in name and
         "\x00" not in name and ":" not in name, "Unsafe relative path: " + repr(name))
    path = PurePosixPath(name)
    need(not path.is_absolute() and ".." not in path.parts and
         all(part not in ("", ".", "..") for part in name.rstrip("/").split("/")),
         "Unsafe relative path: " + name)
    return Path(*path.parts)


def checked_file(base, name):
    relative = safe_relative(name)
    path = base / relative
    need(path.is_file() and not path.is_symlink(), "Missing or nonregular file: " + str(path))
    need(base.resolve() in path.resolve().parents, "File escapes root: " + name)
    for parent in path.parents:
        if parent == base:
            break
        need(not parent.is_symlink(), "Symlink in input path: " + str(parent))
    return path


def compare(left, right, label):
    need(left.read_bytes() == right.read_bytes(), "Byte comparison failed: " + label)
    return {"sha256": sha(left), "size": left.stat().st_size}


def verify_manifest():
    manifest = read_json(ROOT / "manifest.json")
    need(manifest.get("schema_version") == 1 and isinstance(manifest.get("files"), list),
         "Unsupported portable manifest schema")
    seen = set()
    total = 0
    for item in manifest["files"]:
        name = item["path"]
        need(name not in seen and name != "manifest.json", "Duplicate/self manifest entry: " + name)
        seen.add(name)
        path = checked_file(ROOT, name)
        need(type(item["size"]) is int and path.stat().st_size == item["size"],
             "Manifest size mismatch: " + name)
        need(sha(path) == item["sha256"], "Manifest SHA256 mismatch: " + name)
        total += item["size"]
    actual = set()
    for path in ROOT.rglob("*"):
        need(not path.is_symlink(), "Symlink in portable packet: " + str(path))
        if path.is_file() and path != ROOT / "manifest.json":
            actual.add(path.relative_to(ROOT).as_posix())
    need(seen == actual, "Manifest inventory mismatch; unlisted=" + repr(sorted(actual - seen)) +
         "; absent=" + repr(sorted(seen - actual)))
    return {"files_checked": len(seen), "bytes_checked": total,
            "manifest_sha256": sha(ROOT / "manifest.json")}


def extract_upstream(destination):
    archive = ROOT / UPSTREAM_ZIP
    need(sha(archive) == UPSTREAM_SHA, "Pinned K225 archive SHA256 mismatch")
    destination.mkdir()
    with zipfile.ZipFile(archive) as packet:
        members = packet.infolist()
        seen = set()
        for entry in members:
            relative = safe_relative(entry.filename)
            key = relative.as_posix()
            need(key not in seen, "Duplicate ZIP member: " + key)
            seen.add(key)
            mode = (entry.external_attr >> 16) & 0xFFFF
            kind = stat.S_IFMT(mode)
            need(kind in (0, stat.S_IFREG, stat.S_IFDIR), "Nonregular ZIP member: " + key)
            need(not entry.flag_bits & 1, "Encrypted ZIP member: " + key)
            target = destination / relative
            need(destination.resolve() in target.resolve().parents, "ZIP path escapes output: " + key)
            if entry.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with packet.open(entry) as source, target.open("xb") as output:
                    shutil.copyfileobj(source, output)
                need(target.stat().st_size == entry.file_size, "ZIP member size mismatch: " + key)
    baseline = destination / UPSTREAM_FOLDER / "portable"
    need((baseline / "reproduce.py").is_file(), "Pinned upstream portable driver missing")
    return {"archive_sha256": UPSTREAM_SHA, "members": len(members),
            "portable_root": str(baseline)}


def restore_source116(destination):
    source = ROOT / "theory/source116"
    manifest = read_json(source / "restoration_manifest.json")
    need(manifest.get("repo_commit") == "ad8cbe8249445f43408617e88a0edb668b00248d",
         "Source116 restoration commit changed")
    need(len(manifest["files"]) == 17, "Expected exactly 17 Source116 restoration pins")
    seen = set()
    for item in manifest["files"]:
        name = item["restored"]
        need(name not in seen, "Duplicate Source116 restoration entry: " + name)
        seen.add(name)
        need(sha(checked_file(source, name)) == item["sha256"],
             "Source116 restoration SHA256 mismatch: " + name)
    shutil.copytree(source, destination)
    return {"restoration_pins_checked": 17,
            "scope": "Restored Source116 proof generators are untrusted inputs to local-rule checkers; "
                     "finite numerical certificates supplement separate uniform mathematical arguments."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="Initially empty directory outside the portable packet")
    parser.add_argument("--full", action="store_true",
                        help="Freshly rederive all 6,238 final224 runtime cases")
    parser.add_argument("--full-baseline", action="store_true",
                        help="Freshly replay upstream225 and226 runtimes; combine with --full for all three")
    args = parser.parse_args()
    need(sys.version_info >= (3, 10), "Python 3.10 or newer is required")
    need(__debug__ and not sys.flags.optimize and not os.environ.get("PYTHONOPTIMIZE"),
         "Assertions must remain enabled; do not use -O/-OO or PYTHONOPTIMIZE")
    out = args.output_dir.resolve()
    need(out != ROOT and ROOT not in out.parents,
         "Choose an output directory outside the portable packet")
    if out.exists():
        need(out.is_dir() and not any(out.iterdir()),
             "Output directory must be empty; refusing stale receipts: " + str(out))
    else:
        out.mkdir(parents=True)
    (out / "logs").mkdir()
    (out / "logic").mkdir()
    start = time.monotonic()
    result = {
        "schema_version": 1, "status": "IN_PROGRESS",
        "mode": "full" if args.full else "quick",
        "upstream_runtime_mode": "fresh225_and226" if args.full_baseline else "stored_audit",
        "fresh_local_Rocq_build": False,
        "python_version": sys.version, "assertions_enabled": True,
        "output_dir": str(out), "phases": [],
        "proof_scope": {
            "source": "All-natural-register local bisimulations; exact arithmetic emitter; complete guarded CFGs.",
            "fold": "Whole-tape exact positive simulation blocks on arbitrary initial binary tapes.",
            "logic": "Independent finite Hilbert/local-rule replay and exact fresh-emitter binding; "
                     "uniform equiconsistency and private-code coupling remain mathematical arguments in the report.",
            "source116": "Some drivers call proof generators as untrusted inputs and then check all produced nodes; "
                         "this replay is not described as generator-free.",
            "runtime": "Fresh unbounded unary/list induction replay" if args.full else
                       "Integrity, coverage, and positive-duration audit of retained unbounded runtime evidence; no fresh runtime derivation.",
            "formal_status": "Executable ordinary mathematical certificates plus pinned inherited formal evidence; no new kernel check.",
        },
    }
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"

    def save():
        result["seconds"] = time.monotonic() - start
        write_json(out / "replay.json", result)

    def phase(label, action):
        print("[K224] " + label, flush=True)
        entry = {"name": label, "status": "IN_PROGRESS", "log": "logs/" + label + ".log"}
        result["phases"].append(entry)
        save()
        began = time.monotonic()
        log = out / entry["log"]
        try:
            details = action(log)
            if not log.exists():
                write_json(log, details)
            entry.update(status="PASS", seconds=time.monotonic() - began, details=details)
            save()
            return details
        except Exception as error:
            entry.update(status="FAIL", seconds=time.monotonic() - began, error=repr(error))
            if not log.exists():
                log.write_text(repr(error) + "\n", encoding="utf-8")
            save()
            raise

    def run(label, script, *arguments, cwd=None):
        command = [sys.executable, "-B", str(script), *map(str, arguments)]
        def action(log):
            with log.open("w", encoding="utf-8") as stream:
                process = subprocess.run(command, cwd=cwd or out, env=environment,
                                         stdout=stream, stderr=subprocess.STDOUT, check=False)
            need(process.returncode == 0, label + " failed; see " + str(log) + "\n" +
                 log.read_text(encoding="utf-8", errors="replace")[-3000:])
            return {"command": command, "returncode": process.returncode}
        return phase(label, action)

    try:
        result["manifest"] = phase("01_manifest", lambda log: verify_manifest())
        extraction = phase("02_extract_upstream", lambda log: extract_upstream(out / "upstream"))
        baseline = Path(extraction["portable_root"])
        baseline_flags = ["--full", "--full-baseline"] if args.full_baseline else []
        run("03_replay_upstream225", baseline / "reproduce.py", "--output-dir",
            out / "baseline225", *baseline_flags)
        result["upstream_replay"] = read_json(out / "baseline225/replay.json")
        need(result["upstream_replay"]["status"] in ("FULL_REPLAY_PASS", "QUICK_REPLAY_PASS"),
             "Upstream replay did not pass")
        run("04_construct_rel225", ROOT / "verification/construct_rel225.py",
            "--baseline-root", baseline, "--output", out / "rel225")
        run("05_check_emitter", ROOT / "verification/check_emitter.py",
            "--baseline-root", baseline, "--output", out / "rel225/emitter_contract.json")

        def source_links(log):
            fresh = {path.name for path in (out / "rel225").iterdir() if path.is_file()}
            need(fresh == set(SOURCE_OUTPUTS), "Unexpected deterministic source output inventory")
            shipped = {path.name for path in (ROOT / "parent225").iterdir() if path.is_file()}
            need(shipped - {"runtime.json", "runtime_cases.json"} == set(SOURCE_OUTPUTS),
                 "Unexpected shipped deterministic parent output inventory")
            comparisons = {"parent225/" + name: compare(out / "rel225" / name,
                           ROOT / "parent225" / name, "parent225/" + name) for name in SOURCE_OUTPUTS}
            links = (
                (out / "rel225/candidate225.k.tm", ROOT / "machine/reference/rel225.k.tm"),
                (out / "rel225/sites225.json", ROOT / "machine/reference/sites.json"),
                (baseline / "baseline226/source/legacy_state_map.json",
                 ROOT / "machine/reference/legacy_state_map.json"),
                (baseline / "baseline226/vendor/proveit/symbolic_runtime.py",
                 ROOT / "machine/vendor/symbolic_runtime.py"),
                (baseline / "baseline226/vendor/proveit/independent_runtime.py",
                 ROOT / "machine/vendor/independent_runtime.py"),
                (out / "rel225/emitter_contract.json", ROOT / "theory/emitter_contract.json"),
            )
            for left, right in links:
                label = right.relative_to(ROOT).as_posix()
                comparisons[label] = compare(left, right, label)
            return {"byte_comparisons": comparisons}
        result["source_links"] = phase("06_source_and_engine_binding", source_links)
        run("07_build224", ROOT / "machine/build224.py", "--output", out / "machine")
        run("08_independent224", ROOT / "machine/check224.py", "--results", out / "machine",
            "--output", out / "machine/independent224.json")
        result["machine_links"] = phase("09_compare_final_artifacts", lambda log: {
            name: compare(out / "machine" / name, ROOT / "machine/results" / name, name)
            for name in MACHINE_OUTPUTS})
        run("10_actual_rel_helper", ROOT / "theory/check_rel_helper_certificate.py",
            ROOT / "theory/rel_helper_certificate.json", "--output", out / "logic/rel_helper.json")
        run("11_closed_rel_fusion", ROOT / "theory/check_fusion_certificate.py",
            ROOT / "theory/rel_helper_fusion_certificate.json", "--output", out / "logic/rel_fusion.json")
        run("12_bind_fresh_emitter", ROOT / "theory/bind_rel_fusion_certificate.py",
            out / "rel225/emitter_contract.json", "--certificate",
            ROOT / "theory/rel_helper_fusion_certificate.json", "--output", out / "logic/fusion_binding.json")
        result["source116_restoration"] = phase("13_restore_source116",
            lambda log: restore_source116(out / "logic/source116"))
        source116 = out / "logic/source116"
        run("14_general_kappa", source116 / "proofs/check_general_kappa.py", cwd=source116)
        run("15_indiscernibility", source116 / "proofs/replay_indiscernibility.py", cwd=source116)
        run("16_independent_source116", source116 / "audit/check_independent.py", cwd=source116)
        if args.full:
            run("17_full_runtime224", ROOT / "machine/runtime224.py", "--results", out / "machine")
        else:
            def copy_runtime(log):
                names = ("universal224.json", "universal224_cases.json")
                for name in names:
                    shutil.copyfile(ROOT / "machine/results" / name, out / "machine" / name)
                return {"copied": list(names), "scope": "Stored runtime evidence, not freshly derived."}
            phase("17_copy_stored_runtime", copy_runtime)
            run("18_audit_stored_runtime224", ROOT / "machine/runtime224.py", "--results",
                out / "machine", "--audit-stored")
        runtime = read_json(out / "machine/universal224.json")
        helper = read_json(out / "logic/rel_helper.json")
        fusion = read_json(out / "logic/rel_fusion.json")
        binding = read_json(out / "logic/fusion_binding.json")
        need(helper["status"] == "PASS_ACTUAL_REL_HELPER" and
             fusion["status"] == "PASS_CLOSED_HILBERT_CERTIFICATE" and
             binding["status"] == "PASS_CERTIFIED_FUSION_MATCHES_EXACT_EMITTER",
             "A logical checker did not certify its expected endpoint")
        for name in ("proofs/general_kappa_results.json", "proofs/indiscernibility_replay_results.json",
                     "audit/independent_results.json"):
            need(read_json(source116 / name).get("valid") is True, "Source116 replay failed: " + name)
        need(runtime["status"] == "UNIVERSAL_MATHEMATICAL_PASS", "Incomplete runtime evidence")
        result["logic_metrics"] = {"actual_helper_roots": helper["closed_roots"],
                                   "actual_helper_proof_nodes": helper["proof_nodes"],
                                   "fusion_proof_nodes": fusion["proof_nodes"],
                                   "fresh_emitter_sha256": binding["emitter_contract_sha256"]}
        result.update(status="FULL_REPLAY_PASS" if args.full else "QUICK_REPLAY_PASS",
                      working_states=224, rows=448, source_leaves=4799, source_dag_nodes=210,
                      maximum_depth=38, maximum_zero_run=6, startup_steps=409835,
                      canonical_table_sha256=sha(out / "machine/candidate224.tm"),
                      runtime_cases=runtime["cases"], symbolic_steps=runtime["symbolic_steps"],
                      minimum_actual_steps=runtime["minimum_actual_steps"],
                      maximum_symbolic_steps=runtime["maximum_symbolic_steps"],
                      all_rows_used=runtime["all_rows_used"])
        save()
        print("[K224] " + result["status"] + ": 224 states, 448 rows, " +
              str(result["runtime_cases"]) + " runtime cases; " + str(out / "replay.json"), flush=True)
    except Exception as error:
        result.update(status="FAIL", error=repr(error))
        save()
        raise


if __name__ == "__main__":
    main()
