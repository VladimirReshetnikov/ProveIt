#!/usr/bin/env python3
"""Offline deterministic construction and fresh universal replay of K223.

Python 3.10+ and its standard library suffice. The default freshly reconstructs
the source and table, checks their numerical emitter independently, and derives
all 6,449 unbounded binary instruction cases. It also runs the predecessor's
quick certificate replay. --full-baseline freshly rederives the K224, K225 and
K226 runtimes too. Neither mode claims a new proof-assistant kernel build.

All output goes to the required, initially empty directory outside this packet.
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
PACKET = ROOT.parent
PREDECESSOR = "K224_Construction_2026-10-20"
PREDECESSOR_SHA = "cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887"
UPSTREAM = "K225_Construction_2026-10-19"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def relative(name):
    need(isinstance(name, str) and name and "\\" not in name
         and "\x00" not in name and ":" not in name, "Unsafe path: " + repr(name))
    p = PurePosixPath(name)
    need(not p.is_absolute() and all(x not in ("", ".", "..")
         for x in name.rstrip("/").split("/")), "Unsafe path: " + name)
    return Path(*p.parts)


def manifest_check():
    manifest = read(ROOT / "manifest.json")
    need(manifest.get("schema_version") == 1, "Unknown manifest schema")
    seen = set()
    total = 0
    for item in manifest["files"]:
        name = item["path"]
        need(name not in seen and name != "manifest.json", "Duplicate manifest entry")
        seen.add(name)
        p = ROOT / relative(name)
        need(p.is_file() and not p.is_symlink() and ROOT in p.resolve().parents,
             "Missing, nonregular or escaping manifest file: " + name)
        need(all(not x.is_symlink() for x in p.parents if x != ROOT),
             "Symlink in manifest path: " + name)
        need(p.stat().st_size == item["size"] and sha(p) == item["sha256"],
             "Manifest mismatch: " + name)
        total += item["size"]
    actual = set()
    for p in ROOT.rglob("*"):
        need(not p.is_symlink(), "Symlink in portable packet")
        if p.is_file() and p != ROOT / "manifest.json":
            actual.add(p.relative_to(ROOT).as_posix())
    need(actual == seen, "Portable manifest inventory differs")
    return {"status": "EXACT_PORTABLE_MANIFEST_PASS", "files": len(seen),
            "bytes": total, "manifest_sha256": sha(ROOT / "manifest.json")}


def extract_predecessor(destination):
    archive = ROOT / "vendor" / (PREDECESSOR + ".zip")
    need(sha(archive) == PREDECESSOR_SHA, "Predecessor ZIP pin differs")
    destination.mkdir()
    seen = set()
    with zipfile.ZipFile(archive) as packet:
        members = packet.infolist()
        for item in members:
            rel = relative(item.filename)
            need(rel.parts[0] == PREDECESSOR, "Unexpected predecessor root")
            need(rel.as_posix() not in seen, "Duplicate ZIP member")
            seen.add(rel.as_posix())
            kind = stat.S_IFMT((item.external_attr >> 16) & 0xFFFF)
            need(kind in (0, stat.S_IFREG, stat.S_IFDIR)
                 and not item.flag_bits & 1, "Nonregular/encrypted ZIP member")
            target = destination / rel
            need(destination.resolve() in target.resolve().parents, "Escaping ZIP path")
            if item.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with packet.open(item) as src, target.open("xb") as dst:
                    shutil.copyfileobj(src, dst)
                need(target.stat().st_size == item.file_size, "ZIP extraction size differs")
    return {"status": "PINNED_PREDECESSOR_EXTRACTED", "members": len(members),
            "archive_sha256": PREDECESSOR_SHA}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output-dir", type=Path, required=True)
    ap.add_argument("--full-baseline", action="store_true",
                    help="Also freshly replay the K224/K225/K226 runtimes")
    a = ap.parse_args()
    need(sys.version_info >= (3, 10), "Python 3.10+ required")
    need(__debug__ and not sys.flags.optimize and not os.environ.get("PYTHONOPTIMIZE"),
         "Assertions must be enabled; omit -O/-OO and PYTHONOPTIMIZE")
    out = a.output_dir.resolve()
    need(out != PACKET and PACKET not in out.parents, "Output must be outside the packet")
    need(not out.exists() or (out.is_dir() and not any(out.iterdir())),
         "Output directory must initially be empty")
    out.mkdir(parents=True, exist_ok=True)
    (out / "logs").mkdir()
    begun = time.monotonic()
    result = {"schema_version": 1, "status": "IN_PROGRESS", "phases": [],
              "python": sys.version, "assertions_enabled": True,
              "fresh_k223_runtime": True,
              "fresh_predecessor_runtimes": bool(a.full_baseline),
              "fresh_Rocq_or_Lean_build": False,
              "proof_scope": {
                  "construction": "Exact deterministic source grammar, macro contracts, numerical emitter, decoder relation and table bytes.",
                  "independent_emitter": "All-register source bisimulation and uniform constructor decoding side conditions.",
                  "runtime": "Fresh induction for all nine natural registers, arbitrary natural gap/first spare and arbitrary finite remaining spare list.",
                  "theory": "Ordinary mathematical proof in report/main.tex and theory223.tex; no new kernel endpoint."}}
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"

    def save():
        result["seconds"] = time.monotonic() - begun
        write(out / "replay.json", result)

    def phase(name, action):
        print("[K223] " + name, flush=True)
        entry = {"name": name, "status": "IN_PROGRESS"}
        result["phases"].append(entry)
        save()
        start = time.monotonic()
        try:
            entry["result"] = action()
            entry["status"] = "PASS"
        except Exception as error:
            entry.update(status="FAILED", error=repr(error))
            result["status"] = "FAILED"
            raise
        finally:
            entry["seconds"] = time.monotonic() - start
            save()

    def run(name, command, receipt, expected):
        log = out / "logs" / (name + ".log")
        with log.open("w", encoding="utf-8") as stream:
            finished = subprocess.run(command, env=env, stdout=stream,
                                      stderr=subprocess.STDOUT, cwd=out)
        need(finished.returncode == 0, "Command failed; see " + str(log))
        data = read(receipt)
        need(data.get("status") == expected, "Unexpected receipt; see " + str(receipt))
        return {"status": expected, "log": log.relative_to(out).as_posix(),
                "receipt": receipt.relative_to(out).as_posix(),
                "receipt_sha256": sha(receipt)}

    try:
        phase("portable_manifest", manifest_check)
        phase("extract_pinned_K224", lambda: extract_predecessor(out / "predecessor"))
        base = out / "predecessor" / PREDECESSOR
        old_replay = out / "predecessor_replay"
        command = [sys.executable, "-B", str(base / "portable/reproduce.py"),
                   "--output-dir", str(old_replay)]
        if a.full_baseline:
            command += ["--full", "--full-baseline"]
        phase("predecessor_certificates", lambda: run(
            "predecessor", command, old_replay / "replay.json",
            "FULL_REPLAY_PASS" if a.full_baseline else "QUICK_REPLAY_PASS"))
        rebuilt = out / "rebuilt223"
        phase("deterministic_223_construction", lambda: run(
            "construction", [sys.executable, "-B", str(ROOT / "verification/build223.py"),
              "--baseline-root", str(base), "--grammar", str(ROOT / "machine/grammar223.json"),
              "--output", str(rebuilt)], rebuilt / "reconstruction.json",
            "DETERMINISTIC_223_RECONSTRUCTION_PASS"))

        def compare_published():
            records = {}
            for name in ("candidate223.tm", "candidate.k.tm", "candidate.legacy.tm",
                         "sites.json", "canonical_map.json"):
                published = ROOT / "machine" / name
                need(published.read_bytes() == (rebuilt / name).read_bytes(),
                     "Published/rebuilt bytes differ: " + name)
                records[name] = {"sha256": sha(published), "size": published.stat().st_size}
            return records

        phase("published_bytes", compare_published)
        upstream = old_replay / "upstream" / UPSTREAM / "portable"
        phase("independent_emitter_and_decoding", lambda: run(
            "emitter", [sys.executable, "-B", str(ROOT / "verification/audit_ks223_emitter.py"),
              "--baseline224-portable", str(base / "portable"),
              "--upstream225-portable", str(upstream),
              "--source", str(rebuilt / "sites.json"),
              "--grammar", str(ROOT / "machine/grammar223.json"),
              "--output", str(out / "emitter223.json")], out / "emitter223.json",
            "INDEPENDENT_KS223_EMITTER_AND_NATIVE_DECODING_PASS"))
        runtime = out / "runtime223"
        phase("fresh_unbounded_runtime_6449_cases", lambda: run(
            "runtime223", [sys.executable, "-B", str(ROOT / "verification/check223.py"),
              "--baseline-machine-dir", str(base / "portable/machine"),
              "--table", str(rebuilt / "candidate.k.tm"),
              "--sites", str(rebuilt / "sites.json"),
              "--canonical-table", str(rebuilt / "candidate223.tm"),
              "--canonical-map", str(rebuilt / "canonical_map.json"),
              "--output", str(runtime)], runtime / "audit.json", "UNIVERSAL_RUNTIME_PASS"))

        def case_check():
            recorded = ROOT / "certificates/runtime223_cases.json"
            need(recorded.read_bytes() == (runtime / "cases.json").read_bytes(),
                 "Fresh guarded-case summaries differ from the frozen first replay")
            return {"status": "ALL_6449_FRESH_CASE_SUMMARIES_IDENTICAL", "sha256": sha(recorded)}

        phase("fresh_case_summary_identity", case_check)
        phase("final_input_integrity", manifest_check)
        result["status"] = "FULL_K223_REPLAY_PASS"
        save()
        print(result["status"], flush=True)
        return 0
    except Exception as error:
        result.update(status="FAILED", error=repr(error))
        save()
        print("FAILED: " + repr(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
