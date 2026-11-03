#!/usr/bin/env python3
"""Bounded author-only standard-iPRA/QM40 extension over native provider."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import traceback

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError("invoke python3 -I -S -B without optimization")

HERE = Path(__file__).resolve().parent
DC = HERE.parents[2]
SRC = DC / "Lean/DiophantineConsistency"
CLIENT = HERE.parent / "draft/IPRAStandardQM40.lean"
BASELINE = HERE / "historical-IPRAStandardTheory.log"
BASELINE_SOURCE = "/tmp/ipra-standard-current14-author-trial/src/DiophantineConsistency/IPRAStandardTheory.lean"
SEED = Path("/tmp/ipra-qm40-incremental-author-20261102-d/lib")
PARENT = SEED.parent / "RESULT.json"
HIST = DC / "reviews/ipra-standard-current14-author-trial/state.json"
PKG = Path("/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib")
LEAN = Path("/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
TOOL = LEAN.parent.parent / "lib/lean"
MODULES = ("IPRASuccessorInduction", "IPRAAddOneGeneral", "IPRASuccessorInductionConverse",
           "IPRAStandardTheory", "IPRAStandardQM40")
SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ilean",
            ".olean.hash", ".olean.private.hash", ".olean.server.hash", ".ir.hash", ".ilean.hash")
ALLOW_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def record(p):
    p = Path(p)
    if not os.path.lexists(p):
        return None
    need(p.is_file(), ("nonfile or dangling input", str(p)))
    return {"sha256": digest(p), "resolved": str(p.resolve(strict=True)),
            "link": os.readlink(p) if p.is_symlink() else None}


def slots(stem):
    return {str(stem) + s: record(str(stem) + s) for s in SUFFIXES}


def merge(guard, other):
    for p, v in other.items():
        need(p not in guard or guard[p] == v, ("inconsistent guard", p))
        guard[p] = v


def check(guard):
    for p, v in guard.items():
        need(record(p) == v, ("guard changed", p))


def save(p, data):
    with p.open("x") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--preflight-only", action="store_true")
    args = ap.parse_args()
    out = args.output
    need(out.is_absolute() and out.parent == Path("/tmp") and not os.path.lexists(out),
         "output must be a fresh direct /tmp child")
    need(shutil.disk_usage("/tmp").free >= 4 * 1024**3, "less than 4 GiB free")
    need(digest(PARENT) == "3b2ad576262725baf0ad31e68266c9be8d8014f51d4dd905b00e24f5419e5bd0",
         "native parent receipt changed")
    need(digest(HIST) == "bd643e25b07538400b7f7cc397ff64af6ddc6d73f1e563d69fb5c6aed863da61",
         "historical state changed")
    need(digest(LEAN) == "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
         "Lean binary changed")
    prior = json.loads(PARENT.read_text())
    need(prior["status"] == "PASS_AUTHOR_INCREMENTAL_QM40_NATIVE" and
         [(x["module"], x["exit"]) for x in prior["steps"]] ==
         [("IPRAQM40Native", 0), ("IPRAQM40NativeChecks", 0)], "native parent result mismatch")
    check(prior["guards"])
    native = SEED / "DiophantineConsistency/IPRAQM40Native.olean"
    need(digest(native) == "0ebbc2c26f4f223b827705e6318f22cf65fbf32f3dcdb471776b8dc579b1d262",
         "native output drift")
    history = json.loads(HIST.read_text())
    need(history["status"] == "AUTHOR_ONLY_PASS", "historical status mismatch")
    historical_rows = {r["module"].split(".")[-1]: r for r in history["rows"]}
    paths = {name: (CLIENT if name == "IPRAStandardQM40" else SRC / (name + ".lean")) for name in MODULES}
    for name in MODULES[:-1]:
        need(name in historical_rows and digest(paths[name]) == historical_rows[name]["source_sha256"],
             ("standard source differs from historical source", name))
    need(digest(BASELINE) == historical_rows["IPRAStandardTheory"]["log_sha256"] ==
         "5d4f5799782ce2ffadea3175f6903008a8b03b5d389bbb91a6e9347573b68730",
         "historical standard-theory warning baseline mismatch")
    need(CLIENT.is_file() and
         digest(CLIENT) == "f08d26c6eee7dc79c89693da0848d58f36abac0a027e611804944ccaeb76acda",
         "client source drift")
    fixed = {str(p): record(p) for p in [PARENT, HIST, LEAN, BASELINE, Path(__file__), *paths.values()]}
    need(all(fixed.values()), "missing source or fixed input")
    out.mkdir(mode=0o700)
    lib = out / "lib"
    frozen = out / "src" / "DiophantineConsistency"
    logs = out / "logs"
    for p in (lib, frozen, logs):
        p.mkdir(parents=True)
    copy = subprocess.run(["/usr/bin/cp", "-as", str(SEED) + "/.", str(lib) + "/"],
                          capture_output=True, text=True, timeout=120)
    need(copy.returncode == 0 and not copy.stderr and not copy.stdout, ("overlay failed", copy.stderr))
    for base, dirs, _ in os.walk(lib, followlinks=False):
        for dirname in dirs:
            need(not (Path(base) / dirname).is_symlink(), ("linked overlay directory", base, dirname))
    need((lib / "DiophantineConsistency").is_dir() and
         not (lib / "DiophantineConsistency").is_symlink(), "unsafe output directory")
    sources = {}
    for name, src in paths.items():
        target = frozen / (name + ".lean")
        with src.open("rb") as inp, target.open("xb") as dst:
            shutil.copyfileobj(inp, dst)
        need(digest(src) == digest(target), ("source freeze failed", name))
        sources[str(target)] = record(target)
    guards = {}
    for name in MODULES:
        for root in (lib, SEED, PKG, TOOL):
            entries = slots(root / "DiophantineConsistency" / name)
            need(all(v is None for v in entries.values()), ("target slot occupied", name, str(root)))
            merge(guards, entries)
    pre = {"status": "READY_AUTHOR_STANDARD_QM40_NO_LEAN", "parent": str(PARENT),
           "fixed": fixed, "sources": sources, "guards": guards,
           "scope": "Author-only extension over an inherited native/model provider; no paired replay, "
                    "full transitive/package/dynamic ancestry or PDF-byte binding."}
    save(out / "preflight.json", pre)
    print(pre["status"], flush=True)
    if args.preflight_only:
        return
    env = {"PATH": "/usr/bin:/bin", "HOME": "/home/codex",
           "LEAN_PATH": str(lib) + ":" + str(SEED) + ":" + str(PKG), "LEAN_NUM_THREADS": "1"}
    steps = []
    try:
        for name in MODULES:
            need(shutil.disk_usage("/tmp").free >= 4 * 1024**3, "less than 4 GiB free")
            check(fixed); check(sources); check(guards); check(prior["guards"])
            source = frozen / (name + ".lean")
            declared = [x.strip() for x in re.findall(r"^import\s+(\S+)", source.read_text(), re.M)]
            expected = {"Init", *declared}
            deps = subprocess.run([str(LEAN), "--deps", str(source)], env=env,
                                  capture_output=True, text=True, timeout=120)
            need(deps.returncode == 0 and not deps.stderr, ("dependency query failure", name, deps.stderr))
            direct = {}
            for line in deps.stdout.splitlines():
                path = Path(line)
                roots = (lib, SEED, PKG, TOOL)
                need(path.is_absolute() and path.is_file() and line.endswith(".olean") and
                     any(path.is_relative_to(r) for r in roots), ("bad dependency", name, line))
                owner = next(r for r in roots if path.is_relative_to(r))
                rel = path.relative_to(owner)
                module = ".".join(rel.with_suffix("").parts)
                need(module in expected, ("unexpected import", name, module))
                candidates = []
                for root in roots:
                    entries = slots((root / rel).with_suffix(""))
                    merge(guards, entries)
                    value = entries[str(root / rel)]
                    if value is not None:
                        candidates.append((root / rel, value))
                need(candidates and candidates[0][0] == path and
                     all(v["sha256"] == candidates[0][1]["sha256"] for _, v in candidates),
                     ("conflicting dependency resolution", name, module))
                direct[module] = {"path": line, "record": record(path)}
            need(set(direct) == expected, ("direct import set mismatch", name, direct, list(expected)))
            check(fixed); check(sources); check(guards); check(prior["guards"])
            obj = lib / "DiophantineConsistency" / (name + ".olean")
            need(all(v is None for v in slots(obj.with_suffix("")).values()), ("output occupied", name))
            command = [str(LEAN), "-M3000", "-j1", "-DElab.async=false", "--root=" + str(out / "src"),
                       str(source), "-o", str(obj)]
            log = logs / (name + ".log")
            try:
                with log.open("x") as stream:
                    child = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=600)
            except subprocess.TimeoutExpired:
                steps.append({"module": name, "timeout_seconds": 600, "log_sha256": digest(log)})
                raise
            text = log.read_text()
            need(child.returncode == 0 and obj.is_file(), ("compiler failed", name, child.returncode))
            need(not any(x in text for x in ("error:", "sorryAx")), ("bad compiler log", name))
            if "warning:" in text:
                need(name == "IPRAStandardTheory" and
                     digest(source) == historical_rows[name]["source_sha256"] and
                     text.replace(str(source), "<SOURCE>") == BASELINE.read_text().replace(BASELINE_SOURCE, "<SOURCE>"),
                     ("unexpected or changed warning diagnostics", name))
            reports = re.findall(r"^'[^']+' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                                 text, re.M | re.S)
            need(len(reports) == (3 if name == "IPRAStandardQM40" else 0) and
                 all({v.strip() for v in report.split(",") if v.strip()} <= ALLOW_AXIOMS for report in reports),
                 ("unexpected axiom reports", name, reports))
            produced = slots(obj.with_suffix(""))
            need(produced[str(obj)] is not None and
                 all(v is None for p, v in produced.items() if p != str(obj)), ("unexpected companions", name))
            for p, v in produced.items():
                need(guards[p] is None, ("unexpected previous target", p))
                guards[p] = v
            check(fixed); check(sources); check(guards); check(prior["guards"])
            steps.append({"module": name, "exit": child.returncode, "command": command,
                          "direct": direct, "output": produced, "log_sha256": digest(log)})
            save(out / (name + ".json"), steps[-1])
            print(name, "exit", child.returncode, flush=True)
        save(out / "RESULT.json", {"status": "PASS_AUTHOR_STANDARD_QM40", "steps": steps,
                                   "guards": guards, "scope": pre["scope"]})
        print("PASS_AUTHOR_STANDARD_QM40", flush=True)
    except BaseException as exc:
        save(out / "failure.json", {"error": repr(exc), "steps": steps, "scope": pre["scope"]})
        raise


if __name__ == "__main__":
    try:
        main()
    except BaseException:
        traceback.print_exc()
        raise
