#!/usr/bin/env python3
"""Guarded incremental author-only QM40 native retry; not a closure audit."""
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
    raise RuntimeError("invoke python3 -I -S -B, without optimization")

D = Path(__file__).resolve().parent
DC = D.parents[1]
SRC = DC / "Lean/DiophantineConsistency"
PREVIOUS = DC / "reviews/adaptive-qm40-native-bounded-replay"
SEED = Path("/tmp/ipra-qm40-native-author-8thsscoi/lib")
PKG = Path("/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib")
LEAN = Path("/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
TOOL = LEAN.parent.parent / "lib/lean"
LITERAL = DC / "research/adaptive-qm40-proof/verify_literal.py"
CANDIDATE = DC / "research/adaptive-square-sums40-quotient-quartic/candidate.json"
MODULES = ("IPRAQM40Native", "IPRAQM40NativeChecks")
BASE_MODULES = ("AdaptiveQM40Context", "AdaptiveQM40Zeros", "AdaptiveQM40Maps",
                "AdaptiveQM40Norm", "AdaptiveQM40Model", "AdaptiveQM40Checks")
SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ilean",
            ".olean.hash", ".olean.private.hash", ".olean.server.hash", ".ir.hash", ".ilean.hash")
EXPECTED_AXIOMS = {"IPRAQM40Native": 0, "IPRAQM40NativeChecks": 3}
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
    need(p.is_file(), ("candidate is not a regular target", str(p)))
    return {"sha256": digest(p), "resolved": str(p.resolve(strict=True)),
            "link": os.readlink(p) if p.is_symlink() else None}


def slots(stem):
    return {str(stem) + s: record(str(stem) + s) for s in SUFFIXES}


def merge(guard, newer):
    for path, value in newer.items():
        need(path not in guard or guard[path] == value, ("guard drift", path))
        guard[path] = value


def check(guard):
    for path, value in guard.items():
        need(record(path) == value, ("guard changed", path))


def write_json(p, data):
    with p.open("x") as stream:
        json.dump(data, stream, sort_keys=True, indent=2)
        stream.write("\n")


def literal_check():
    result = subprocess.run([sys.executable, "-I", "-S", "-B", str(LITERAL)],
                            capture_output=True, text=True, timeout=60)
    need(result.returncode == 0 and not result.stderr and result.stdout.strip() ==
         "PASS: 40 named variables, 4 ports and all 166 Lean literal rows match the pinned DAG",
         ("literal binding check failed", result.returncode, result.stdout, result.stderr))
    return {"exit": result.returncode, "stdout_sha256": hashlib.sha256(result.stdout.encode()).hexdigest()}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--preflight-only", action="store_true")
    args = ap.parse_args()
    out = args.output
    need(out.is_absolute() and out.parent == Path("/tmp") and not os.path.lexists(out),
         "output must be a fresh direct /tmp child")
    need(shutil.disk_usage("/tmp").free >= 4 * 1024**3, "less than 4 GiB free")
    for root in (SEED, PKG, TOOL):
        need(root.is_dir() and not root.is_symlink(), ("unavailable provider", str(root)))
    old_path = PREVIOUS / "terminal-observation.json"
    need(digest(old_path) == "d394d48c153d158b9f22d41642f3363ef4edc50ea343406e4ab163caee792d97",
         "previous observation pin changed")
    old = json.loads(old_path.read_text())
    need(old["tool_session"] == 2241 and old["observed_exit_code"] == 1 and
         old["observed_completed_children"] == list(BASE_MODULES), "prior observation mismatch")
    rows = {row["module"]: row for row in old["rows"]}
    need(set(BASE_MODULES).issubset(rows), "missing previous model observations")
    need(rows["IPRAQM40Native"]["object_sha256_after_run"] is None and
         rows["IPRAQM40Native"]["snapshot_sha256_after_run"] ==
         "d261c83bf10cd406063b6622b477dac4aefe0a811f1e471ad5142e587864d40b",
         "previous native timeout observation mismatch")
    need(digest(CANDIDATE) == "fd49361551fde7c523c4494c2fbfd475f9f6c0b7660e3aef22c09228db82700d",
         "candidate pin changed")
    fixed = {str(p): record(p) for p in (LEAN, old_path, CANDIDATE, LITERAL, Path(__file__))}
    need(all(x is not None for x in fixed.values()), "missing fixed input")
    need(digest(LEAN) == "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550" and
         digest(LITERAL) == "42fcda37bfba094571d429a045f5e4c1bc9961c16817a45670530d57dc10592a",
         "Lean binary or literal verifier drift")
    for name in BASE_MODULES:
        obj = SEED / "DiophantineConsistency" / (name + ".olean")
        row = rows[name]
        need(obj.is_file() and digest(obj) == row["object_sha256_after_run"], ("prior object drift", name))
        need(digest(SRC / (name + ".lean")) == row["workspace_sha256_after_run"], ("prior source drift", name))
        need(digest(PREVIOUS / "author/src/DiophantineConsistency" / (name + ".lean")) ==
             row["snapshot_sha256_after_run"], ("snapshot drift", name))
        need(digest(PREVIOUS / "author/logs" / (name + ".log")) == row["log_sha256_after_run"],
             ("prior log drift", name))
        for p in (SRC / (name + ".lean"), PREVIOUS / "author/src/DiophantineConsistency" / (name + ".lean"),
                  PREVIOUS / "author/logs" / (name + ".log")):
            fixed[str(p)] = record(p)
    first = literal_check()
    out.mkdir(mode=0o700)
    lib = out / "lib"
    frozen = out / "src" / "DiophantineConsistency"
    logs = out / "logs"
    for p in (lib, frozen, logs):
        p.mkdir(parents=True)
    # Lean selects a module-root directory before resolving individual files:
    # an empty fresh DiophantineConsistency directory shadows SEED.  Create a
    # fresh symlink overlay of the entire seed, as in the prior bounded driver.
    # The fresh tree owns its directories; the seed itself is never modified.
    copy = subprocess.run(["/usr/bin/cp", "-as", str(SEED) + "/.", str(lib) + "/"],
                          capture_output=True, text=True, timeout=120)
    need(copy.returncode == 0 and not copy.stdout and not copy.stderr,
         ("seed overlay failed", copy.returncode, copy.stdout, copy.stderr))
    for base, dirs, _ in os.walk(lib, followlinks=False):
        for dirname in dirs:
            need(not (Path(base) / dirname).is_symlink(), ("overlay has linked directory", base, dirname))
    need((lib / "DiophantineConsistency").is_dir() and
         not (lib / "DiophantineConsistency").is_symlink(), "unsafe output parent")
    sources = {}
    for name in MODULES:
        source = SRC / (name + ".lean")
        historical = PREVIOUS / "author/src/DiophantineConsistency" / (name + ".lean")
        need(source.is_file() and historical.is_file() and digest(source) == digest(historical),
             ("source differs from prior snapshot", name))
        if name == "IPRAQM40Native":
            need(digest(source) == rows[name]["snapshot_sha256_after_run"], "prior native source drift")
        else:
            need(digest(source) == "5ac79bbbfd71b8e4ab2ac91e61da6ba3bff2be95dd139683b75c15fc9da47b05",
                 "prior native checks source drift")
        target = frozen / (name + ".lean")
        with source.open("rb") as src, target.open("xb") as dst:
            shutil.copyfileobj(src, dst)
        sources[str(source)] = record(source)
        sources[str(historical)] = record(historical)
        sources[str(target)] = record(target)
    guards = {}
    for name in MODULES:
        for root in (lib, SEED, PKG):
            guard = slots(root / "DiophantineConsistency" / name)
            need(all(v is None for v in guard.values()), ("target slot already occupied", name, str(root)))
            merge(guards, guard)
    for name in BASE_MODULES:
        merge(guards, slots(SEED / "DiophantineConsistency" / name))
    pre = {"status": "READY_INCREMENTAL_QM40_NO_LEAN", "seed": str(SEED), "package": str(PKG),
           "fixed": fixed, "sources": sources, "guards": guards, "literal_check": first,
           "scope": "Single-side incremental retry over six previously observed author objects; "
                    "point-in-time guards and inherited project/package/dynamic ancestry."}
    write_json(out / "preflight.json", pre)
    print(pre["status"], flush=True)
    if args.preflight_only:
        return
    env = {"PATH": "/usr/bin:/bin", "HOME": "/home/codex",
           "LEAN_PATH": str(lib) + ":" + str(SEED) + ":" + str(PKG), "LEAN_NUM_THREADS": "1"}
    steps = []
    try:
        for name in MODULES:
            need(shutil.disk_usage("/tmp").free >= 4 * 1024**3, "less than 4 GiB free")
            check(fixed); check(sources); check(guards)
            source = frozen / (name + ".lean")
            deps = subprocess.run([str(LEAN), "--deps", str(source)], env=env,
                                  capture_output=True, text=True, timeout=120)
            need(deps.returncode == 0 and not deps.stderr, ("dependency query failed", name, deps.stderr))
            direct = []
            for line in deps.stdout.splitlines():
                path = Path(line)
                roots = (lib, SEED, PKG, TOOL)
                need(path.is_absolute() and path.is_file() and line.endswith(".olean") and
                     any(path.is_relative_to(root) for root in roots),
                     ("unexpected dependency", name, line))
                owner = next(root for root in roots if path.is_relative_to(root))
                relative = path.relative_to(owner)
                relative_stem = Path(str(relative)[:-len(".olean")])
                module_candidates = []
                for root in roots:
                    candidates = slots(root / relative_stem)
                    merge(guards, candidates)
                    item = candidates[str(root / relative)]
                    if item is not None:
                        module_candidates.append((root / relative, item))
                need(module_candidates and module_candidates[0][0] == path and
                     all(item["sha256"] == module_candidates[0][1]["sha256"]
                         for _, item in module_candidates),
                     ("conflicting or unexpected dependency resolution", name, line, module_candidates))
                if name == "IPRAQM40NativeChecks" and path == lib / "DiophantineConsistency/IPRAQM40Native.olean":
                    need(slots(path.with_suffix("")) == built_slots, "new native object drift")
                direct.append({"path": line, "record": record(path)})
            expected = ({str(PKG / "Init.olean"), str(lib / "DiophantineConsistency/AdaptiveQM40Model.olean"),
                         str(lib / "DiophantineConsistency/IPRAQF41Native.olean")}
                        if name == "IPRAQM40Native" else
                        {str(PKG / "Init.olean"), str(lib / "DiophantineConsistency/IPRAQM40Native.olean")})
            need(set(d["path"] for d in direct) == expected, ("unexpected direct inputs", name, direct))
            check(fixed); check(sources); check(guards)
            target = lib / "DiophantineConsistency" / (name + ".olean")
            need(not any(v is not None for v in slots(target.with_suffix("")).values()),
                 ("output slot occupied", name))
            command = [str(LEAN), "-M3000", "-j1", "-DElab.async=false", "--root=" + str(out / "src"),
                       str(source), "-o", str(target)]
            log = logs / (name + ".log")
            try:
                with log.open("x") as stream:
                    run = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=600)
            except subprocess.TimeoutExpired:
                steps.append({"module": name, "timeout_seconds": 600, "log_sha256": digest(log)})
                raise
            text = log.read_text()
            need(run.returncode == 0 and target.is_file(), ("Lean failed", name, run.returncode))
            need(not any(x in text for x in ("error:", "warning:", "sorryAx")), ("bad compiler log", name))
            reports = re.findall(r"^'[^']+' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                                 text, re.M | re.S)
            need(len(reports) == EXPECTED_AXIOMS[name] and
                 all({x.strip() for x in report.split(",") if x.strip()} <= ALLOW_AXIOMS for report in reports),
                 ("unexpected axiom reports", name, reports))
            built = slots(target.with_suffix(""))
            need(built[str(target)] is not None and all(v is None for k, v in built.items() if k != str(target)),
                 ("unexpected output companions", name, built))
            # Replace only the intentionally created output's previous absence.
            for k, value in built.items():
                need(guards[k] is None, ("unexpected prior output", k))
                guards[k] = value
            if name == "IPRAQM40Native":
                built_slots = built
            check(fixed); check(sources); check(guards)
            steps.append({"module": name, "exit": run.returncode, "command": command,
                          "direct": direct, "output": built, "log_sha256": digest(log)})
            write_json(out / (name + ".json"), steps[-1])
            print(name, "exit", run.returncode, flush=True)
        need(literal_check() == first, "literal check changed")
        check(fixed); check(sources); check(guards)
        write_json(out / "RESULT.json", {"status": "PASS_AUTHOR_INCREMENTAL_QM40_NATIVE",
                   "steps": steps, "guards": guards, "scope": pre["scope"]})
        print("PASS_AUTHOR_INCREMENTAL_QM40_NATIVE", flush=True)
    except BaseException as exc:
        write_json(out / "failure.json", {"error": repr(exc), "steps": steps,
                   "scope": pre["scope"]})
        raise


if __name__ == "__main__":
    try:
        main()
    except BaseException:
        traceback.print_exc()
        raise
