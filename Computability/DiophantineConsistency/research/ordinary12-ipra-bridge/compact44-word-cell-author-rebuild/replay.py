#!/usr/bin/env python3
"""Single-author compact word/cell extension; inherited provider ancestry."""
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
BRIDGE = HERE.parent
SEED = Path("/tmp/ipra-marked-suffix-final-build-01/lib")
PARENT = SEED.parent / "RESULT.json"
PKG = Path("/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib")
LEAN = Path("/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
TOOL = LEAN.parent.parent / "lib/lean"
SOURCES = {
    "CompactForwardCellInputs": BRIDGE / "compact44-forward-cell-inputs-exploration/CompactForwardCellInputs.lean",
    "CompactWordCellClient": BRIDGE / "compact44-word-cell-client-plan/CompactWordCellClient-DRAFT.lean",
}
SOURCE_PINS = {"CompactForwardCellInputs": "b535716229d5754bfd0ce9e16b61996746ae60186745cb741ccab7f7ce5036d4",
               "CompactWordCellClient": "7523e9d67c2e1683c1060ba561953472fbb32a6160b85083c3dfb270872579ca"}
SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ilean",
            ".olean.hash", ".olean.private.hash", ".olean.server.hash", ".ir.hash", ".ilean.hash")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
COUNTS = {"CompactForwardCellInputs": 5, "CompactWordCellClient": 6}


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
    need(digest(PARENT) == "861109aea9162f2ba0573c640a0ba4dc1658e290ea7a620cdda39f1587695068",
         "marked suffix parent receipt changed")
    need(json.loads(PARENT.read_text())["status"] == "PASS_AUTHOR_ONLY_MARKED_SUFFIX", "wrong parent status")
    need(digest(LEAN) == "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
         "Lean binary changed")
    for name, src in SOURCES.items():
        need(digest(src) == SOURCE_PINS[name], ("source drift", name))
    expected_inputs = {
        "CompactCoefficientDecoder": "f796c257b8c98949750928b1847cd0a9749a6bcaf56941f88e7d780eaa238d8d",
        "ArithmeticStandardCasts": "c992bafb003c67229c756a634d31c11ecfb942839904367554488ba27ddc597a",
        "CompactMarkedTransport": "14e5aa75e98b7c5ce7e5d568325683f360ca1eb16901ae47f005f34856f4b2ec",
    }
    fixed = {str(p): record(p) for p in [PARENT, LEAN, Path(__file__), *SOURCES.values()]}
    for name, value in expected_inputs.items():
        p = SEED / "DiophantineConsistency" / (name + ".olean")
        need(digest(p) == value, ("direct seed object drift", name))
        fixed[str(p)] = record(p)
    need(all(fixed.values()), "missing fixed input")
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
    for name, src in SOURCES.items():
        target = frozen / (name + ".lean")
        with src.open("rb") as inp, target.open("xb") as dst:
            shutil.copyfileobj(inp, dst)
        need(digest(src) == digest(target), ("source freeze failed", name))
        sources[str(target)] = record(target)
    guards = {}
    for name in SOURCES:
        for root in (lib, SEED, PKG, TOOL):
            entries = slots(root / "DiophantineConsistency" / name)
            need(all(v is None for v in entries.values()), ("target slot occupied", name, str(root)))
            merge(guards, entries)
    pre = {"status": "READY_AUTHOR_WORD_CELL_NO_LEAN", "parent": str(PARENT),
           "fixed": fixed, "sources": sources, "guards": guards,
           "scope": "Author-only incremental extension; inherited model, project/package/transitive/dynamic "
                    "ancestry and point-in-time limitations; no paired replay or graph-zero/iPRA claim."}
    save(out / "preflight.json", pre)
    print(pre["status"], flush=True)
    if args.preflight_only:
        return
    env = {"PATH": "/usr/bin:/bin", "HOME": "/home/codex",
           "LEAN_PATH": str(lib) + ":" + str(SEED) + ":" + str(PKG), "LEAN_NUM_THREADS": "1"}
    steps = []
    try:
        for name in SOURCES:
            need(shutil.disk_usage("/tmp").free >= 4 * 1024**3, "less than 4 GiB free")
            check(fixed); check(sources); check(guards)
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
            check(fixed); check(sources); check(guards)
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
            need(not any(x in text for x in ("error:", "warning:", "sorryAx")), ("bad compiler log", name))
            reports = re.findall(r"^'[^']+' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                                 text, re.M | re.S)
            need(len(reports) == COUNTS[name] and
                 all({v.strip() for v in report.split(",") if v.strip()} <= ALLOWED for report in reports),
                 ("unexpected axiom reports", name, reports))
            produced = slots(obj.with_suffix(""))
            need(produced[str(obj)] is not None and
                 all(v is None for p, v in produced.items() if p != str(obj)), ("unexpected companions", name))
            for p, v in produced.items():
                need(guards[p] is None, ("unexpected previous target", p))
                guards[p] = v
            check(fixed); check(sources); check(guards)
            steps.append({"module": name, "exit": child.returncode, "command": command,
                          "direct": direct, "output": produced, "log_sha256": digest(log)})
            save(out / (name + ".json"), steps[-1])
            print(name, "exit", child.returncode, flush=True)
        save(out / "RESULT.json", {"status": "PASS_AUTHOR_WORD_CELL", "steps": steps,
                                   "guards": guards, "scope": pre["scope"]})
        print("PASS_AUTHOR_WORD_CELL", flush=True)
    except BaseException as exc:
        save(out / "failure.json", {"error": repr(exc), "steps": steps, "scope": pre["scope"]})
        raise


if __name__ == "__main__":
    try:
        main()
    except BaseException:
        traceback.print_exc()
        raise
