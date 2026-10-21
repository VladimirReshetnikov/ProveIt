#!/usr/bin/env python3
"""Cleanly compile and kernel-check the isolated 218/221/225/226/227/229-state extensions.

First run the pinned K230 reference build. This script verifies its source
copies, reuses those compiled dependencies, and freshly compiles every selected
extension source in an isolated directory. The default target is dense226.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

from source_data import parse, program_text

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def below(root, relative):
    path = (root / relative).resolve()
    require(path.is_relative_to(root.resolve()), f"Path escapes root: {relative}")
    return path


def reference_checks(manifest, reference, jeff, compiled):
    require(sha(reference / "manifest.json") == manifest["reference_manifest_sha256"],
            "The K230 manifest is not the pinned manifest.")
    rm = json.loads((reference / "manifest.json").read_text())
    require(rm["reference"]["commit"] == manifest["jeff_commit"], "Wrong Jeff reference commit.")
    objects = {}
    for relative, digest in rm["local_files"].items():
        require(sha(below(reference, relative)) == digest, f"K230 source changed: {relative}")
        if compiled and relative.endswith(".v"):
            copied = reference / ".build/project" / relative
            require(sha(copied) == digest, f"K230 build copy changed: {relative}")
    for relative, item in rm["reference_files"].items():
        require(sha(below(jeff, item["source"])) == item["sha256"],
                f"Jeff reference source changed: {item['source']}")
        if compiled:
            require(sha(below(reference, relative)) == item["sha256"],
                    f"Reference build copy changed: {relative}")
    if compiled:
        for relative in rm["compile_order"]:
            stem = relative if relative in rm["reference_files"] else ".build/project/" + relative
            obj = (reference / stem).with_suffix(".vo")
            require(obj.is_file(), "First complete the pinned K230 build; missing " + stem + "o")
            objects[stem[:-2] + ".vo"] = sha(obj)
    return rm, objects


def literal_rows(source):
    rows = re.findall(r"\((true|false), ([LR]), (\d+), (true|false), ([LR]), (\d+)\)",
                      source.read_text())
    out = {}
    for q, (w0, d0, n0, w1, d1, n1) in enumerate(rows):
        out[q, 0] = int(w0 == "true"), d0, int(n0)
        out[q, 1] = int(w1 == "true"), d1, int(n1)
    return out


def check_variant(v, spec, reference):
    inputs = {k: ROOT / p for k, p in spec["inputs"].items()}
    dense, sparse, old = parse(inputs["dense"]), parse(inputs["sparse"]), parse(reference / "machine/k230.tm")
    deleted = set(spec["deleted_sparse_labels"])
    require(set(dense) == {(q, b) for q in range(v) for b in (0, 1)}, "Wrong dense state census.")
    require(set(sparse) == {(q, b) for q in range(230) if q not in deleted for b in (0, 1)},
            "Wrong sparse state census.")
    require(all(w in (0, 1) and d in ("L", "R") and 0 <= n <= v for w, d, n in dense.values()),
            "Invalid dense transition.")
    require(any(line == "#! start 0" for line in inputs["dense"].read_text().splitlines()),
            "Dense machine must start at state zero.")
    if "dense_labels" in spec:
        labels = spec["dense_labels"]
        require(len(labels) == v + 1 and labels[v] == 230 and len(set(labels)) == v + 1
                and not set(labels) & deleted, "Bad explicit dense-to-sparse label list.")
        renumber = {q: i for i, q in enumerate(labels)}
    else:
        renumber = {q: i for i, q in enumerate(q for q in range(231) if q not in deleted)}
    require(dense == {(renumber[q], b): (w, d, renumber[n])
                      for (q, b), (w, d, n) in sparse.items()}, "Dense/sparse table mismatch.")
    proof = ROOT / "coq" / str(v)
    require(literal_rows(proof / f"Table{v}.v") == dense, "Dense Rocq table mismatch.")
    padded = dict(sparse)
    padded.update({(q, b): old[q, b] for q in deleted for b in (0, 1)})
    require(literal_rows(proof / "Table230.v") == padded, "Sparse Rocq table mismatch.")
    stats = None
    if v != 229:
        generated, stats = program_text(json.loads(inputs["sites"].read_text()))
        generated = f"(** Source sites SHA256 {sha(inputs['sites'])}. *)\n" + generated.replace("p227", f"p{v}")
        require(generated == (proof / f"Prog{v}.v").read_text(), "Source-tree serialization mismatch.")
        require(sha(inputs["certificate"]) == sha(proof / f"Cert{v}Offsets.v"),
                "Source-certificate serialization mismatch.")
    else:
        require(sha(inputs["sites"]) == sha(reference / "machine/sites230.json"),
                "The 229 runtime must retain the original source.")
    return {"working_states": v, "transition_rows": len(dense),
            "input_sha256": {k: sha(p) for k, p in inputs.items()}, "source_stats": stats}


def toolchain(coqc, work):
    version = subprocess.check_output([coqc, "--version"], text=True).strip()
    require(re.search(r"version 9\.1\.0(?:\s|$)", version) is not None,
            "Use Rocq 9.1.0; found " + version)
    stdlib = None
    switch, opam = os.environ.get("OPAM_SWITCH_PREFIX"), shutil.which("opam")
    executable = Path(shutil.which(coqc) or coqc).resolve()
    if switch and opam and executable.is_relative_to(Path(switch).resolve()):
        stdlib = subprocess.check_output(
            [opam, "list", "--installed", "--short", "--columns=version", "--color=never", "rocq-stdlib"],
            text=True).strip()
        require(stdlib == "9.0.0", "Use rocq-stdlib 9.0.0; found " + stdlib)
    probe = work / "ToolchainProbe.v"
    probe.write_text("From Stdlib Require Import FinFun.\nCheck FinFun.Injective.\n")
    run = subprocess.run([coqc, str(probe)], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (work / "toolchain.log").write_text(run.stdout)
    require(run.returncode == 0, "Standard-library compatibility probe failed: " + run.stdout)
    return {"compiler": version, "required_stdlib": "9.0.0", "detected_stdlib": stdlib,
            "api_probe_exit_code": run.returncode, "api_probe_log_sha256": sha(work / "toolchain.log")}


def compile_variant(v, spec, reference, rm, objects, coqc, compile_only):
    work = ROOT / ".build" / str(v)
    work.mkdir(parents=True, exist_ok=True)
    result = {"status": "RUNNING", "working_states": v, "namespace": spec["namespace"],
              "manifest_sha256": sha(ROOT / "manifest.json"), "compiled": {},
              "reference_manifest_sha256": sha(reference / "manifest.json"),
              "reference_objects_sha256": objects, "closed_reports": 0}
    started = time.perf_counter()
    result_path = work / "verification.json"
    result["toolchain"] = toolchain(coqc, work)
    flags = []
    for name, relative in rm["logical_roots"].items():
        root = relative if relative.startswith(".build/library/") else ".build/project/" + relative
        flags += ["-Q", str(reference / root), name]
    flags += ["-Q", str(work), spec["namespace"]]
    try:
        with (work / "compilation.log").open("w") as log:
            for name in spec["compile_order"]:
                source = ROOT / "coq" / str(v) / f"{name}.v"
                target = work / source.name
                shutil.copyfile(source, target)
                t = time.perf_counter()
                run = subprocess.run([coqc, *flags, "-w", "-deprecated,-notation-overridden", str(target)],
                                     text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                log.write(f"FILE {name}.v\n{run.stdout}\n")
                log.flush()
                print(f"{run.returncode}: {v}/{name}.v ({time.perf_counter() - t:.3f}s)", flush=True)
                require(run.returncode == 0, run.stdout)
                item = {"source_sha256": sha(source), "object_sha256": sha(target.with_suffix(".vo")),
                        "seconds": time.perf_counter() - t, "stdout": run.stdout}
                result["compiled"][name] = item
                require(sha(source) == sha(target), "Proof source changed while compiling.")
                if name in (f"Correct{v}", f"CorrectDense{v}"):
                    require(run.stdout.count("Closed under the global context") == spec["expected_closed_reports"]
                            and "Axioms:" not in run.stdout, "The final assumption audit failed.")
                if name == spec["target"]:
                    result["closed_reports"] = run.stdout.count("Closed under the global context")
                result_path.write_text(json.dumps(result, indent=2) + "\n")
        require(result["closed_reports"] == spec["expected_closed_reports"], "Missing final assumption audit.")
        if not compile_only:
            checker = Path(coqc).resolve().with_name("coqchk.exe" if os.name == "nt" else "coqchk")
            require(checker.is_file(), "Select a compiler with its matching coqchk executable.")
            target = spec["namespace"] + "." + spec["target"]
            print("Independent kernel recheck: " + target, flush=True)
            t = time.perf_counter()
            with (work / "coqchk.log").open("w") as log:
                run = subprocess.run([str(checker), *flags, "-silent", "-o", target],
                                     text=True, stdout=log, stderr=subprocess.STDOUT)
            result["coqchk"] = {"target": target, "exit_code": run.returncode,
                                "seconds": time.perf_counter() - t, "log_sha256": sha(work / "coqchk.log")}
            require(run.returncode == 0, "Independent kernel recheck failed.")
        result["status"] = "PASS_CLOSED_COMPILE" if compile_only else "PASS_CLOSED_KERNEL"
    except Exception as exc:
        result["status"] = "FAILED"
        result["error"] = str(exc)
        raise
    finally:
        result["seconds"] = time.perf_counter() - started
        result["compilation_log_sha256"] = sha(work / "compilation.log") if (work / "compilation.log").exists() else None
        result_path.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT.parent / "vendor/k230-rocq")
    parser.add_argument("--jeff-reference", type=Path, default=ROOT.parent / "vendor/jeff-reference")
    parser.add_argument("--states", type=int, choices=(218, 221, 225, 226, 227, 229), default=218)
    parser.add_argument("--all", action="store_true", help="Check all three closed endpoints.")
    parser.add_argument("--coqc", default=os.environ.get("COQC") or shutil.which("coqc"))
    parser.add_argument("--check-only", action="store_true", help="Check pinned bytes and literal data without Rocq.")
    parser.add_argument("--compile-only", action="store_true", help="Compile closed proofs, omitting independent coqchk.")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "manifest.json").read_text())
    for relative, digest in manifest["files"].items():
        require(sha(below(ROOT, relative)) == digest, f"Extension source changed: {relative}")
    reference, jeff = args.reference.resolve(), args.jeff_reference.resolve()
    rm, objects = reference_checks(manifest, reference, jeff, compiled=not args.check_only)
    variants = (226, 227, 229) if args.all else (args.states,)
    checks = {str(v): check_variant(v, manifest["variants"][str(v)], reference) for v in variants}
    if args.check_only:
        print(json.dumps({"status": "PASS_PINNED_BYTES_AND_LITERAL_DATA", "variants": checks}, indent=2))
        return
    require(args.coqc, "Select Rocq 9.1.0 with rocq-stdlib 9.0.0 or pass --coqc.")
    for v in variants:
        compile_variant(v, manifest["variants"][str(v)], reference, rm, objects, args.coqc, args.compile_only)


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print("Build error: " + str(error), file=sys.stderr)
        raise SystemExit(1)
