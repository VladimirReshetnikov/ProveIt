#!/usr/bin/env python3
"""Independent frozen-package audit and paired singleton-DAG measurements.

Each package runs in its own persistent Python process, imported as fastunknot.
This isolates even the maintained modules that use absolute package imports.
The workers time complete fresh-PD group_decide/recognize calls internally;
package loading, IPC, source freezing and record serialization are excluded.
All certificates, incomplete outcomes, sample orders and A/A controls are kept.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib
import json
import os
from pathlib import Path
import platform
import random
import shutil
from statistics import median
import subprocess
import sys
import time

BASELINE_COMMIT = "483b7397a1086206bc463222094315390c42550d"
SEED = 261009817


def plain_encode(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def file_hashes(root):
    root = Path(root)
    return {
        str(p.relative_to(root)): sha256(p.read_bytes()).hexdigest()
        for p in sorted(root.rglob("*.py"))
    }


def freeze_package(fast_root, target):
    """Copy the full Python package, refusing pre-existing different snapshots."""
    source = Path(fast_root) / "fastunknot"
    expected = file_hashes(source)
    assert "__init__.py" in expected, source
    target = Path(target) / "fastunknot"
    if target.exists():
        assert file_hashes(target) == expected, ("snapshot already differs", target)
    else:
        for relative in expected:
            destination = target / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / relative, destination)
    assert expected == file_hashes(source), "source changed while being frozen"
    assert expected == file_hashes(target), "snapshot hash mismatch"
    return expected


def group_records(evidence):
    """Copied structurally, not imported from either package's research code."""
    result = []
    for key, value in evidence.items():
        if key == "group":
            result.append(value)
        elif isinstance(value, dict):
            result.extend(group_records(value))
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict):
                    result.extend(group_records(item))
    return result


def worker_main(package_root):
    sys.path.insert(0, str(Path(package_root).resolve()))
    package = importlib.import_module("fastunknot")
    group = importlib.import_module("fastunknot.group_certificate")
    search = importlib.import_module("fastunknot.compressed_search")
    json_safe = importlib.import_module("fastunknot.integer_codec").json_safe
    print(json.dumps({"ready": True, "package": str(Path(package.__file__).resolve())}), flush=True)
    for line in sys.stdin:
        request = json.loads(line)
        action = request["action"]
        if action == "stop":
            return
        try:
            if action == "braid":
                try:
                    diagram = package.Diagram.from_braid(request["strands"], request["word"])
                    record = {"pd": diagram.pd, "valid_knot": True}
                except package.DiagramError as exc:
                    record = {"valid_knot": False, "reason": str(exc)}
            elif action == "certificate":
                stats = {}
                try:
                    certificate = search.compressed_certificate(
                        package.Diagram.from_pd(request["pd"]), stats=stats, **request["options"]
                    )
                    record = {"certificate": certificate, "stats": stats,
                              "status": "CERTIFICATE" if certificate else "STALLED"}
                except group.GroupLimit as exc:
                    record = {"certificate": None, "stats": stats, "status": "LIMIT",
                              "reason": str(exc)}
            elif action == "verify":
                valid = group.verify_group_certificate(
                    package.Diagram.from_pd(request["pd"]), request["certificate"],
                    **request["options"]
                )
                record = {"valid": valid}
            elif action in ("stages", "benchmark"):
                fn = group.group_decide if action == "stages" else package.recognize
                # Fresh input validation, discovery and mandatory source replay are timed.
                start = time.perf_counter()
                result = fn(package.Diagram.from_pd(request["pd"]), **request["options"])
                elapsed = time.perf_counter() - start
                if action == "stages":
                    status = result["status"]
                    groups = [result]
                    method = "group_decide"
                    reason = result.get("reason")
                else:
                    status = result.status
                    groups = group_records(result.evidence)
                    method = result.method
                    reason = result.evidence.get("reason")
                record = {"seconds": elapsed, "status": status, "method": method,
                          "completed": status in ("UNKNOT", "KNOTTED"),
                          "reason": reason, "groups": groups}
            else:
                raise ValueError(f"unknown worker action: {action}")
            print(json.dumps(json_safe(record), separators=(",", ":")), flush=True)
        except Exception as exc:
            import traceback
            traceback.print_exc(file=sys.stderr)
            print(json.dumps({"worker_error": type(exc).__name__, "message": str(exc)}), flush=True)


class Worker:
    def __init__(self, root, label):
        self.root = Path(root)
        self.label = label
        self.process = subprocess.Popen(
            [sys.executable, str(Path(__file__).resolve()), "--worker", str(self.root)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=sys.stderr,
            text=True, bufsize=1,
            env=dict(os.environ, PYTHONHASHSEED="0"),
        )
        self.ready = json.loads(self.process.stdout.readline())
        assert self.ready.get("ready"), self.ready
        assert Path(self.ready["package"]).is_relative_to(self.root.resolve())

    def call(self, request):
        assert self.process.poll() is None, self.label
        self.process.stdin.write(json.dumps(request, separators=(",", ":")) + "\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        assert line, ("worker exited", self.label, self.process.poll())
        result = json.loads(line)
        assert "worker_error" not in result, (self.label, request.get("action"), result)
        return result

    def close(self):
        if self.process.poll() is None:
            self.process.stdin.write('{"action":"stop"}\n')
            self.process.stdin.flush()
            self.process.wait(timeout=30)
        assert self.process.returncode == 0, (self.label, self.process.returncode)


def read_corpus(path):
    data = json.loads(Path(path).read_text())
    rows = data.get("rows", data.get("cases")) if isinstance(data, dict) else data
    assert isinstance(rows, list) and rows
    required = ("name", "pd", "expected")
    result = []
    for row in rows:
        source = row.get("source", row)
        assert all(key in source for key in required), source.keys()
        result.append({key: source[key] for key in ("name", "pd", "crossings", "expected")
                       if key in source})
    return result


def stage_sources(worker, sizes):
    rows = []
    for crossings in sizes:
        braid = {"strands": crossings + 1, "word": list(range(1, crossings + 1))}
        source = worker.call({"action": "braid", **braid})
        assert source["valid_knot"]
        rows.append({"name": f"stabilized-circle-{crossings}", "crossings": crossings,
                     "pd": source["pd"], "expected": "UNKNOT", "braid": braid,
                     "provenance": "Closure of sigma_1 ... sigma_n; successive stabilizations of the circle."})
    return rows


def cache_proof(proofs, certificate):
    if certificate is None:
        return None
    raw = plain_encode(certificate)
    key = sha256(raw).hexdigest()
    proofs[key] = certificate
    return {"certificate_sha256": key, "certificate_bytes": len(raw),
            "certificate_version": certificate["version"]}


def summarize(samples):
    arms = list(samples[0]["measurements"])
    medians = {}
    for arm in arms:
        values = [sample["measurements"][arm]["seconds"] for sample in samples
                  if sample["measurements"][arm]["completed"]]
        medians[arm] = median(values) if values else None
    pairs = [("versus_default", "baseline_default", "singleton"),
             ("versus_forest", "baseline_forest", "singleton")]
    pairs += [(arm + "_AA", arm, arm + "_AA")
              for arm in ("baseline_default", "baseline_forest", "singleton")]
    ratios = {}
    for label, numerator, denominator in pairs:
        values = [sample["measurements"][numerator]["seconds"] /
                  sample["measurements"][denominator]["seconds"]
                  for sample in samples
                  if sample["measurements"][numerator]["completed"]
                  and sample["measurements"][denominator]["completed"]]
        ratios[label] = {"count": len(values), "median": median(values) if values else None}
    return {"medians": medians, "paired_ratios": ratios}


def benchmark(workers, inputs, mode, rounds, feature_key):
    stage = mode == "stages"
    feature = feature_key if stage else "group_" + feature_key
    forest = "primitive_forest" if stage else "group_primitive_forest"
    arms = {
        "baseline_default": ("baseline", {}), "baseline_default_AA": ("baseline", {}),
        "baseline_forest": ("baseline", {forest: True}),
        "baseline_forest_AA": ("baseline", {forest: True}),
        "singleton": ("current", {feature: True}),
        "singleton_AA": ("current", {feature: True}),
    }
    common = (
        {"seconds": None, "max_work": 50_000_000, "max_nodes": 1_000_000,
         "compressed_search": True}
        if stage else
        {"use_group": True, "group_relators": True, "group_compressed_search": True,
         "group_seconds": 10, "group_max_work": 20_000_000,
         "seconds": 12, "max_objects": 50_000}
    )
    rng = random.Random(SEED + (2 if stage else 1))
    rows, proofs = [], {}
    for source in inputs:
        samples, warmups = [], []
        for iteration in range(-1, rounds):
            order = list(arms)
            rng.shuffle(order)
            measurements = {}
            for arm in order:
                worker_name, extra = arms[arm]
                result = workers[worker_name].call(
                    {"action": mode, "pd": source["pd"], "options": dict(common, **extra)}
                )
                if result["completed"]:
                    assert result["status"] == source["expected"], (source["name"], arm, result)
                records = []
                for group in result["groups"]:
                    certificate = group.pop("certificate", None)
                    proof = cache_proof(proofs, certificate)
                    if proof:
                        group.update(proof)
                        group["move_kinds"] = {}
                        for move in certificate["moves"]:
                            kind = move["kind"]
                            group["move_kinds"][kind] = group["move_kinds"].get(kind, 0) + 1
                    records.append(group)
                result["groups"] = records
                measurements[arm] = result
            record = {"iteration": iteration, "order": order, "measurements": measurements}
            (warmups if iteration < 0 else samples).append(record)
        row = {"source": source, "samples": samples, "warmups": warmups,
               **summarize(samples)}
        rows.append(row)
        print(source["name"], json.dumps({key: row[key] for key in ("medians", "paired_ratios")}),
              flush=True)
    completed = sum(result["completed"] for row in rows for sample in row["samples"]
                    for result in sample["measurements"].values())
    return {
        "cases": rows, "certificates": proofs, "rounds": rounds, "arms": arms,
        "common_options": common, "measured_calls": len(rows) * len(arms) * rounds,
        "warmup_calls": len(rows) * len(arms), "completed_calls": completed,
        "scope": (
            "Actual stabilized-circle source diagrams through the checked group stage only: "
            "fresh PD validation, discovery and mandatory source replay. Earlier diagram "
            "simplification is bypassed. These are not hard unknots and the ratios are not "
            "whole-recognition speedups. " if stage else
            "Complete fresh-PD recognition on the preserved ordinary corpus, including all "
            "preprocessing stages, group discovery if reached and mandatory source replay. "
        ) + "Six shuffled arms compare the entire pinned baseline default and forest policies "
        "with current singleton mode, each with an A/A control. Workers isolate full packages. "
        "Incomplete outcomes are retained and excluded from completed medians and paired ratios.",
    }


def audit(workers, ordinary, feature_key):
    inputs = list(ordinary)
    rng = random.Random(261008504)
    for index in range(240):
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 15))]
        candidate = workers["baseline"].call({"action": "braid", "strands": strands, "word": word})
        if candidate["valid_knot"]:
            inputs.append({"name": f"random-{index}", "pd": candidate["pd"],
                           "braid": {"strands": strands, "word": word},
                           "provenance": "Fixed-seed random braid conditioned on a validated single component."})
    inputs += stage_sources(workers["baseline"], (3, 4, 8, 16, 32, 64, 128))
    rows, proofs = [], {}
    modes = {"default": {}, "projection": {"primitive_projection": True},
             "forest": {"primitive_forest": True}}
    options = {"relator_moves": True, "max_work": 20_000_000, "max_nodes": 100_000}
    for source in inputs:
        legacy = {}
        for name, extra in modes.items():
            request = {"action": "certificate", "pd": source["pd"],
                       "options": dict(options, **extra)}
            before = workers["baseline"].call(request)
            after = workers["current"].call(request)
            assert before["certificate"] == after["certificate"], (source["name"], name)
            assert before["status"] == after["status"], (source["name"], name, before, after)
            proof = cache_proof(proofs, after["certificate"])
            legacy[name] = {"proof": proof, "status": after["status"],
                            "old_stats": before["stats"], "new_stats": after["stats"]}
        after = workers["current"].call({"action": "certificate", "pd": source["pd"],
                                           "options": dict(options, **{feature_key: True})})
        certificate = after.pop("certificate")
        if certificate is not None:
            for compressed in (False, True):
                verified = workers["current"].call(
                    {"action": "verify", "pd": source["pd"], "certificate": certificate,
                     "options": {"compressed": compressed, "max_work": 20_000_000,
                                 "max_nodes": 100_000}}
                )
                assert verified["valid"], (source["name"], compressed)
            assert source.get("expected", "UNKNOT") == "UNKNOT", source["name"]
        after["proof"] = cache_proof(proofs, certificate)
        rows.append({"source": source, "legacy": legacy, "singleton": after})
        if len(rows) % 10 == 0:
            print("audit", len(rows), "diagrams", flush=True)
    return {
        "cases": rows, "certificates": proofs, "diagrams": len(rows),
        "legacy_mode_comparisons": 3 * len(rows),
        "legacy_certificates_and_nondecisions_identical": True,
        "singleton_certificates": sum(bool(row["singleton"]["proof"]) for row in rows),
        "newly_closed_versus_default": sum(bool(row["singleton"]["proof"])
            and not bool(row["legacy"]["default"]["proof"]) for row in rows),
        "lost_positives_versus_default": sum(not bool(row["singleton"]["proof"])
            and bool(row["legacy"]["default"]["proof"]) for row in rows),
        "newly_closed_versus_forest": sum(bool(row["singleton"]["proof"])
            and not bool(row["legacy"]["forest"]["proof"]) for row in rows),
        "lost_positives_versus_forest": sum(not bool(row["singleton"]["proof"])
            and bool(row["legacy"]["forest"]["proof"]) for row in rows),
        "scope": "Actual validated source diagrams. Default, projection and forest legacy "
        "certificates and bounded nondecisions are compared exactly against the full pinned "
        "baseline. Every singleton-enabled positive passes independent literal and compressed "
        "replay from its source. This finite audit does not establish completeness."
    }


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--worker":
        worker_main(sys.argv[2])
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("audit", "benchmark", "stages"))
    parser.add_argument("--baseline-fast", type=Path, required=True)
    parser.add_argument("--current-fast", type=Path, required=True)
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--snapshots", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--sizes", type=int, nargs="+", default=(16, 32, 64, 128, 256))
    parser.add_argument("--feature-key", default="singleton_dag")
    args = parser.parse_args()
    assert args.rounds >= 1
    assert args.corpus is not None or args.mode == "stages"
    before = {"baseline": file_hashes(args.baseline_fast / "fastunknot"),
              "current": file_hashes(args.current_fast / "fastunknot")}
    script_hash = sha256(Path(__file__).read_bytes()).hexdigest()
    original_roots = {"baseline": args.baseline_fast, "current": args.current_fast}
    frozen_roots = {key: args.snapshots / key for key in original_roots}
    for key in original_roots:
        assert freeze_package(original_roots[key], frozen_roots[key]) == before[key]
    workers = {key: Worker(root, key) for key, root in frozen_roots.items()}
    start = time.perf_counter()
    try:
        ordinary = read_corpus(args.corpus) if args.corpus is not None else None
        if args.mode == "audit":
            result = audit(workers, ordinary, args.feature_key)
        else:
            inputs = stage_sources(workers["baseline"], args.sizes) if args.mode == "stages" else ordinary
            result = benchmark(workers, inputs, args.mode, args.rounds, args.feature_key)
    finally:
        for worker in workers.values():
            worker.close()
    assert before == {key: file_hashes(root / "fastunknot") for key, root in original_roots.items()}
    assert before == {key: file_hashes(root / "fastunknot") for key, root in frozen_roots.items()}
    assert script_hash == sha256(Path(__file__).read_bytes()).hexdigest()
    result.update(
        mode=args.mode, baseline_commit=BASELINE_COMMIT, feature_key=args.feature_key,
        seed=SEED + (0 if args.mode == "audit" else 2 if args.mode == "stages" else 1),
        seconds=time.perf_counter() - start, python=platform.python_version(),
        executable=sys.executable, platform=platform.platform(), python_hash_seed="0",
        source_sha256=before, script_sha256=script_hash, source_hashes_unchanged=True,
        corpus_sha256=sha256(args.corpus.read_bytes()).hexdigest() if args.corpus else None,
        timing_boundary="Worker perf_counter encloses fn(Diagram.from_pd(pd), **options), "
        "and stops before result traversal or serialization. Imports and IPC are outside timers."
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    excluded = {"cases", "certificates", "source_sha256"}
    print(json.dumps({key: value for key, value in result.items() if key not in excluded}, indent=2), flush=True)


if __name__ == "__main__":
    main()
