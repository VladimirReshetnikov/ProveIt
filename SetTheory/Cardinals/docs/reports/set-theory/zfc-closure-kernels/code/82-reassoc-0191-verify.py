#!/usr/bin/env python3
"""Reproduce the archive's claims, including expected rejected experiments.

PASS means the research findings reproduce. It does not certify any complete
consistency machine below246 states. Standard library only; no network.
All reconstruction occurs in a temporary directory; inputs remain unchanged.
"""
from __future__ import annotations
import argparse
import contextlib
import copy
from hashlib import sha256
import importlib.util
import io
import json
from pathlib import Path
import runpy
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
REFERENCE = ROOT / "reference/context246"
sys.dont_write_bytecode = True


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def json_read(path):
    return json.loads(path.read_text())


def without_seconds(value):
    if isinstance(value, dict):
        return {k: without_seconds(v) for k, v in value.items() if k != "seconds"}
    if isinstance(value, list):
        return [without_seconds(v) for v in value]
    return value


def manifest_check():
    manifest = ROOT / "SHA256SUMS"
    if not manifest.exists():
        return {"status": "NOT_YET_FROZEN", "files": 0}
    count = 0
    for line in manifest.read_text().splitlines():
        want, name = line.split("  ", 1)
        path = (ROOT / name).resolve()
        require(path.is_relative_to(ROOT), "Manifest path escapes package")
        require(path.is_file() and digest(path) == want, "Hash mismatch: " + name)
        count += 1
    return {"status": "PASS", "files": count}


def macro_inductions():
    sys.path.insert(0, str(REFERENCE / "code"))
    proof = load("prefix246_macro_review", REFERENCE / "code/check_macro_inductions.py")

    class ReadTrackingDict(dict):
        reads = set()
        def __getitem__(self, key):
            self.reads.add(key)
            return super().__getitem__(key)

    proof.TABLE = ReadTrackingDict(proof.TABLE)
    proof.prove_blocks()
    word = proof.prove_word_identity()
    macros = proof.prove_macros()
    marks = proof.prove_marks()
    support = sorted(proof.TABLE.reads)
    require(len(support) == 42, "Unexpected macro transition support")
    record = {
        "status": "PASS_ORDINARY_INDUCTION_PREMISES",
        "proof_assistant_endpoint": False,
        "support_rows": [list(row) for row in support],
        "block_theorems": list(proof.BLOCK_PROOFS.values()),
        "word_identity": word,
        "macro_theorems": macros,
        "mark_theorems": marks,
    }
    return proof.TABLE, support, record


def parse_tm(path):
    table, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        if not line or line.startswith("#"):
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        require((q, b) not in table, "Duplicate transition")
        require(b in (0, 1) and w in (0, 1) and d in ("L", "R"), "Invalid row")
        table[q, b] = (w, d, t)
    states = {q for q, _ in table}
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, "Incomplete table")
    require({t for w, d, t in table.values()} - states == {254}, "Wrong halt closure")
    require(start == 95, "Wrong old-label start")
    return table, start


def blank_replay(table, start, ticks=410735):
    q, head, ones = start, 0, set()
    for tick in range(ticks):
        require(q != 254, "Unexpected halt during bootstrap at " + str(tick))
        w, d, q = table[q, int(head in ones)]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if d == "R" else -1
    return q, head, ones


def exact_bootstraps(tables):
    values = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167
    ones = {-6, 176}
    position = 177
    for value in values:
        ones.update(range(position + 1, position + value + 2))
        position += value + 2
    goal = (96, -5, ones)
    result = {}
    for name, table in tables.items():
        actual = blank_replay(table, 95)
        require(actual == goal, "Complete bootstrap mismatch: " + name)
        result[name] = {
            "status": "PASS_EXACT_FINITE_BOOTSTRAP",
            "steps": 410735, "start": 95, "exit_state": 96, "head": -5,
            "marker": -6, "header": 176, "one_count": len(ones),
            "all_one_positions": sorted(ones), "all_other_cells_zero": True,
            "physical_primary_values": values[:9], "spare_values": values[9:],
            "whole_runtime_or_consistency_claim": False,
        }
    return result


def invoke_main(module, arguments):
    previous = sys.argv
    sys.argv = [str(module.__file__), *map(str, arguments)]
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            module.main()
    finally:
        sys.argv = previous


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON report; otherwise inputs stay unchanged.")
    parser.add_argument("--hashes-only", action="store_true")
    args = parser.parse_args()
    require(__debug__, "Do not run with -O; assertions are verification gates.")
    began = time.monotonic()
    hashes = manifest_check()
    if args.hashes_only:
        require(hashes["status"] == "PASS", "No frozen manifest")
        print(json.dumps(hashes, indent=2))
        return

    pins = {
        "machine/zfc_prefix246_old.tm": "303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee",
        "sources/Prog254.v": "1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746",
    }
    for path, expected in pins.items():
        require(digest(REFERENCE / path) == expected, "Pinned input mismatch: " + path)
    macro_table, support, macro_record = macro_inductions()
    print("PASS: inherited ordinary macro induction premises;42 exact support rows.", flush=True)

    sys.path.insert(0, str(ROOT / "decoder"))
    import rotation_candidate as decoder
    audit = load("independent_rm_audit", ROOT / "audit/check_rm_certificate.py")
    original_program = audit.load_program(REFERENCE / "sources/Prog254.v")
    delivered = ROOT / "decoder/rotation_candidates"
    tables = {"baseline246": decoder.T}
    source_results, affine_results, reconstruction = {}, {}, {}
    recipes = [
        (178, 208, 1, 23, 24, 206, 16),
        (190, 99, 1, 105, 105, 114, 179),
        (219, 178, 1, 206, 23, 208, 205),
        (226, 193, 0, 190, 213, 231, 207),
    ]
    expected_cases = {178: 1166, 190: 2651, 219: 5655, 226: 8391}
    with tempfile.TemporaryDirectory(prefix="bb246_research_verify_") as temporary:
        temp = Path(temporary)
        decoder.HERE = temp / "decoder"
        decoder.HERE.mkdir()
        baseline_affine = decoder.check(decoder.T, decoder.nodes)
        require(baseline_affine["status"] == "PASS", "Baseline affine failure")
        require(baseline_affine["counts"] == {"cases": 8391, "rules": 2911962}, "Baseline count mismatch")
        for recipe in recipes:
            q = recipe[0]
            with contextlib.redirect_stdout(io.StringIO()):
                evidence = decoder.recipe(*recipe)
            made = decoder.HERE / "rotation_candidates"
            for suffix in (".tm", "_source.json", "_bisimulation.json"):
                name = "rotation" + str(q) + suffix
                require((made / name).read_bytes() == (delivered / name).read_bytes(),
                        "Reconstruction differs: " + name)
            table, start = parse_tm(made / ("rotation" + str(q) + ".tm"))
            require(len(table) // 2 == (245 if q == 178 else 246), "Wrong state count")
            require(all(table[key] == macro_table[key] for key in support),
                    "Changed macro support in decoder experiment")
            new_program = audit.load_program(made / ("rotation" + str(q) + "_source.json"))
            certificate = json_read(made / ("rotation" + str(q) + "_bisimulation.json"))
            checked = audit.verify(original_program, new_program, certificate)
            require(checked["pairs"] == checked["reachable_pairs"] == 4533, "Wrong reachable pair count")
            require(checked["branches"] == 6463, "Wrong branch count")
            actual = evidence["affine"]
            expected_status = "PASS" if q == 226 else "FAIL"
            require(actual["status"] == expected_status, "Unexpected affine outcome")
            require(actual["counts"]["cases"] == expected_cases[q], "Changed failure location or coverage")
            if q == 178:
                require(actual["index"] == 894 and actual["pc"] == "11101001001010100111000000"
                        and actual["zero"] is True and actual["r"] == 1, "Wrong documented178 rejection")
                tables["rotation178_245"] = table
            if q == 226:
                require(actual["counts"]["rules"] == 2912625, "Changed226 rule count")
                tables["rotation226_246"] = table
            source_results[str(q)] = checked
            affine_results[str(q)] = actual
            reconstruction[str(q)] = {
                "table_sha256": digest(made / ("rotation" + str(q) + ".tm")),
                "states": len(table) // 2, "rows": len(table),
                "source_occurrences": len(evidence["source_changes"]),
                "exact_reconstruction": True, "macro_support_unchanged": True,
            }
            print(f"PASS: rotation{q} source certificate; affine {expected_status}"
                  f" after{actual['counts']['cases']} cases (expected).", flush=True)

        # A meaningful negative control: the independent checker must reject
        # both a corrupt operation label and a corrupt successor pair.
        controls = {}
        for kind in ("operation", "successor"):
            bad = copy.deepcopy(certificate)
            if kind == "operation":
                bad["pairs"][0]["instruction"] = "EInc 99"
            else:
                row = next(row for row in bad["pairs"] if row["successors"])
                row["successors"][0] = (row["successors"][0] + 1) % len(bad["pairs"])
            try:
                audit.verify(original_program, new_program, bad)
            except (ValueError, IndexError, KeyError) as ex:
                controls[kind] = {"rejected": True, "reason": str(ex)}
            else:
                raise RuntimeError("Corrupt certificate accepted: " + kind)

        bootstraps = exact_bootstraps(tables)
        print("PASS: baseline and both decoder tables have the exact410735-step blank frame.", flush=True)
        # The literal fixture imports the freshly reconstructed candidate from
        # decoder.HERE; it writes only into this temporary directory.
        with contextlib.redirect_stdout(io.StringIO()):
            runpy.run_path(str(ROOT / "decoder/concrete_rotation_failure.py"),
                           run_name="__main__")
        literal = json_read(decoder.HERE / "rotation_candidates/rotation178_literal_counterexample.json")
        require(literal == json_read(delivered / "rotation178_literal_counterexample.json"),
                "Literal discrepancy changed")
        require(literal["runs"]["baseline246"]["steps"] == 380 and
                literal["runs"]["rotation178_245"]["steps"] == 378, "Wrong literal return timing")

        kernel = load("mtf_local_verifier", ROOT / "kernel/verify_mtf.py")
        kernel.HERE = temp / "kernel"
        kernel.HERE.mkdir()
        invoke_main(kernel, ["--baseline", REFERENCE / "machine/zfc_prefix246_old.tm"])
        mtf = json_read(kernel.HERE / "mtf-verification.json")
        require(mtf == json_read(ROOT / "kernel/mtf-verification.json"), "MTF premises changed")
        require((kernel.HERE / "candidate-mtf245-local.tm").read_bytes() ==
                (ROOT / "kernel/candidate-mtf245-local.tm").read_bytes(), "MTF table changed")

        cfg = load("mtf_specialization_diagnostic", ROOT / "kernel/mtf_cfg.py")
        cfg_output = kernel.HERE / "mtf-permutation-cfg.json"
        invoke_main(cfg, ["--program", REFERENCE / "sources/Prog254.v", "--output", cfg_output])
        diagnostic = json_read(cfg_output)
        require(without_seconds(diagnostic) ==
                without_seconds(json_read(ROOT / "kernel/mtf-permutation-cfg.json")),
                "Permutation closure diagnostic changed")
        print("PASS:2040 MTF local fixtures, literal induction premises, header obstruction,"
              " and11117-pair permutation diagnostic.", flush=True)

    result = {
        "status": "PASS_RESEARCH_FINDINGS_REPRODUCED",
        "complete_sub246_machine_certified": False,
        "fresh_proof_assistant_endpoint": False,
        "serialized_internal_zfc_proof": False,
        "manifest": hashes,
        "pinned_inputs": pins,
        "reconstruction": reconstruction,
        "independent_register_certificates": source_results,
        "negative_certificate_controls": controls,
        "baseline_affine": baseline_affine,
        "candidate_affine": affine_results,
        "macro_induction_premises": macro_record,
        "bootstraps": bootstraps,
        "literal178_counterexample": literal,
        "mtf_local": mtf,
        "permutation_diagnostic": diagnostic,
        "optional_searches_rerun_by_default": False,
        "seconds": time.monotonic() - began,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS_RESEARCH_FINDINGS_REPRODUCED; no complete sub246 machine certified.")
    print("Elapsed seconds:", round(result["seconds"], 3))


if __name__ == "__main__":
    main()
