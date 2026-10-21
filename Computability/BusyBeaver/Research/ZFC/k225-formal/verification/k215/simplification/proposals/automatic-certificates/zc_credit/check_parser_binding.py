#!/usr/bin/env python3
"""Finite independent comparison of the extracted Coq parser and exact ZC data.

Checks literal source field-reader/refill contracts, not complete AX/MP bodies
or the binary implementation. Requires coqc, ocamlc and the pinned checkout.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader
    spec.loader.exec_module(module)
    return module


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--zc", required=True, type=Path,
                    help="candidate-k215/alternatives/zero-credit directory")
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--limit", type=int, default=1000)
    a = ap.parse_args()
    assert a.limit >= 6
    a.out.mkdir(parents=True, exist_ok=False)
    here = Path(__file__).resolve().parent
    for name in ["ConcretePrefixCredit.v", "ExtractCodec.v", "codec_driver.ml"]:
        shutil.copyfile(here/name, a.out/name)
    commands = [["coqc", "-q", "ConcretePrefixCredit.v"],
                ["coqc", "-q", "ExtractCodec.v"],
                ["ocamlc", "-c", "codec.mli"],
                ["ocamlc", "-o", "codec_driver", "codec.ml", "codec_driver.ml"]]
    for i, command in enumerate(commands):
        r = subprocess.run(command, cwd=a.out, text=True, capture_output=True)
        (a.out/f"build-{i}.log").write_text(r.stdout+r.stderr)
        if r.returncode:
            raise RuntimeError(f"Command failed: {command}")
    r = subprocess.run([str(a.out.resolve()/"codec_driver"), str(a.limit)],
                       text=True, capture_output=True, check=True)
    (a.out/"extracted_words.jsonl").write_text(r.stdout)
    extracted = [json.loads(s) for s in r.stdout.splitlines()]
    model_path = a.zc/"code/check_tag_lowering.py"
    language_path = a.zc/"code/source_language.py"
    source_path = a.zc/"source/zc215.sites.json"
    model = load("tag_lowering_reference", model_path)
    language = load("source_reference", language_path)
    rows = json.loads(source_path.read_text())
    graph = language.graph_intervals(rows)
    assert language.graph_arithmetic(rows)[0] == graph
    assert len(rows) == 4752
    total_steps = 0

    def run(start, stop, registers, budget):
        nonlocal total_steps
        registers = list(registers)
        pc, steps = start, 0
        while pc != stop:
            assert steps < budget, (start, pc, registers)
            _, op, k = rows[pc]
            targets = graph[pc][1]
            if op == "CI":
                registers[k] += 1
                pc = targets[0]
            elif op == "CD":
                positive = int(registers[k] > 0)
                registers[k] -= positive
                pc = targets[positive]
            elif op in ("CB", "CC"):
                pc = targets[0]
            else:
                raise AssertionError("Unexpected halt in field reader")
            steps += 1
        total_steps += steps
        return registers

    readers = [(10,24,3), (4592,4606,4), (160,174,5), (201,215,4)]
    for n in range(a.limit):
        index, encoded, word = extracted[n]
        assert index == encoded == n
        assert word == [list(k) for k in model.parse(n)]
        assert model.encode(tuple(tuple(k) for k in word)) == n
        tag, residual = model.unpair(n)
        for start,stop,target in readers:
            before = [0]*9
            before[8] = n
            after = run(start,stop,before,100*n+1000)
            expected = [0]*9
            expected[target],expected[8] = tag,residual
            assert after == expected, (n,start,after,expected)
        # Literal refill and positive-continuation paths into the tag reader.
        before = [0]*9
        before[0] = n+1
        after = run(0,10,before,100*n+1000)
        expected = [0]*9
        expected[0],expected[8] = n+2,n
        assert after == expected, ("refill",n,after)
        before = [0]*9
        before[0],before[8] = 7,n+1
        after = run(0,10,before,100*n+1000)
        expected = before.copy()
        expected[8] = n
        assert after == expected
        # Literal dispatcher distinguishes the actual command tags.
        before = [0]*9
        before[3],before[8] = tag,residual
        stop = [4726,4699,4592][tag] if tag < 3 else 27
        after = run(24,stop,before,8)
        assert after[3] == max(tag-3,0) and after[8] == residual
    receipt = {
        "status": "PASS",
        "scope": "Finite extracted-code/parser comparison and literal isolated source reader/refill/dispatch contracts; not a full source or binary correctness proof",
        "candidate_range": [0,a.limit],
        "upper_bound_exclusive": True,
        "matched_extracted_Coq_words": len(extracted),
        "matched_literal_field_reader_cases": a.limit*len(readers),
        "matched_literal_refill_cases": a.limit,
        "matched_literal_positive_continuation_cases": a.limit,
        "matched_literal_dispatch_cases": a.limit,
        "literal_source_steps": total_steps,
        "source_leaf_count": len(rows),
        "raw_zero": extracted[0],
        "trailing_zero_example": extracted[2],
        "hashes": {
            "ConcretePrefixCredit.v": sha(here/"ConcretePrefixCredit.v"),
            "ExtractCodec.v": sha(here/"ExtractCodec.v"),
            "codec_driver.ml": sha(here/"codec_driver.ml"),
            "check_parser_binding.py": sha(Path(__file__)),
            "zc215.sites.json": sha(source_path),
            "reference_check_tag_lowering.py": sha(model_path),
            "reference_source_language.py": sha(language_path),
            "extracted_words.jsonl": sha(a.out/"extracted_words.jsonl"),
        },
        "build_commands": commands,
    }
    (a.out/"result.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must be enabled")
    main()
