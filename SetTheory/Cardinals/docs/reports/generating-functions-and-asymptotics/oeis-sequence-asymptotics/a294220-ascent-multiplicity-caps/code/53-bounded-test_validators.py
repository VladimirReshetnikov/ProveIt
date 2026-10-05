#!/usr/bin/env python3
"""Fail-closed regression tests, including subprocess runs with and without -O."""
from __future__ import annotations

import ast
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from bounded_exact import DATA, VerificationError, load_json, require, same

HERE = Path(__file__).resolve().parent
FILES = ("expected_counts.json", "expected_histograms.json", "published_counts.json")


def run_case(label, documents, mutations, raw_replacements=None, enumeration=False):
    changed = copy.deepcopy(documents)
    for filename, mutate in mutations:
        mutate(changed[filename])
    with tempfile.TemporaryDirectory(prefix="bounded-ascent-invalid-") as directory:
        directory = Path(directory)
        for filename, document in changed.items():
            text = json.dumps(document)
            if raw_replacements and filename in raw_replacements:
                text = raw_replacements[filename](text)
            (directory/filename).write_text(text, encoding="utf-8")
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else [])
            command += [str(HERE/"bounded_exact.py"), "--data-dir", str(directory),
                        "--enumeration-only" if enumeration else "--validate-only"]
            env = dict(os.environ)
            env.pop("PYTHONOPTIMIZE", None)
            env["PYTHONDONTWRITEBYTECODE"] = "1"
            completed = subprocess.run(command, text=True, capture_output=True, env=env)
            require(completed.returncode == 1,
                    f"negative test {label!r} optimized={optimized}: expected exit 1; "
                    f"got {completed.returncode}; stdout={completed.stdout!r}; stderr={completed.stderr!r}")
            require(completed.stderr.startswith("FAIL: "),
                    f"negative test {label!r}: did not fail through an explicit verification exception")
    return 2


def set_field(key, value):
    def mutate(obj):
        obj[key] = value
    return mutate


def main():
    # This scan prevents a later accidental regression to removable assertions.
    for path in HERE.glob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)),
                f"removable assertion statement found in {path.name}")
    documents = {name: load_json(DATA/name) for name in FILES}
    countfile, histfile, pubfile = FILES
    cases = []

    def case(name, filename, mutate):
        cases.append((name, [(filename, mutate)], None, False))

    case("missing count row", countfile, lambda d: d["rows"].pop())
    case("duplicate count row", countfile, lambda d: d["rows"].append(copy.deepcopy(d["rows"][0])))
    case("truncated count values", countfile, lambda d: d["rows"][0]["values"].pop())
    case("extra count value", countfile, lambda d: d["rows"][0]["values"].append(99))
    case("count r below range", countfile, lambda d: d["rows"][0].update(r=1))
    case("count r above range", countfile, lambda d: d["rows"][0].update(r=7))
    case("count r noninteger", countfile, lambda d: d["rows"][0].update(r=2.0))
    case("count float", countfile, lambda d: d["rows"][0]["values"].__setitem__(2, 2.0))
    case("count boolean", countfile, lambda d: d["rows"][0]["values"].__setitem__(2, True))
    case("count string", countfile, lambda d: d["rows"][0]["values"].__setitem__(2, "2"))
    case("count negative", countfile, lambda d: d["rows"][0]["values"].__setitem__(2, -2))
    case("count zero", countfile, lambda d: d["rows"][0]["values"].__setitem__(2, 0))
    case("false empty count", countfile, lambda d: d["rows"][0]["values"].__setitem__(0, 2))
    case("unknown count field", countfile, lambda d: d.update(ignored=True))
    case("missing count coverage", countfile, lambda d: d.pop("coverage"))
    case("reduced declared count coverage", countfile, lambda d: d["coverage"].update(n_max=9))
    case("boolean count schema version", countfile, lambda d: d.update(schema_version=True))
    case("nonarray count rows", countfile, lambda d: d.update(rows={}))

    case("missing histogram row", histfile, lambda d: d["rows"].pop())
    case("duplicate histogram row", histfile, lambda d: d["rows"].append(copy.deepcopy(d["rows"][0])))
    case("histogram n zero", histfile, lambda d: d["rows"][0].update(n=0))
    case("histogram n too large", histfile, lambda d: d["rows"][0].update(n=11))
    case("histogram n boolean", histfile, lambda d: d["rows"][0].update(n=True))
    case("histogram r too large", histfile, lambda d: d["rows"][0].update(r=7))
    case("empty endpoint list", histfile, lambda d: d["rows"][0].update(endpoints=[]))
    case("missing endpoint bin", histfile, lambda d: d["rows"][-1]["endpoints"].pop())
    case("duplicate endpoint bin", histfile, lambda d: d["rows"][0]["endpoints"].append(copy.deepcopy(d["rows"][0]["endpoints"][0])))
    case("wrong endpoint dimension", histfile, lambda d: d["rows"][0]["endpoints"][0]["x"].pop())
    case("negative endpoint coordinate", histfile, lambda d: d["rows"][0]["endpoints"][0]["x"].__setitem__(0, -1))
    case("too large endpoint coordinate", histfile, lambda d: d["rows"][0]["endpoints"][0]["x"].__setitem__(0, 3))
    case("floating endpoint coordinate", histfile, lambda d: d["rows"][0]["endpoints"][0]["x"].__setitem__(0, 1.0))
    case("boolean endpoint coordinate", histfile, lambda d: d["rows"][0]["endpoints"][0]["x"].__setitem__(0, True))
    case("impossible endpoint statistics", histfile, lambda d: d["rows"][0]["endpoints"][0].update(x=[0, 1]))
    case("zero endpoint count", histfile, lambda d: d["rows"][0]["endpoints"][0].update(count=0))
    case("noninteger endpoint count", histfile, lambda d: d["rows"][0]["endpoints"][0].update(count=1.0))
    case("boolean endpoint count", histfile, lambda d: d["rows"][0]["endpoints"][0].update(count=True))
    case("incorrect endpoint total", histfile, lambda d: d["rows"][0]["endpoints"][0].update(count=2))
    case("reduced declared histogram coverage", histfile, lambda d: d["coverage"].update(n_max=9))
    case("unknown endpoint field", histfile, lambda d: d["rows"][0]["endpoints"][0].update(ignored=0))

    case("missing published source", pubfile, lambda d: d["sources"].pop())
    case("duplicate published source", pubfile, lambda d: d["sources"].append(copy.deepcopy(d["sources"][0])))
    case("wrong published source", pubfile, lambda d: d["sources"][0].update(oeis="A000000"))
    case("wrong published URL", pubfile, lambda d: d["sources"][0].update(url="https://example.org"))
    case("missing published row", pubfile, lambda d: d["sources"][1]["rows"].pop())
    case("duplicate published row", pubfile, lambda d: d["sources"][1]["rows"].append(copy.deepcopy(d["sources"][1]["rows"][0])))
    case("truncated published values", pubfile, lambda d: d["sources"][0]["rows"][0]["values"].pop())
    case("noninteger published count", pubfile, lambda d: d["sources"][0]["rows"][0]["values"].__setitem__(2, 2.0))
    case("published r out of range", pubfile, lambda d: d["sources"][0]["rows"][0].update(r=3))
    case("reduced declared published coverage", pubfile, lambda d: d["sources"][0].update(n_max=10))

    for filename in FILES:
        cases.append((f"malformed JSON {filename}", [], {filename: lambda text: "not json"}, False))
        cases.append((f"truncated JSON {filename}", [], {filename: lambda text: text[:-2]}, False))
        cases.append((f"duplicate JSON key {filename}", [], {filename: lambda text: text.replace('"schema_version": 1', '"schema_version": 1, "schema_version": 1', 1)}, False))
        cases.append((f"nonfinite JSON constant {filename}", [], {filename: lambda text: text.replace('"schema_version": 1', '"schema_version": NaN', 1)}, False))

    # Syntactically valid fixtures with valid coverage and internally consistent
    # totals must still fail against independently recomputed mathematics.
    def corrupt_count(d):
        d["rows"][0]["values"][2] += 1

    def match_corrupt_count(d):
        row = next(row for row in d["rows"] if row["r"] == 2 and row["n"] == 2)
        row["endpoints"][0]["count"] += 1

    cases.append(("wrong values despite consistent totals", [(countfile, corrupt_count), (histfile, match_corrupt_count)], None, True))

    def corrupt_histogram_preserving_total(d):
        row = next(row for row in d["rows"] if row["r"] == 2 and row["n"] == 10)
        donor = next(item for item in row["endpoints"] if item["count"] > 1)
        recipient = next(item for item in row["endpoints"] if item is not donor)
        donor["count"] -= 1
        recipient["count"] += 1

    cases.append(("wrong histogram despite correct total", [(histfile, corrupt_histogram_preserving_total)], None, True))
    cases.append(("wrong published value", [(pubfile, lambda d: d["sources"][0]["rows"][0]["values"].__setitem__(11, 77452))], None, True))

    children = 0
    for label, mutations, raw, enumeration in cases:
        children += run_case(label, documents, mutations, raw, enumeration)
    same(len(cases), 64, "negative-case test coverage")
    same(children, 128, "normal/optimized child coverage")
    print(f"PASS {len(cases)} malformed/incomplete/wrong-value cases rejected in {children} subprocesses, half with -O", flush=True)
    print("PASS source scan: no correctness check uses a removable assertion statement", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except VerificationError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
