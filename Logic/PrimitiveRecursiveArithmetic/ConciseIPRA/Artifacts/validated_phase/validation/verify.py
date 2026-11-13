"""Independent process regression suite for the eager entry three-field core.

This is an untrusted development script. Its cases exercise canonical proof
paths, grammar and alphabet rejection, false goals, and witness scope. It does
not claim to prove the universal mathematical soundness theorem by testing.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import ast
import copy
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tempfile
import tokenize

from translate import translate

ROOT = Path(__file__).resolve().parent
UPSTREAM = ROOT / "reference"
CANDIDATE = ROOT / "checker_candidate300.py"
CONTROL = UPSTREAM / "code/checker_entry_tokens304.py"


def measure(path):
    source = path.read_bytes()
    tree = ast.parse(source)
    normalized = (ast.unparse(tree) + "\n").encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {"tokens": sum(t.type not in ignored for t in
                          tokenize.tokenize(io.BytesIO(normalized).readline)),
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_bytes": len(normalized),
            "gzip9_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            "source_sha256": hashlib.sha256(source).hexdigest()}


def run(job):
    name, path, document, expected, optimized = job
    result = subprocess.run([sys.executable, *(["-O"] if optimized else []), str(path)],
                            input=json.dumps(document), text=True,
                            capture_output=True, timeout=15)
    accepted = result.returncode == 0 and result.stdout == "ACCEPT\n"
    return {"case": name, "profile": path.name, "optimized": optimized,
            "expected": expected, "accepted": accepted,
            "exit_code": result.returncode, "pass": accepted == expected}


def replace_name(tree, old, new):
    if type(tree) is list:
        return [replace_name(x, old, new) for x in tree]
    return new if tree == old else tree


def main():
    source_cases = json.loads((UPSTREAM / "certificates/checker_entry_tokens304.json").read_text())["cases"]
    positives = [case for case in source_cases if case["expected"]]
    cases = []
    compilation = []
    control_jobs = []
    for case in positives:
        document, stats = translate(case["certificate"])
        compilation.append({"name": case["name"], "stats": stats})
        cases.append((case["name"], document, True))
        cases.append((case["name"] + "_false_zero_one", document[:-1] + [[1, [1]]], False))
        cases.append((case["name"] + "_false_one_zero", document[:-1] + [[[1], 1]], False))
        cases.append((case["name"] + "_missing_root_packet", document[:-2] + document[-1:], False))
        control_jobs.extend((case["name"], CONTROL, case["certificate"], True, opt)
                            for opt in (False, True))

    base = cases[0][1]
    for index, goal in enumerate([0, 1, [], [0, 1], [2, 1], [3, 1], [-1, 1],
                                  [[0]], [[1]], [1, 1, 1], [[], 1],
                                  True, 1.5, None, "x", {}]):
        cases.append(("invalid_public_" + str(index), base[:-1] + [goal], False))
    for index, value in enumerate([None, True, False, 1.5, "", {}, "unused",
                                   float("nan"), float("inf"), float("-inf")]):
        cases.append(("invalid_unused_alphabet_" + str(index), [value] + base, False))
    for index, value in enumerate([[], [0], [0, 1], [0, 1, 2, 3], 0, None]):
        cases.append(("malformed_root_packet_" + str(index), base[:-2] + [value] + base[-1:], False))
    cases.append(("valid_unused_integer_prefix", [31] + base, True))
    cases.append(("valid_unused_list_prefix", [[-100, [1, 2, 3], []]] + base, True))
    cases.append(("no_packets", [base[-1]], False))
    cases.append(("scalar_top_level", 0, False))
    cases.append(("empty_top_level", [], False))

    capture = json.loads((ROOT / "future_witness_capture.json").read_text())
    cases.append(("future_witness_capture", capture, False))
    for name in (-1, -3, -4, -5):
        cases.append(("future_witness_name_" + str(name), replace_name(capture, -2, name), False))

    # These attacks retain the old public codec and concern used scope or false
    # goals. Their raw packet protocols are not universally translated.
    inherited = json.loads((UPSTREAM / "reference/fixtures/three_field_cases.json").read_text())["cases"]
    for case in inherited:
        if case["name"].startswith("raw_attack_"):
            document = copy.deepcopy(case["certificate"])
            for packet in document[:-1]:
                if type(packet) is list and len(packet) == 3 and packet[0] == 0 and packet[1] in ([], 0, 2):
                    packet[0] = []
            cases.append(("inherited_" + case["name"], document, False))

    jobs = [(name, CANDIDATE, doc, expected, opt)
            for name, doc, expected in cases for opt in (False, True)]
    jobs.extend(control_jobs)
    # Build the deliberately invalid ordering only in a temporary directory.
    # It is a boundary diagnostic, never an installable checker artifact.
    old = "i(s * 3 or (a := i(*a, t, 2)), (c(g, s) or s or len(a) == 2 == u) and k)"
    new = "i(c(g, s) or s * 3 or (a := i(*a, t, 2)), (s or len(a) == 2 == u) and k)"
    source = CANDIDATE.read_text()
    if source.count(old) != 1:
        raise ValueError("The reviewed candidate source changed")
    with tempfile.TemporaryDirectory(prefix="ipra_boundary_") as directory:
        diagnostic = Path(directory) / "UNSOUND_late_witness.py"
        diagnostic.write_text(source.replace(old, new))
        jobs.extend(("late_witness_negative_control", diagnostic, capture, True, opt)
                    for opt in (False, True))
        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(run, jobs))
    failures = [row for row in results if not row["pass"]]
    receipt = {"python": sys.version,
               "candidate": measure(CANDIDATE), "matched_entry_control": measure(CONTROL),
               "canonical_compiler_input": str(UPSTREAM / "certificates/checker_entry_tokens304.json"),
               "compiler": measure(ROOT / "translate.py"),
               "canonical_proofs_compiled": len(positives),
               "candidate_cases": len(cases), "process_executions": len(results),
               "failures": failures, "compilation": compilation,
               "limitations": ["Finite regressions are not the soundness proof.",
                               "The compiler's contract is canonical certificates, not all raw aliases.",
                               "Sorted public grammar includes padding aliases; completeness is canonical."],
               "results": results}
    (ROOT / "cases.json").write_text(json.dumps({"cases": [
        {"name": n, "certificate": d, "expected": e} for n, d, e in cases]}, indent=1) + "\n")
    (ROOT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: value for key, value in receipt.items()
                      if key not in ("results", "compilation")}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
