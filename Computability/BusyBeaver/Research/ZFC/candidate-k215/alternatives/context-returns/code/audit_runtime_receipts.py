#!/usr/bin/env python3
"""Bind complete archived quantified-runtime receipts to the frozen artifacts.

This is an independent receipt/coverage audit, not a replacement for rerunning
validate_native.py. Also emits exact canonical dense tables and the PDF table.
"""
from pathlib import Path
import gzip
import hashlib
import json

import verify_context as v

ROOT = Path(__file__).resolve().parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compressed_json(path):
    return json.loads(gzip.decompress(path.read_bytes()))


def audit(name, native_name, source_name, folder):
    native, source = ROOT / "machine" / native_name, ROOT / "machine" / source_name
    evidence = ROOT / folder
    table, halt = v.read_table(native)
    states = {q for q, _ in table}
    v.require(len(states) == 215 and len(table) == 430 and halt == 254, "native state convention")
    rows = json.loads(source.read_bytes())
    cases = compressed_json(evidence / "runtime_cases.json.gz")
    report = json.loads((evidence / "runtime.json").read_bytes())
    expected = [(i, p) for i, (_, op, _) in enumerate(rows)
                for p in ((False, True) if op == "CD" else (False,))]
    actual = [(c["site_index"], c["positive"]) for c in cases]
    v.require(actual == expected and len(cases) == 6176, "ordered unique case coverage")
    v.require(report["status"] == "UNIVERSAL_MATHEMATICAL_PASS" and report["failures"] == [], "runtime status")
    v.require(report["proved_cases"] == report["expected_cases"] == len(cases), "case count")
    v.require(report["table_sha256"] == digest(native) and report["sites_sha256"] == digest(source), "input pins")
    runtime = ROOT / "code/runtime-inputs/runtime"
    v.require(report["checker_sha256"] == digest(runtime / "symbolic_runtime.py"), "symbolic checker pin")
    v.require(report["helper_sha256"] == digest(runtime / "independent_runtime.py"), "runtime helper pin")
    mapping = {int(k): int(z) for k, z in json.loads((ROOT / "code/runtime-inputs/inputs/legacy_mapping.json").read_text()).items()}
    for q in states | {254}:
        mapping.setdefault(q, q + 1000)
    inverse = {mapping[q]: q for q in states | {254}}
    v.require(len(inverse) == 216, "injective legacy mapping")
    legacy = {(mapping[q], r): (w, d, mapping[z]) for (q, r), (w, d, z) in table.items()}
    used = set()
    total_rules = 0
    for case in cases:
        duration = case["duration"]
        v.require(len(duration) == 13 and all(type(n) is int for n in duration), "affine duration")
        v.require(duration[0] >= 1 and all(n >= 0 for n in duration[1:]), "positive duration for every natural parameter")
        total_rules += case["symbolic_steps"]
        for q, r in case["rows"]:
            v.require((q, r) in legacy, "case row outside the frozen table")
            used.add((inverse[q], r))

    def inspect_trace(value):
        if not isinstance(value, list):
            return
        if len(value) >= 2 and isinstance(value[0], str) and value[0] in ("literal", "unary"):
            row = value[1]
            v.require(isinstance(row, list) and len(row) == 5, "block row format")
            q, r, w, d, z = row
            v.require(legacy[q, r] == (w, d, z), "block row differs from literal table")
            used.add((inverse[q], r))
        for item in value:
            if isinstance(item, list):
                inspect_trace(item)

    v.require(len(report["blocks"]) == 4, "four structural list schemas")
    for block in report["blocks"]:
        v.require(block["arbitrary_contexts"] is True, "block exterior scope")
        inspect_trace(block["trace"])
    v.require(used == set(table), "complete 430-row accounting")
    dense, labels = v.canonical(table, halt)
    dense_path = native.with_name(native.name.replace(".native.tm", ".tm"))
    dense_bytes = v.serialize(dense)
    dense_path.write_bytes(dense_bytes)
    map_path = dense_path.with_suffix(".mapping.json")
    map_path.write_text(json.dumps(labels, indent=2, sort_keys=True) + "\n")
    q, head, ones, _ = v.blank_run(dense, 95740)
    v.require((q, head, ones) == (labels[84], -8, v.expected_frame()), "dense complete blank frame")
    result = {"status": "PASS", "name": name, "native_sha256": digest(native),
              "dense_sha256": digest(dense_path), "source_sha256": digest(source),
              "case_count": len(cases), "symbolic_inference_steps": total_rules,
              "minimum_duration_constant": min(c["duration"][0] for c in cases),
              "all_affine_durations_positive": True, "native_rows_accounted": len(used),
              "all_working_states_graph_reachable": True, "dense_dispatcher": labels[84],
              "dense_halt": labels[254], "dense_blank_steps": 95740,
              "scope": "Receipt binding, case coverage, positive durations, row accounting, dense table identity, and exact finite dense startup. Full symbolic derivations are rerun by validate_native.py."}
    return result, dense


def write_latex(table):
    def action(q, bit):
        w, d, z = table[q, bit]
        return f"\\texttt{{{w}{'R' if d == 1 else 'L'}{z}}}"
    header = "State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1 \\\\\n"
    text = "\\begingroup\\small\n\\begin{longtable}{@{}rll@{\\hspace{1.4em}}rll@{\\hspace{1.4em}}rll@{}}\n\\toprule\n"
    text += header + "\\midrule\n\\endfirsthead\n\\toprule\n" + header + "\\midrule\n\\endhead\n"
    text += "\\midrule\\multicolumn{9}{r}{\\emph{Continued on the next page}}\\\\\n\\endfoot\n\\bottomrule\n\\endlastfoot\n"
    for q in range(72):
        groups = []
        for state in (q, q + 72, q + 144):
            groups.append(f"{state} & {action(state, 0)} & {action(state, 1)}" if state < 215 else " & & ")
        text += " & ".join(groups) + " \\\\\n"
    text += "\\end{longtable}\n\\endgroup\n"
    path = ROOT / "sections/transition_table.tex"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def main():
    result0, _ = audit("history returns", "k215-context.native.tm", "sites215.json", "evidence")
    result1, dense = audit("shallower decoder", "k215-shallow.native.tm", "sites-shallow.json", "evidence/shallow")
    write_latex(dense)
    result = {"status": "PASS", "machines": [result0, result1]}
    (ROOT / "evidence/receipt-audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
