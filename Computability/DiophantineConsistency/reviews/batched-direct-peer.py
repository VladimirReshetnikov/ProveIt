#!/usr/bin/env python3
"""Independent archive, whole-quartic, and shared-frame ledger checks.

Imports no delivered module. The universal Pell/CRT review is in the
adjacent Markdown note; finite checks do not replace it.
"""
import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import zipfile


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def whole_quartic(directory, domain):
    eq = json.loads((directory/"equation.json").read_text())
    expanded = json.loads((directory/"expanded_polynomial.json").read_text())
    need(eq["domain"] == expanded["domain"] == domain, "domain")
    n = len(eq["variables"])
    need(len({v["name"] for v in eq["variables"]}) == n, "variable names")
    out = defaultdict(int)
    live = set()
    for row in eq["residuals"]:
        need(len({tuple(m) for c, m in row["terms"]}) == len(row["terms"]), "row uniqueness")
        for c, m in row["terms"]:
            need(type(c) is int and c and len(m) <= 2 and m == sorted(m) and
                 all(type(i) is int and 0 <= i < n for i in m), "literal quadratic term")
            live.update(m)
        for c, m in row["terms"]:
            for d, p in row["terms"]:
                out[tuple(sorted(m+p))] += c*d
    wanted = {m: c for m, c in out.items() if c}
    actual = {tuple(m): c for c, m in expanded["terms"]}
    need(wanted == actual and len(actual) == len(expanded["terms"]), "complete SOS expansion")
    need(live == set(range(n)) and expanded["variables"] == n, "complete coordinate list")
    return dict(variables=n, quadratic_rows=len(eq["residuals"]), degree=max(map(len, actual)),
                monomials=len(actual), height=max(map(abs, actual.values())),
                equation_sha256=sha256((directory/"equation.json").read_bytes()).hexdigest())


def frame_ledger(root):
    trace = json.loads((root/"direct/output/shared_frame/construction_trace.json").read_text())
    frame = trace["shared_frame"]
    calls = [m for m in trace["macro_log"] if m["macro"] == "shared_power"]
    groups = frame["index_groups"]
    need(len(calls) == 28 and len(groups) == 23, "actual finite call/group counts")
    group = {g["tag"]: g for g in groups}
    need(len(group) == 23 and {tuple(g["k"]) for g in groups} ==
         {tuple(c["exponent"]) for c in calls}, "literal exponent grouping")
    for c in calls:
        need(c["exponent"] == group[c["group"]]["k"], "group linkage")
    ports = [c[k] for c in calls for k in ["base", "exponent", "output"]]
    need(all(a[0] == "c" or a[1] < frame["A_slack"][1] for a in ports),
         "semantic power requests must precede the Pell frame")
    frozen = {a[1] for a in ports if a[0] == "v"}
    definitions = {}
    for row in trace["raw_rows"]:
        i = row["gate"]
        if i is not None:
            terms = {tuple(m): c for c, m in row["terms"]}
            need(terms.get((i,)) == 1, "monic arithmetic gate")
            definitions[i] = {m: -c for m, c in terms.items() if m != (i,)}

    def expand_affine(a):
        if a[0] == "c":
            return {(): a[1]}
        if a[1] in frozen:
            return {(a[1],): 1}
        need(a[1] in definitions, "unexpected W dependency")
        result = defaultdict(int)
        for m, c in definitions[a[1]].items():
            need(c >= 0 and len(m) <= 1, "W must be a nonnegative affine sum of ports")
            term = {(): 1} if not m else expand_affine(["v", m[0]])
            for p, d in term.items():
                result[p] += c*d
        return dict(result)

    expected = Counter({(): 1})
    for a in ports:
        expected[() if a[0] == "c" else (a[1],)] += a[1] if a[0] == "c" else 1
    need(expand_affine(frame["W"]) == dict(expected), "W includes all actual base/exponent/output slots")
    offset_atoms = {tuple(c["common_offset"]) for c in trace["congruences"]}
    need(len(offset_atoms) == 1, "one actual congruence offset")
    offsets = {a[1] for a in offset_atoms if a[0] == "v"}
    memo = {}

    def leaves(a):
        if a[0] == "c":
            return set()
        i = a[1]
        if i not in definitions:
            return {i}
        if i not in memo:
            found = set()
            for mon in definitions[i]:
                for j in mon:
                    need(j < i, "triangular request arithmetic")
                    found.update(leaves(["v", j]))
            memo[i] = found
        return memo[i]

    need(not any(leaves(a) & offsets for a in ports), "offset must be chosen after the semantic requests")
    return dict(power_calls=28, literal_exponent_groups=23,
                W_port_terms_with_multiplicity=len(ports), all_outputs_in_W=True,
                frame_absent_from_power_request_inputs=True,
                shared_offset_absent_from_semantic_power_requests=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--directory", type=Path, required=True)
    ap.add_argument("--archive", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    expected = "ff0d3f638d91a905f676f6fe3e40e134979a14880ed34cadf0741604386e8e55"
    need(sha256(args.archive.read_bytes()).hexdigest() == expected, "whole archive digest")
    matched = 0
    with zipfile.ZipFile(args.archive) as z:
        for item in z.infolist():
            if not item.is_dir():
                relative = Path(item.filename).relative_to("con-zfc-batched-certificates")
                need((args.directory/relative).read_bytes() == z.read(item), "archival member identity")
                matched += 1
    results = {}
    for name in ["common_radix", "common_radix_offset", "shared_frame", "compact667", "compact680"]:
        results[name] = whole_quartic(args.directory/"direct/output"/name, "nonnegative integers")
    results["integer1690"] = whole_quartic(args.directory/"integer/signed_output", "unrestricted integers")
    need((args.directory/"integer/source/parent_natural.json").read_bytes() ==
         (args.directory/"direct/output/shared_frame/equation.json").read_bytes(), "coherent integer parent")
    result = dict(status="PASS", optimized=not __debug__, archive_sha256=expected,
                  exact_archive_members=matched, quartics=results,
                  shared_frame_ledger=frame_ledger(args.directory),
                  integer_parent_matches_shared_frame=True,
                  scope="Independent literal algebra/data checks; unbounded ordinary proof reviewed separately. No Lean or new internal-ZFC derivation.")
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
