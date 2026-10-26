#!/usr/bin/env python3
"""Static circuit-schema census; does not parse, compile, or certify Lean.

Inputs are the immutable pinned source files; outputs are local research artifacts.
The constructor grammar is deliberately restricted to these generated node lists.
"""
import argparse
import csv
import hashlib
import json
import re
from pathlib import Path


def declaration_span(text, name):
    pat = re.compile(r"^(?:private )?(?:def|theorem|abbrev) " + re.escape(name) + r"\b", re.M)
    found = pat.search(text)
    assert found, name
    end = re.search(r"^(?:private )?(?:def|theorem|abbrev|end)\b", text[found.end():], re.M)
    stop = found.end() + end.start() if end else len(text)
    return found.start(), stop, text[found.start():stop]


def node_list(text, name="naturalNodes"):
    _, _, block = declaration_span(text, name)
    nodes = []
    for line in block.splitlines():
        m = re.match(r"\s*\[?\.(input|constant)\s+⟨(\d+),by decide⟩", line)
        if m:
            nodes.append((m[1], int(m[2])))
            continue
        m = re.match(r"\s*\[?\.literal\s+\((-?\d+)\)", line)
        if m:
            nodes.append(("literal", int(m[1])))
            continue
        m = re.match(r"\s*\[?\.(add|sub|mul)\s+(\d+)\s+(\d+)", line)
        if m:
            nodes.append((m[1], int(m[2]), int(m[3])))
    expected = re.search(r"theorem natural_length\s*:\s*naturalNodes.length\s*=\s*(\d+)", text)
    assert expected, "length theorem grammar changed"
    assert len(nodes) == int(expected[1]), (len(nodes), expected[1])
    return nodes


def check_certificate(nodes, labels, base, inputs, fixed):
    assert len(labels) == len(nodes), "length"
    assert labels[base] == 1, "base"
    for i, node in enumerate(nodes):
        if node[0] == "input":
            assert 0 <= node[1] < inputs, ("input", i, node)
        if node[0] == "constant":
            assert 0 <= node[1] < fixed, ("constant", i, node)
        if node[0] in ("add", "sub", "mul"):
            assert 0 <= node[1] < i and 0 <= node[2] < i, ("topology", i, node)
        if labels[i] and i != base:
            assert node[0] == "mul", ("power kind", i, node)
            a, b = node[1:]
            assert labels[a] and labels[b] and labels[i] == labels[a] + labels[b], ("power transition", i, node)


def negative_tests(nodes, labels, base, fixed):
    bad_labels = labels.copy()
    power_index = next(i for i, value in enumerate(labels) if value and i != base)
    bad_labels[power_index] += 1
    forward_nodes = nodes.copy()
    op_index = next(i for i, n in enumerate(nodes) if n[0] in ("add", "sub", "mul"))
    node = nodes[op_index]
    forward_nodes[op_index] = (node[0], op_index + 1, node[2])
    results = []
    for name, ns, ls in (("mutated positive exponent", nodes, bad_labels), ("forward/non-earlier edge", forward_nodes, labels)):
        try:
            check_certificate(ns, ls, base, 9, fixed)
        except AssertionError as exc:
            results.append({"mutation": name, "result": "rejected", "reason": str(exc)})
        else:
            raise AssertionError("negative test incorrectly accepted " + name)
    return results


def census(source, out):
    modules = source / "Computability/DiophantineConsistency/Lean/DiophantineConsistency"
    results = []
    for family, fixed in (("Split", 12), ("Gap", 11)):
        report = "59" if family == "Split" else "66"
        name = family + "CircuitSteps" + report
        circuit = family + "Circuit" + report
        path = modules / (name + ".lean")
        text = path.read_text()
        nodes = node_list((modules / (circuit + ".lean")).read_text())
        labels = [0] * len(nodes)
        powers = []
        for match in re.finditer(r"^theorem (natural_power_(\d+))\b.*?naturalRegister p x (\d+) = naturalRegister p x (\d+) \^ (\d+)", text, re.M | re.S):
            name_, node_, node, base, exponent = match.groups()
            assert node_ == node
            node, base, exponent = map(int, (node, base, exponent))
            labels[base] = 1
            labels[node] = exponent
            powers.append({"name": name_, "node": node, "base": base, "exponent": exponent})
        bases = {p["base"] for p in powers}
        assert len(bases) == 1
        base = bases.pop()
        check_certificate(nodes, labels, base, 9, fixed)
        steps = re.findall(r"^theorem (natural_step_\d+)\b", text, re.M)
        step_spans = [declaration_span(text, n) for n in steps]
        power_spans = [declaration_span(text, p["name"]) for p in powers]
        spans_stat = lambda spans: {
            "declarations": len(spans),
            "span_lines_including_blank_lines": sum(s[2].count("\n") for s in spans),
            "span_utf8_bytes_including_blank_lines": sum(len(s[2].encode()) for s in spans),
            "first_line": text.count("\n", 0, spans[0][0]) + 1,
            "last_line": text.count("\n", 0, spans[-1][1]),
        }
        all_sources = sorted(modules.glob("*.lean"))
        direct_consumers = [p.name for p in all_sources if p != path and f"import DiophantineConsistency.{name}" in p.read_text()]
        result = {
            "module": name, "circuit_module": circuit,
            "path": str(path.relative_to(source)),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "lines": text.count("\n"), "utf8_bytes": len(path.read_bytes()),
            "step_wrappers": spans_stat(step_spans), "power_lemmas": spans_stat(power_spans),
            "node_count": len(nodes), "power_base": base,
            "nonzero_power_labels": sum(bool(x) for x in labels),
            "topology_static_check": "passed", "power_label_static_check": "passed",
            "negative_tests": negative_tests(nodes, labels, base, fixed),
            "direct_importers": direct_consumers,
            "verification_limit": "Python data-shape/arithmetic checks only; Lean not run",
        }
        results.append(result)
        if family == "Split":
            existing = (modules / "SplitJointPower59.lean").read_text()
            match = re.search(r"def natural_oldLabelsData : List ℕ := \[([^\]]+)\]", existing)
            assert match, "existing Split label table grammar changed"
            old_labels = list(map(int, match[1].split(",")))
            assert labels == old_labels, "Split existing label table mismatch"
            result["matches_existing_SplitJointPower59_natural_oldLabelsData"] = True
        (out / (family.lower() + "_power_labels.json")).write_text(json.dumps({"module": name, "base": base, "labels": labels, "powers": powers}, indent=2) + "\n")
        render_candidate(out, family, report, fixed, len(nodes), base, labels, powers)
        result["api_preserving_candidate"] = render_compatible_candidate(out, text, family, report, fixed, len(nodes), base, labels, powers)
    (out / "circuit_census.json").write_text(json.dumps(results, indent=2) + "\n")
    with (out / "circuit_census.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["module", "lines", "utf8_bytes", "step_wrappers", "step_span_lines", "power_lemmas", "power_span_lines", "natural_nodes", "power_base"])
        for r in results:
            w.writerow([r["module"], r["lines"], r["utf8_bytes"], r["step_wrappers"]["declarations"], r["step_wrappers"]["span_lines_including_blank_lines"], r["power_lemmas"]["declarations"], r["power_lemmas"]["span_lines_including_blank_lines"], r["node_count"], r["power_base"]])
    print(json.dumps(results, indent=2))


def render_candidate(out, family, report, fixed, length, base, labels, powers):
    ns = family + "CircuitCandidate" + report
    circuit = family + "Circuit" + report
    data = ",\n    ".join(",".join(map(str, labels[i:i+16])) for i in range(0, len(labels), 16))
    last = powers[-1]
    text = f'''import DiophantineConsistency.ArithmeticDAGPowers
import DiophantineConsistency.{circuit}

/-!
UNCOMPILED RESEARCH CANDIDATE, not a checked replacement or project patch.
Pinned input: 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
Label values are extracted from the existing natural_power_* statements.
Python checked topology and each positive exponent transition independently.
The finite Lean certificate and all declarations below still require compilation.
The literal DAG is imported unchanged; no operation-count reduction is claimed.
-/
namespace DiophantineConsistency.{ns}
open ArithmeticDAG
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
variable {{R : Type*}} [CommRing R]

def naturalRegister (p : Fin {fixed} → R) (x : Fin 9 → R) (i : ℕ) : R :=
  (run p x {circuit}.naturalNodes []).getD i 0

/-- One indexed equation replaces a family of statement wrappers. -/
theorem natural_step (p : Fin {fixed} → R) (x : Fin 9 → R) (i : Fin {length}) :
    naturalRegister p x i.val =
      ({circuit}.naturalNodes.getD i.val (.literal 0)).evalAt p x
        (naturalRegister p x) :=
  run_node_equation p x {circuit}.naturalNodes {circuit}.natural_topological i.val
    (by simpa only [{circuit}.natural_length] using i.isLt)

def powerLabels : List ℕ :=
  [{data}]

def powerLabel (i : ℕ) : ℕ := powerLabels.getD i 0

/-- This is the only new closed proof obligation for all power instances. -/
private theorem power_steps : ∀ i : Fin {length},
    i.val ≠ {base} → powerLabel i.val ≠ 0 →
      PowerStep {circuit}.naturalNodes powerLabel i.val := by
  decide +kernel

theorem natural_power (p : Fin {fixed} → R) (x : Fin 9 → R)
    (i : Fin {length}) (hi : powerLabel i.val ≠ 0) :
    naturalRegister p x i.val = naturalRegister p x {base} ^ powerLabel i.val := by
  apply run_power p x {circuit}.naturalNodes {circuit}.natural_topological
    powerLabel {base} (by decide +kernel)
  · intro j hj
    exact power_steps ⟨j, by simpa only [{circuit}.natural_length] using hj⟩
  · simpa only [{circuit}.natural_length] using i.isLt
  · exact hi

/-- Compatibility smoke test for a concrete gate; not yet compiled. -/
example (p : Fin {fixed} → R) (x : Fin 9 → R) :
    naturalRegister p x 0 = x 0 :=
  natural_step p x ⟨0, by decide⟩

/-- Compatibility smoke test for the last original power lemma. -/
example (p : Fin {fixed} → R) (x : Fin 9 → R) :
    naturalRegister p x {last['node']} = naturalRegister p x {base} ^ {last['exponent']} :=
  natural_power p x ⟨{last['node']}, by decide⟩ (by decide +kernel)

#print axioms DiophantineConsistency.{ns}.natural_step
#print axioms DiophantineConsistency.{ns}.natural_power
end DiophantineConsistency.{ns}
'''
    (out / (ns + ".lean")).write_text(text)


def render_compatible_candidate(out, original, family, report, fixed, length, base, labels, powers):
    """Keep all public theorem headers and gate wrappers, replace power proofs only."""
    circuit = family + "Circuit" + report
    start, _, _ = declaration_span(original, powers[0]["name"])
    prefix = original[:start].replace(
        "import DiophantineConsistency.ArithmeticDAGSemantics",
        "import DiophantineConsistency.ArithmeticDAGPowers", 1)
    warning = "/- UNCOMPILED CANDIDATE: API-preserving power-proof refactor, not a verified replacement. -/\n"
    data = ",\n    ".join(",".join(map(str, labels[i:i+16])) for i in range(0, len(labels), 16))
    shared = f'''private def naturalPowerLabelsData : List ℕ :=
  [{data}]

private def naturalPowerLabel (i : ℕ) : ℕ := naturalPowerLabelsData.getD i 0

private theorem naturalPowerSteps : ∀ i : Fin {length},
    i.val ≠ {base} → naturalPowerLabel i.val ≠ 0 →
      PowerStep {circuit}.naturalNodes naturalPowerLabel i.val := by
  decide +kernel

private theorem natural_power_all (p : Fin {fixed} → R) (x : Fin 9 → R)
    (i : Fin {length}) (hi : naturalPowerLabel i.val ≠ 0) :
    naturalRegister p x i.val = naturalRegister p x {base} ^ naturalPowerLabel i.val := by
  apply run_power p x {circuit}.naturalNodes {circuit}.natural_topological
    naturalPowerLabel {base} (by decide +kernel)
  · intro j hj
    exact naturalPowerSteps ⟨j, by simpa only [{circuit}.natural_length] using hj⟩
  · simpa only [{circuit}.natural_length] using i.isLt
  · exact hi

'''
    replacements = []
    for p in powers:
        _, _, old = declaration_span(original, p["name"])
        header = old.split(" :=", 1)[0]
        replacements.append(header + f' :=\n  natural_power_all p x ⟨{p["node"]}, by decide⟩ (by decide +kernel)\n\n')
    namespace = f"DiophantineConsistency.{family}CircuitSteps{report}"
    audit = f"#print axioms {namespace}.natural_step_0\n#print axioms {namespace}.{powers[-1]['name']}\n"
    text = warning + prefix + shared + "".join(replacements) + audit + f"end {namespace}\n"
    folder = out / "api_preserving_candidates" / "DiophantineConsistency"
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / f"{family}CircuitSteps{report}.lean"
    path.write_text(text)
    original_headers = re.findall(r"^(theorem natural_(?:step|power)_\d+\b.*?)(?= :=)", original, re.M | re.S)
    candidate_headers = re.findall(r"^(theorem natural_(?:step|power)_\d+\b.*?)(?= :=)", text, re.M | re.S)
    assert original_headers == candidate_headers, "public statement text changed"
    return {"path": str(path.relative_to(out)), "lines": text.count("\n"), "utf8_bytes": len(text.encode()), "public_statement_text_unchanged": True, "removed_ring_calls": len(powers), "compilation": "not run"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parent.parent / "sources")
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    census(args.source, args.out)
