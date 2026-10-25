#!/usr/bin/env python3
"""Independent finite certificate replay for the signed-front quartics.

The verifier does not import build.py or a producer/eliminator. Its algebra
helper is the retained, independent checker from the parent distribution.
The unbounded semantic step is proved in PROOF.md, not by finite testing.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
BASE = ROOT / "upstream_common"
spec = importlib.util.spec_from_file_location(
    "independent_algebra", BASE / "code/inherited_independent_algebra.py")
IA = importlib.util.module_from_spec(spec)
spec.loader.exec_module(IA)
PROFILES = ("integer248", "integer246", "integer245")
FLAGS = ["-B"] + (["-O"] if sys.flags.optimize else [])


def need(condition, message):
    if not condition:
        raise ValueError(message)


def get(path):
    return json.loads(path.read_text())


def file_sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pin_check():
    manifest = get(ROOT / "UPSTREAM_PINS.json")
    actual = sorted(str(p.relative_to(BASE)) for p in BASE.rglob("*")
                    if p.is_file() and "__pycache__" not in p.parts)
    need(actual == sorted(manifest["files"]), "upstream file census")
    for name, digest in manifest["files"].items():
        need(file_sha(BASE / name) == digest, "upstream byte pin: " + name)
    need(manifest["repository_commit"] ==
         "3ecd6a6cf53d47519228328567f45fb7ee9781d9", "snapshot pin")
    return len(actual)


def source_replay(source, certificate):
    """Reconstruct the complete new source without trusting edit locations."""
    old = get(BASE / "data/source.json")
    old_guards = get(BASE / "data/remainder_transformation.json")["new_guards"]
    names = {v["name"]: j for j, v in enumerate(old["variables"])}
    r, s = names["fact0.remainder"], names["fact0.slack"]
    B, q, o = names["choose0.output"], names["pow2.output"], names["choose0.oslack"]
    front = [g for g in old_guards if g["kind"] == "front_nonnegative"]
    need([g["coordinate"] for g in front] == [r, s, o], "front guard interface")
    need(all(IA.norm(g["expression"]) == IA.v(g["coordinate"]) for g in front),
         "old front guard expression")
    remaining = [{k: v for k, v in g.items() if k not in ("row", "auxiliary")}
                 for g in old_guards if g["kind"] != "front_nonnegative"]
    need([g["kind"] for g in remaining] ==
         ["shared_square_cap", "centered_remainder_budget"], "retained guard interface")
    old_bound = [row for row in old["residuals"]
                 if row["label"] == "choose0.digit_bound"]
    need(len(old_bound) == 1, "exact-output bound row census")
    need(IA.norm(old_bound[0]) == IA.add(IA.v(q), IA.sc(IA.v(B), -1),
         IA.sc(IA.v(o), -1), IA.con(-1)), "old exact-output bound identity")

    expected = copy.deepcopy(old)
    expected["residuals"] = [row for row in expected["residuals"]
                             if row["label"] != "choose0.digit_bound"]
    z = len(expected["variables"])
    expected["variables"].append({"name": "bootstrap.odd_square_root",
                                  "kind": "signed_witness"})
    expected["residuals"].append({"label": "bootstrap.odd_square_radix",
        "terms": IA.terms(IA.add(IA.v(q), IA.sc(IA.mul(IA.v(z), IA.v(z)), -4),
                               IA.sc(IA.v(z), -4), IA.con(-1)))})
    fused = IA.add(IA.mul(IA.v(r), IA.v(s)), IA.v(r), IA.v(s))
    guards = [{"kind": "fused_factorial_signs", "expression": IA.terms(fused)}] + remaining
    records = []
    for j, guard in enumerate(guards):
        aux = list(range(len(expected["variables"]), len(expected["variables"]) + 3))
        a, b, c = aux
        expected["variables"].extend({"name": f"bootstrap.guard{j}.{letter}",
                                      "kind": "integer_guard"} for letter in ("a", "b", "c"))
        row_id = len(expected["residuals"])
        poly = IA.add(IA.norm(guard["expression"]),
                      {(a, a): -1, (b, b): -1, (c, c): -1, (c,): -1})
        expected["residuals"].append({"label": f"bootstrap.guard{j}", "terms": IA.terms(poly)})
        records.append(dict(guard, auxiliary=aux, row=row_id))
    expected["variant"] += ":fused_factorial_signs_and_odd_square"
    need(source == expected, "complete signed-front source replay")
    expected_certificate = {
        "schema": "fused_sign_bootstrap_v1",
        "parent_source_sha256": IA.sha(old), "source_sha256": IA.sha(source),
        "original_guard_coordinates": [r, s, o], "fused_front_coordinates": [r, s],
        "radix_coordinate": q, "odd_square_root_coordinate": z,
        "guard_records": records, "removed_row_labels": ["choose0.digit_bound"],
        "proof": "BOOTSTRAP_PROOF.md"}
    need(certificate == expected_certificate, "complete source transformation record")
    return {"variables_before_projection": len(source["variables"]),
            "quadratic_residuals_before_factoring": len(source["residuals"]),
            "retained_guards": 2, "new_guards": 1}


def load_bundle(root):
    source = {name: get(root / "source" / (name + ".json")) for name in
              ("source", "transformation", "factored", "factorization_certificate")}
    profiles = {}
    for profile in PROFILES:
        profiles[profile] = {name: get(root / "equations" / profile / (name + ".json"))
            for name in ("projected", "projection_certificate", "equation",
                         "translation_certificate", "expanded_polynomial", "METRICS")}
    return source, profiles


def audit_profile(factored, data):
    count = IA.projection(factored, data["projected"], data["projection_certificate"])
    shifts = IA.translation(data["projected"], data["equation"], data["translation_certificate"])
    equation = data["equation"]
    need(equation["domain"] == "unrestricted integers", "endpoint domain")
    polynomial, used = IA.literal(equation)
    need(used == set(range(len(equation["variables"]))), "unused endpoint coordinate")
    expanded = data["expanded_polynomial"]
    need(IA.norm(expanded) == polynomial, "complete expanded polynomial")
    need(expanded["variables"] == len(equation["variables"]), "expansion variable census")
    need(expanded["domain"] == equation["domain"], "expansion domain")
    metrics = {"variables": len(equation["variables"]),
               "residuals": len(equation["residuals"]), "degree": IA.deg(polynomial),
               "monomials": len(polynomial), "height": max(map(abs, polynomial.values()))}
    need(metrics == data["METRICS"], "endpoint measured metrics")
    need(metrics["degree"] == 4, "endpoint exact quartic degree")
    return dict(metrics, projection_steps=count, translated_coordinates=shifts,
                equation_sha256=IA.sha(equation),
                expanded_polynomial_sha256=IA.sha(expanded))


def audit(root):
    source, profiles = load_bundle(root)
    result = {"source": source_replay(source["source"], source["transformation"])}
    result["horn_factorization_edits"] = IA.factorization(source["source"],
        source["factored"], source["factorization_certificate"])
    result["profiles"] = {name: audit_profile(source["factored"], data)
                           for name, data in profiles.items()}
    return result


def negative_controls():
    source, profiles = load_bundle(ROOT)
    rejected = []

    def reject(name, callback):
        try:
            callback()
        except (ValueError, KeyError, IndexError, TypeError):
            rejected.append(name)
        else:
            raise ValueError("negative control accepted: " + name)

    for label in ("bootstrap.guard0", "bootstrap.odd_square_radix"):
        altered = copy.deepcopy(source["source"])
        row = next(r for r in altered["residuals"] if r["label"] == label)
        row["terms"][0][0] += 1
        metadata = copy.deepcopy(source["transformation"])
        metadata["source_sha256"] = IA.sha(altered)
        reject(label + " coefficient", lambda: source_replay(altered, metadata))
    data = profiles["integer248"]
    altered = copy.deepcopy(data["projection_certificate"])
    altered["steps"][0]["restoration"][0][0] += 1
    reject("monic restoration coefficient", lambda: IA.projection(
        source["factored"], data["projected"], altered))
    altered = copy.deepcopy(data)
    altered["expanded_polynomial"]["terms"][0][0] += 1
    reject("collected polynomial coefficient", lambda: audit_profile(source["factored"], altered))
    altered = copy.deepcopy(data)
    altered["translation_certificate"]["shifts"][0][1] += 1
    reject("integral coordinate shift", lambda: audit_profile(source["factored"], altered))
    return {"rejected": len(rejected), "controls": rejected}


def run(script, *args):
    result = subprocess.run([sys.executable, *FLAGS, str(script), *map(str, args)],
                            text=True, capture_output=True, cwd=ROOT)
    need(result.returncode == 0, result.stdout + "\n" + result.stderr)
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true", help="rebuild in a temporary directory")
    parser.add_argument("--skip-upstream-audit", action="store_true",
                        help="skip the parent finite checker; byte pins are still mandatory")
    parser.add_argument("--output", type=Path, help="write the verification receipt")
    args = parser.parse_args()
    receipt = {"status": "PASS", "optimized": bool(sys.flags.optimize),
               "upstream_pinned_files": pin_check(), "independent_audit": audit(ROOT),
               "negative_controls": negative_controls(),
               "scope": "Finite literal replay; unbounded semantic proof is PROOF.md."}
    if not args.skip_upstream_audit:
        receipt["parent_audit"] = json.loads(run(BASE / "code/verify.py"))
    if args.rebuild:
        with tempfile.TemporaryDirectory(prefix="signed_front_quartics_") as temp:
            fresh = Path(temp)
            run(ROOT / "build.py", "--output", fresh)
            files = sorted(list((fresh / "source").glob("*.json")) +
                           list((fresh / "equations").glob("*/*.json")))
            need(len(files) == 22, "rebuild file census")
            for path in files:
                relative = path.relative_to(fresh)
                need(path.read_bytes() == (ROOT / relative).read_bytes(),
                     "rebuild byte mismatch: " + str(relative))
            fresh_audit = audit(fresh)
            need(fresh_audit == receipt["independent_audit"], "fresh finite audit mismatch")
            receipt["rebuild"] = {"identical_json_files": len(files), "fresh_audit": "PASS"}
    text = json.dumps(receipt, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
