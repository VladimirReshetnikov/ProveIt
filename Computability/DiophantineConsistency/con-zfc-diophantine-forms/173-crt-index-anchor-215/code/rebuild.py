#!/usr/bin/env python3
"""Rebuild every released coefficient list from the pinned 225-variable source.

Usage, from the unpacked release:
    python3 -B code/rebuild.py --output-dir /path/to/an/empty/directory

No optimization or projection search is performed. The source producer is
rerun; the radical/affine and coordinate/row certificates are then replayed.
Frozen optimization-stage files supply descriptive metadata only. Their
residual and expanded coefficient lists are regenerated and compared.

This is the producer/replay path. The separate audit scripts are the
independent verification path. Python 3.10+ and its standard library suffice.
"""
from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import importlib
import io
import json
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def serialize_like(value, reference):
    """Regenerate bytes in either of the two JSON layouts used by the release."""
    compact = canonical(value)
    if compact == reference:
        return compact
    pretty = (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()
    if pretty == reference:
        return pretty
    # Coefficient equality is still checked separately if metadata/layout differs.
    return compact


def main(package_root, output_dir):
    root = package_root.resolve()
    out = output_dir.resolve()
    require((root / "OPTIMIZATION_CHAIN.json").is_file(), "Package root has no OPTIMIZATION_CHAIN.json")
    require(out != root and out not in root.parents, "Output must not overwrite the release or an ancestor")
    require(not out.exists() or (out.is_dir() and not any(out.iterdir())),
            "Use a new or empty output directory")
    out.mkdir(parents=True, exist_ok=True)

    code = root / "code"
    sys.path.insert(0, str(code))
    anchor = importlib.import_module("build_anchor")
    projection = importlib.import_module("audit_projection")
    optimization = importlib.import_module("audit_optimizations")
    anchor.ROOT = root

    def source_path(relative):
        path = (root / relative).resolve()
        require(path == root or root in path.parents, "Package reference escapes the release")
        return path

    receipt = {
        "status": "PASS",
        "method": "fresh source producer; exact radical, affine, row, and coordinate certificate replay",
        "parent225_sha256": digest((root / "source/parent225/equation.json").read_bytes()),
        "stages": [], "profiles": [],
        "coefficient_policy": "Every residual and expansion is regenerated. Frozen later-stage files supply noncoefficient metadata only.",
        "limits": "Finite reconstruction and identities; not a new proof-assistant proof or a consistency decision.",
    }
    rebuilt = {}

    def serialized_rows(rows):
        return [[[co, list(mon)] for mon, co in sorted(row.items())] for row in rows]

    def with_generated_rows(metadata, rows):
        """Copy only descriptive fields, replacing every coefficient list."""
        require(len(metadata["residuals"]) == len(rows), "Residual count changed")
        result = {key: copy.deepcopy(value) for key, value in metadata.items() if key != "residuals"}
        result["residuals"] = []
        for old_row, terms in zip(metadata["residuals"], serialized_rows(rows)):
            new_row = {key: copy.deepcopy(value) for key, value in old_row.items() if key != "terms"}
            new_row["terms"] = terms
            result["residuals"].append(new_row)
        return result

    def record(relative_directory, generated, operation, metadata_supplied=False):
        """Compare, serialize, and expand one freshly computed residual system."""
        reference_dir = source_path(relative_directory)
        reference_raw = (reference_dir / "equation.json").read_bytes()
        reference = json.loads(reference_raw)
        n = len(generated["variables"])
        require(n == len(reference["variables"]), f"Dimension mismatch: {relative_directory}")
        generated_rows = [optimization.sparse(row["terms"], n) for row in generated["residuals"]]
        reference_rows = [optimization.sparse(row["terms"], n) for row in reference["residuals"]]
        require(generated_rows == reference_rows, f"Residual coefficient mismatch: {relative_directory}")
        require(generated.get("domain") == reference.get("domain") == "unrestricted integers",
                f"Domain mismatch: {relative_directory}")
        measure, expansion = optimization.metrics(generated, generated_rows)

        expanded_path = reference_dir / "expanded_polynomial.json"
        require(expanded_path.is_file(), f"Missing comparison expansion: {relative_directory}")
        expanded_raw = expanded_path.read_bytes()
        expanded_reference = json.loads(expanded_raw)
        if "variables" in expanded_reference:
            require(expanded_reference["variables"] == n, "Expansion dimension mismatch")
        require(optimization.sparse(expanded_reference["terms"], n, degree=4) == expansion,
                f"Expanded coefficient mismatch: {relative_directory}")
        expanded_generated = {key: copy.deepcopy(value) for key, value in expanded_reference.items() if key != "terms"}
        expanded_generated["terms"] = [[co, list(mon)] for mon, co in sorted(expansion.items())]

        target_dir = out / relative_directory
        target_dir.mkdir(parents=True, exist_ok=True)
        equation_bytes = serialize_like(generated, reference_raw)
        expansion_bytes = serialize_like(expanded_generated, expanded_raw)
        (target_dir / "equation.json").write_bytes(equation_bytes)
        (target_dir / "expanded_polynomial.json").write_bytes(expansion_bytes)
        (target_dir / "metrics.json").write_bytes(canonical(measure))
        stage = {
            "directory": relative_directory, "operation": operation,
            "residual_coefficients_equal": True, "expanded_coefficients_equal": True,
            "equation_byte_identical": equation_bytes == reference_raw,
            "expansion_byte_identical": expansion_bytes == expanded_raw,
            "equation_sha256": digest(equation_bytes), "metrics": measure,
            "noncoefficient_metadata_from_frozen_stage": metadata_supplied,
        }
        receipt["stages"].append(stage)
        rebuilt[relative_directory + "/equation.json"] = generated
        return generated

    # These flags are fixed arithmetic constructions, not a search for a zero.
    for count, explicit, quartic in [(219, False, False), (220, True, False), (221, True, True)]:
        relative = f"source/anchor{count}"
        target = out / relative
        captured = io.StringIO()
        with contextlib.redirect_stdout(captured):
            anchor.build(target, explicit_index=explicit, quartic_index=quartic)
        generated = load(target / "equation.json")
        # The complete source producer is deterministic, including its source delta.
        for filename in ("uncontracted.json", "certificate.json"):
            require(load(target / filename) == load(root / relative / filename),
                    f"Source reconstruction mismatch: {relative}/{filename}")
        record(relative, generated, "fresh arithmetic source producer")

    routes = {
        "P215": (221, "stages/projection216", "stages/affine215"),
        "P213": (219, "stages/projection214_affine", "stages/affine213"),
        "P214": (220, "stages/projection215_explicit", "stages/affine214"),
    }
    manifest = load(root / "OPTIMIZATION_CHAIN.json")
    require({p["name"] for p in manifest["profiles"]} == set(routes), "Unexpected profile set")
    require(len(manifest["profiles"]) == len(routes), "Duplicate profiles")

    for profile in manifest["profiles"]:
        name = profile["name"]
        count, radical_dir, affine_dir = routes[name]
        current = rebuilt[f"source/anchor{count}/equation.json"]
        cert = load(source_path(radical_dir) / "projection_certificate.json")
        require(cert.get("schema") == "common_hessian_radical_projection_v1", "Unknown radical certificate")
        for step in cert["steps"]:
            current = projection.one_step(current, step, numerical_controls=False)
        current = record(radical_dir, current, f"{len(cert['steps'])} radical projection certificates")

        affine_cert = load(source_path(affine_dir) / "projection_certificate.json")
        require(digest(canonical(current)) == affine_cert["input_sha256"], "Affine projection source digest")
        current = projection.affine_projection(current, affine_cert)
        current = record(affine_dir, current, "unit affine projection certificate")
        require(receipt["stages"][-1]["equation_sha256"] == affine_cert["output_sha256"],
                "Affine projection target digest")
        require(profile["source"] == affine_dir + "/equation.json", "Manifest projection connection")

        total_ops = 0
        for stage in profile["stages"]:
            n = len(current["variables"])
            rows = [optimization.sparse(row["terms"], n) for row in current["residuals"]]
            require(receipt["stages"][-1]["equation_sha256"] == stage["input_sha256"],
                    "Optimization input digest")
            certificate = load(source_path(stage["certificate"]))
            operations = optimization.get_ops(stage["kind"], certificate, n)
            new_rows = optimization.apply(rows, operations, n)
            # Metadata includes coordinate names and historical labels; no terms are reused.
            metadata = load(source_path(stage["equation"]))
            current = with_generated_rows(metadata, new_rows)
            relative = str(Path(stage["equation"]).parent)
            current = record(relative, current, f"{stage['kind']} certificate replay", metadata_supplied=True)
            require(receipt["stages"][-1]["equation_sha256"] == stage["output_sha256"],
                    "Optimization output digest")
            total_ops += len(operations)

        destination = "equations/principal" if name == "P215" else f"equations/companions/{name.lower()}"
        current = record(destination, current, "public equation export")
        measure, _ = optimization.metrics(current, [optimization.sparse(r["terms"], len(current["variables"])) for r in current["residuals"]])
        receipt["profiles"].append({"name": name, "directory": destination,
            "metrics": measure, "optimization_operations": total_ops,
            "equation_sha256": receipt["stages"][-1]["equation_sha256"]})

    receipt["reconstructed_stage_count"] = len(receipt["stages"])
    receipt["all_residual_coefficients_equal"] = all(x["residual_coefficients_equal"] for x in receipt["stages"])
    receipt["all_expanded_coefficients_equal"] = all(x["expanded_coefficients_equal"] for x in receipt["stages"])
    receipt["all_equations_byte_identical"] = all(x["equation_byte_identical"] for x in receipt["stages"])
    receipt["all_expansions_byte_identical"] = all(x["expansion_byte_identical"] for x in receipt["stages"])
    (out / "REBUILD_RECEIPT.json").write_bytes(canonical(receipt))
    print(json.dumps({key: receipt[key] for key in (
        "status", "reconstructed_stage_count", "all_residual_coefficients_equal",
        "all_expanded_coefficients_equal", "all_equations_byte_identical",
        "all_expansions_byte_identical", "profiles")}, indent=2))
    return receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--package-root", type=Path,
                        default=Path(__file__).resolve().parents[1],
                        help="defaults to the parent of the installed code directory")
    args = parser.parse_args()
    main(args.package_root, args.output_dir)
