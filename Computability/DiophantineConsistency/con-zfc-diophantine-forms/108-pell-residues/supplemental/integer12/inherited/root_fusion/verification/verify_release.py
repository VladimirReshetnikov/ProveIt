#!/usr/bin/env python3
"""Read-only release verification, except an explicitly requested receipt.

Uses only Python's standard library. Exact identities and coefficient checks
are distinguished from finite transcription diagnostics. This script is not
a formal proof of the unbounded inherited native/refutation theorem.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import importlib.util
import json
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))
import build_equations as builder
import check_integrated as independent
import check_crt


def require(condition, message):
    if not condition:
        raise ValueError(message)


def import_path(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_manifest():
    path = ROOT / "MANIFEST.json"
    if not path.exists():
        return {"present": False, "reason": "pre-release run"}
    manifest = json.loads(path.read_text())
    for record in manifest["files"]:
        relative = Path(record["path"])
        require(not relative.is_absolute() and ".." not in relative.parts,
                "unsafe manifest path")
        target = ROOT / relative
        data = target.read_bytes()
        require(len(data) == record["bytes"], "manifest size: " + str(relative))
        require(hashlib.sha256(data).hexdigest() == record["sha256"],
                "manifest digest: " + str(relative))
    return {"present": True, "files_verified": len(manifest["files"])}


def check_source_recipe(base):
    recipe = import_path("source34_recipe",
                         ROOT / "coefficients/recipe/source34_builder.py")
    original, receipt = recipe.construct()
    mapped = {
        "beta": original["beta"], "K0": original["K"],
        "MC": original["MC"], "MF": original["MF_source"],
        "cone_A": 1 << 1113, "cone_B": 1 << 666104,
    }
    require(mapped == base, "original finite recipe versus complete payloads")
    return {"machine_to_all_943_tiles": True,
            "basis_convolution_checks": receipt["basis_convolution_checks"],
            "whole_fixed_tuple": True}


def check_crt_shape(packet):
    nodes = packet["nodes"]
    operations = {"add": 0, "sub": 0, "mul": 0}
    variables = set()
    live = set()
    for index, node in enumerate(nodes):
        if node[0] in operations:
            operations[node[0]] += 1
            require(len(node) == 3 and
                    all(isinstance(i, int) and 0 <= i < index for i in node[1:]),
                    "CRT graph topological order")
        elif node[0] == "variable":
            variables.add(node[1])
        elif node[0] == "coefficient":
            require(node[1] in builder.BASE_PORTS, "CRT coefficient port")
        else:
            require(node[0] == "integer" and isinstance(node[1], int),
                    "CRT integer numeral leaf")
    def visit(index):
        if index in live:
            return
        live.add(index)
        node = nodes[index]
        if node[0] in operations:
            visit(node[1])
            visit(node[2])
    visit(packet["output"])
    require(len(live) == len(nodes), "CRT dead node")
    require(variables == set(packet["variables"]) and len(variables) == 13,
            "CRT variable declarations")
    require(operations == packet["operation_counts"] and
            sum(operations.values()) == packet["operations"],
            "CRT live binary operation count")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Optional path for a JSON receipt; omitted is read-only.")
    args = parser.parse_args()
    started = time.monotonic()
    manifest = check_manifest()
    base, coefficient_receipt = independent.coefficients(ROOT)
    recipe_receipt = check_source_recipe(base)

    packets = [builder.make13(), builder.make13(False), builder.make14(),
               builder.make14(False), builder.make15()]
    if hasattr(builder, "make13crt"):
        packets.insert(0, builder.make13crt())
    expected_names = {p["name"] for p in packets}
    actual_names = {p.stem for p in (ROOT / "equations").glob("norm*.json")}
    require(actual_names == expected_names, "unexpected or missing norm packets")
    literal_results = []
    for packet in packets:
        path = ROOT / "equations" / (packet["name"] + ".json")
        literal = json.loads(path.read_text())
        require(literal == packet, "deterministic DAG reconstruction: " + packet["name"])
        if literal.get("crt_carrier"):
            check_crt_shape(literal)
            result = check_crt.transcription(literal, base)
            result.update(name=literal["name"], variables=13,
                          operations=literal["operations"],
                          exact_topology_liveness_and_counts=True)
            literal_results.append(result)
        else:
            literal_results.append(independent.audit_packet(literal, base))

    identities = independent.local_identities()
    generic = independent.exact_generic_clearing()
    degrees = independent.degree_certificates()
    degrees["norm13_crt"] = check_crt.exact_degree()

    # A meaningful negative control: preserve the graph shape and counts,
    # but corrupt the 64 in an inner three-root norm. Independent semantics
    # must reject the changed polynomial, not merely its file digest.
    corrupt = copy.deepcopy(builder.make13())
    changed = False
    for node in corrupt["nodes"]:
        if node == ["integer", 64]:
            node[1] = 65
            changed = True
            break
    require(changed, "negative-control target missing")
    try:
        independent.audit_packet(corrupt, base)
    except ValueError:
        negative_control = "PASS: the corrupted norm coefficient was rejected"
    else:
        raise ValueError("negative control unexpectedly accepted")

    companion_root = ROOT / "companions/quotient_fusion"
    companion_builder = import_path("build", companion_root / "build.py")
    old_build = sys.modules.get("build")
    sys.modules["build"] = companion_builder
    try:
        companion_check = import_path("quotient_independent",
                                      companion_root / "verify.py")
    finally:
        if old_build is None:
            del sys.modules["build"]
        else:
            sys.modules["build"] = old_build
    companions = []
    for variant, transport in companion_builder.EXPORTED_VARIANTS:
        rebuilt = companion_builder.make(variant, transport)
        path = companion_root / (rebuilt["name"] + ".json")
        literal = json.loads(path.read_text())
        require(literal == rebuilt, "quotient deterministic reconstruction")
        companions.append(companion_check.audit(literal))

    receipt = {
        "status": "PASS",
        "python_optimized": not __debug__,
        "manifest": manifest,
        "complete_coefficient_reconstruction": coefficient_receipt,
        "inherited_finite_recipe_replay": recipe_receipt,
        "exact_local_identities": identities,
        "exact_generic_cleared_norms": generic,
        "exact_degree_certificates": degrees,
        "literal_norm_equations": literal_results,
        "quotient_companions": companions,
        "negative_control": negative_control,
        "scope": (
            "Exact finite arithmetic and circuit certification, plus labelled "
            "finite transcription diagnostics. The ordinary semantic proof is "
            "in the report. The inherited unbounded native/refutation calibration "
            "is an explicit mathematical dependency, not proved by this program."
        ),
        "seconds": round(time.monotonic() - started, 3),
    }
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({
        "status": receipt["status"],
        "python_optimized": receipt["python_optimized"],
        "norm_equations": len(literal_results),
        "quotient_companions": len(companions),
        "manifest": manifest,
        "negative_control": negative_control,
        "seconds": receipt["seconds"],
    }, indent=2))


if __name__ == "__main__":
    main()
