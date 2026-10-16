#!/usr/bin/env python3
"""Reconstruct and verify the frozen 286-state Mira runtime, without source writes.

The supplied roots may be Git checkouts or finite source snapshots. Exact byte
hashes identify every source file used; no network or Git command is invoked.
The two verified ProveIt modules execute from memory, and upstream files are
read only as finite data. No Coq source or upstream Python generator executes.

Example (run from this directory):
  python3 extract_runtime.py --repo /path/to/ProveIt \
      --upstream /path/to/busy-beaver \
      --output output/independent_runtime_rebuild.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from types import ModuleType

HERE = Path(__file__).resolve().parent
PROVEIT_COMMIT = "4747142d5d15213eb711bdadfa3cc7e769fcb7a7"
UPSTREAM_COMMIT = "297ab8df7e5de329605c3875b4934643b371a5e3"
SOURCE_DIR = "Computability/BusyBeaver/Research/ZFC"
SOURCE_HASHES = {
    f"{SOURCE_DIR}/recover_wade_dag.py":
        "caa4996be46f9201991dba07f81d4673f14e874ac682226c29fce9e0cea851f1",
    f"{SOURCE_DIR}/mira_backend.py":
        "39508fea4786276dd3655737b07f29f827c06fc5653499a24941b1866d690836",
}
DATA_HASHES = {
    "ZF/m254/coq/prog/Dag254.v":
        "538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3",
    "ZF/m254/machine/zfc_254.tm":
        "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb",
}
FROZEN_SHA256 = "5e939b9b89b7d74f40101162ed1eb263c37e558d7366d652db90fac1c26321b9"


def require(condition, message):
    """Checks must remain active even if Python is invoked with -O."""
    if not condition:
        raise ValueError(message)


def verified_bytes(root, pins):
    blobs = {}
    for relative, expected in pins.items():
        data = (root / relative).read_bytes()
        actual = hashlib.sha256(data).hexdigest()
        require(actual == expected,
                f"Pinned source mismatch: {relative}; expected {expected}, got {actual}")
        blobs[relative] = data
    return blobs


def load_verified_module(name, path, source):
    """Use already verified source bytes; do not create import bytecode files."""
    module = ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = ""
    sys.modules[name] = module
    exec(compile(source, str(path), "exec"), module.__dict__)
    return module


def audit(repo, upstream, runtime_path):
    repo, upstream = repo.resolve(), upstream.resolve()
    source = verified_bytes(repo, SOURCE_HASHES)
    data = verified_bytes(upstream, DATA_HASHES)
    frozen_bytes = runtime_path.read_bytes()
    require(hashlib.sha256(frozen_bytes).hexdigest() == FROZEN_SHA256,
            "The supplied frozen runtime differs from runtime_286.json's exact pin")
    frozen = json.loads(frozen_bytes)

    # The assembler imports recover_wade_dag by this precise module name.
    # Restore any caller bindings afterwards, so this function is reusable.
    module_names = ("recover_wade_dag", "_bb5_pinned_mira_backend")
    previous = {name: sys.modules.get(name) for name in module_names}
    old_bytecode_setting = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        recover_path = f"{SOURCE_DIR}/recover_wade_dag.py"
        recover = load_verified_module(module_names[0], repo / recover_path,
                                       source[recover_path])
        require(recover.COMMIT == UPSTREAM_COMMIT, "Unexpected upstream source pin")
        recover.SNAPSHOT = upstream  # An in-memory input path; no source edits.
        assembler_path = f"{SOURCE_DIR}/mira_backend.py"
        assembler = load_verified_module(module_names[1], repo / assembler_path,
                                         source[assembler_path])
        require(assembler.LITERAL_SHA256 == DATA_HASHES[assembler.LITERAL_PATH],
                "Assembler literal pin differs from independent pin")
        nodes, names = recover.parse_dag(data[assembler.DAG_PATH].decode("utf-8"))
        machine = assembler.compile_dag(nodes, names)

        inverse = {number: name for name, number in machine.labels.items()}
        require(len(inverse) == len(machine.labels), "Assembler labels are not injective")
        runtime_names = {name for name in machine.labels
                         if name != "halt" and not name.startswith("i:")}
        initializer_names = {name for name in machine.labels if name.startswith("i:")}
        named_rows = {}
        for name in runtime_names:
            for bit in (0, 1):
                write, direction, target = machine.table[machine.labels[name], bit]
                target_name = inverse[target]
                require(target_name == "halt" or target_name in runtime_names,
                        "Extracted runtime returns into the discarded initializer")
                named_rows[name, bit] = (write, direction, target_name)

        expected_rows = {}
        for name, bit, write, direction, target in frozen["rows"]:
            require((name, bit) not in expected_rows, "Duplicate frozen runtime row")
            expected_rows[name, bit] = (write, direction, target)
        require(set(named_rows) == set(expected_rows), "Runtime source/read key sets differ")
        for key, actual in sorted(named_rows.items()):
            require(actual == expected_rows[key],
                    f"Runtime row differs at {key!r}: {actual!r} != {expected_rows[key]!r}")

        require(machine.halt == 408 and len(machine.table) == 816,
                "The pinned default assembler no longer reproduces the 408-state control")
        require(len(initializer_names) == 122 and len(runtime_names) == 286,
                "Unexpected initializer/runtime state partition")
        require(len(named_rows) == 572 and machine.gap == 102,
                "Unexpected runtime row count or default gap")
        require(machine.initial_registers == (0,) * 9, "Initial register vector changed")
        require(machine.labels["d:0"] == machine.root, "Runtime entry changed")
        expected_metadata = {
            "proveit_commit": PROVEIT_COMMIT,
            "upstream_commit": UPSTREAM_COMMIT,
            "runtime_states": 286,
            "entry": "d:0",
            "minimum_gap": 102,
            "physical_register_order": list(assembler.PHYS_ORDER),
            "registers": [0] * 9,
            "source_file": assembler_path,
            "source_sha256": SOURCE_HASHES[assembler_path],
        }
        for key, expected in expected_metadata.items():
            require(frozen[key] == expected, f"Frozen runtime metadata differs: {key}")

        return {
            "status": "PASS",
            "proveit_commit": PROVEIT_COMMIT,
            "upstream_commit": UPSTREAM_COMMIT,
            "provenance_method": "Exact SHA-256 pins for every executed source and input data file",
            "source_sha256": SOURCE_HASHES,
            "upstream_data_sha256": DATA_HASHES,
            "current_source_sha256": SOURCE_HASHES[assembler_path],
            "input_DAG_sha256": DATA_HASHES[assembler.DAG_PATH],
            "frozen_runtime_sha256": FROZEN_SHA256,
            "recompiled_original_total_states": machine.halt,
            "recompiled_original_rows": len(machine.table),
            "initializer_states": len(initializer_names),
            "exact_frozen_runtime_rows_matched": len(named_rows),
            "baseline_gap": machine.gap,
            "runtime_states": len(runtime_names),
            "runtime_entry": "d:0",
            "runtime_metadata_matched": True,
            "source_file_writes_performed": False,
            "upstream_programs_executed": False,
            "proof_scope": "Exact reconstruction and row comparison; no arbitrary-runtime or Con(ZFC) theorem",
        }
    finally:
        sys.dont_write_bytecode = old_bytecode_setting
        for name, module in previous.items():
            if module is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True,
                        help="ProveIt checkout or snapshot containing the two pinned Python files")
    parser.add_argument("--upstream", type=Path, required=True,
                        help="busy-beaver checkout or snapshot root containing ZF/m254/")
    parser.add_argument("--runtime", type=Path, default=HERE / "runtime_286.json")
    parser.add_argument("--output", type=Path,
                        help="Optional JSON evidence path; source roots are protected from writes")
    args = parser.parse_args()
    if args.output is not None:
        output = args.output.resolve()
        for source_root in (args.repo.resolve(), args.upstream.resolve()):
            if output == source_root or source_root in output.parents:
                parser.error("--output must be outside both supplied source roots")
        if output == args.runtime.resolve():
            parser.error("--output cannot overwrite the frozen runtime")
    result = audit(args.repo, args.upstream, args.runtime)
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
