"""Compile the published 219-node program with the public Wade backend.

This reconstructs a usable compiler baseline without Mira-Cult's unavailable
source.py. It DOES NOT reconstruct Mira-Cult's smaller interpreter. The caller
supplies an outside-repository scratch directory. Four pinned MIT-0 backend
files are copied there from the unchanged vendored snapshot; the three Python
modules are executed there. --upstream-clone selects a separate Git clone
instead. The source files in the snapshot are never modified.
The published .v program is parsed only as a finite data table, never executed.

Example:
  uv run --no-project python Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py \
    --scratch /tmp/zfc-wade-route \
    --output-evidence Computability/BusyBeaver/Research/ZFC/wade-route-evidence.json
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
COMMIT = "297ab8df7e5de329605c3875b4934643b371a5e3"
SNAPSHOT = ROOT / "lib/jeff-busy-beaver-zfc254"
SOURCE_SHA256 = {
    "ZF/generator/TMBuilder.py": "03d3a636404e1bcdeceafd98b9478b7a367ab334f3ab9f8a00df1d5c03fdf517",
    "ZF/generator/tm.py": "2d00bf8c8324d8e9bc5639ba14e508091d854a7c93ecb96ab598f41c15ae9787",
    "ZF/generator/tmdb.py": "4ccf4dab37438109a350d77259b5eb52e33ce110a954cd2d56a218e84e653526",
    "ZF/generator/LICENSE.wade": "c1dffee77db98625debe39b47538e1d2f3b7956cbc7bcd6ed9363701b2177cfa",
    "ZF/m254/coq/prog/Dag254.v": "538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3",
}
REGISTERS = ["nextproof", "topwff", "wffstack", "axiomcode", "param1",
             "param2", "scratch1", "scratch2", "prooflist"]


def git_bytes(clone: Path | None, path: str) -> bytes:
    data = ((SNAPSHOT / path).read_bytes() if clone is None else
            subprocess.check_output(["git", "show", f"{COMMIT}:{path}"], cwd=clone))
    if hashlib.sha256(data).hexdigest() != SOURCE_SHA256[path]:
        raise ValueError(f"source differs from the pinned version: {path}")
    return data


def parse_dag(text: str) -> tuple[dict[int, tuple[str, str]], dict[int, str]]:
    pattern = (r"\| ([0-9]+) => \((E\w+(?: [0-9]+)?), (E\w+(?: [0-9]+)?)\)"
               r"\s+\(\* (.*?) \*\)")
    nodes, names = {}, {}
    for match in re.finditer(pattern, text):
        number, left, right, name = match.groups()
        q = int(number)
        if q in nodes:
            raise ValueError("duplicate DAG node")
        nodes[q], names[q] = (left, right), name
    if set(nodes) != set(range(len(nodes))) or not nodes:
        raise ValueError("expected a nonempty consecutively numbered DAG")
    if len(set(names.values())) != len(names) or names[0] != "main().0":
        raise ValueError("unexpected DAG names or root")
    for edges in nodes.values():
        for edge in edges:
            if edge == "EHalt":
                continue
            kind, number = edge.split()
            n = int(number)
            if (kind == "ENode" and n not in nodes or
                    kind in ("EInc", "EDecnz") and n >= len(REGISTERS) or
                    kind not in ("ENode", "EInc", "EDecnz", "EBreak", "EContinue")):
                raise ValueError("unsupported DAG edge")
    return nodes, names


def builder_from_dag(backend, nodes: dict[int, tuple[str, str]], names: dict[int, str]):
    builder = backend.TMBuilder()
    registers = [builder.reg(name) for name in REGISTERS]

    def leaf(edge: str):
        if edge == "EHalt":
            return "halt"
        kind, value = edge.split()
        n = int(value)
        if kind == "ENode":
            return n
        if kind == "EInc":
            return registers[n].inc
        if kind == "EDecnz":
            return registers[n].decnz
        return f"_{'break' if kind == 'EBreak' else 'continue'}.{n}"

    for q in range(len(nodes)):
        sequence = backend.Sequence(tuple(leaf(e) for e in nodes[q]))
        sequence.name = names[q]
        builder.sequences.append(sequence)
    return builder


def compile_dag(backend, nodes: dict[int, tuple[str, str]], names: dict[int, str]):
    builder = builder_from_dag(backend, nodes, names)
    builder.generate()
    builder.tm.gc()
    return builder.tm


def reextract(machine, nodes: dict[int, tuple[str, str]], names: dict[int, str]) -> None:
    """Independently invert emitted decision edges; compare every source edge."""
    byname = {name: q for q, name in names.items()}
    register_ids = {name: i for i, name in enumerate(REGISTERS)}
    for q, edges in nodes.items():
        for bit, expected in enumerate(edges):
            action = machine.states[names[q], str(bit)]
            target = action.nextstate
            if target in byname:
                actual = f"ENode {byname[target]}"
                if action.write != str(bit) or action.direction != "R":
                    raise ValueError("node edge changed tape or direction")
            elif target == "halt":
                actual = "EHalt"
            elif match := re.fullmatch(r"3\.(.*)\.(inc|decnz)", target):
                kind = "EInc" if match[2] == "inc" else "EDecnz"
                actual = f"{kind} {register_ids[match[1]]}"
            elif target.startswith("6.break."):
                actual = f"EBreak {int(target.rsplit('.', 1)[1]) + (bit == 0)}"
            elif target.startswith("6.continue."):
                level = int(target.rsplit(".", 1)[1])
                actual = ("EBreak 0" if bit == 0 and action.write == "1"
                          else f"EContinue {level + bit}")
            else:
                raise ValueError(f"unexpected emitted target {target}")
            if actual != expected:
                raise ValueError(f"node {q}, bit {bit}: {actual} != {expected}")
            direct = expected.split()[0] in ("ENode", "EInc", "EDecnz", "EHalt")
            expected_write = str(bit) if direct else ("1" if expected == "EBreak 0" and bit == 0 else "0")
            if action.write != expected_write or action.direction != ("R" if direct else "L"):
                raise ValueError(f"node {q}, bit {bit}: emitted write/move differs")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-clone", type=Path)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--output-evidence", type=Path)
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    if scratch == ROOT or ROOT in scratch.parents or scratch == Path("/"):
        parser.error("scratch must be outside the repository and not filesystem root")
    scratch.mkdir(parents=True, exist_ok=True)
    backend_blobs = {}
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        path = "ZF/generator/" + name
        data = git_bytes(args.upstream_clone, path)
        (scratch / name).write_bytes(data)
        backend_blobs[path] = hashlib.sha256(data).hexdigest()
    dag_path = "ZF/m254/coq/prog/Dag254.v"
    source = git_bytes(args.upstream_clone, dag_path)
    nodes, names = parse_dag(source.decode())
    sys.path.insert(0, str(scratch))
    backend = importlib.import_module("TMBuilder")
    machine = compile_dag(backend, nodes, names)
    reextract(machine, nodes, names)
    output = scratch / "recovered-dag219.tm"
    machine.save(str(output))
    states = {q for q, _ in machine.states}
    framework = {q for q in states if q[0].isdigit()}
    missing = [[q, bit] for q in sorted(states) for bit in ("0", "1")
               if (q, bit) not in machine.states]
    result = {"upstream_commit": COMMIT, "DAG_source": dag_path,
              "DAG_source_sha256": hashlib.sha256(source).hexdigest(),
              "backend_source_sha256": backend_blobs,
              "DAG_nodes": len(nodes), "registers": REGISTERS,
              "working_states": len(states), "framework_states": len(framework),
              "decision_states": len(states - framework),
              "transition_rows": len(machine.states), "missing_transition_rows": missing,
              "terminal_targets": sorted({a.nextstate for a in machine.states.values()} - states),
              "edge_kinds": dict(Counter(e.split()[0] for es in nodes.values() for e in es)),
              "reextracted_DAG_exact": True, "source_py_required": False,
              "original_254_interpreter_reconstructed": False,
              "Lean_compiler_simulation_proved": False,
              "machine_sha256": hashlib.sha256(output.read_bytes()).hexdigest()}
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output_evidence:
        args.output_evidence.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
