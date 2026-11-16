#!/usr/bin/env python3
"""Generate numerical startup checkpoints for Lean to verify."""

from hashlib import sha256
from pathlib import Path
import sys

CHUNK_SIZE = 4096
SEED = (24, 1, 152919395647067130113387679226998336721518593)
variants = {
    "PA194OR": (
        "PA194ORH_research_2026-11-15/machines/PA194OR/machine.tm",
        "379e12957eafc5ecb1ec04868067fe931af913e7bc46e69a36b6067d83c4c79f",
        58170,
    ),
    "PA194LC": (
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC/machine.tm",
        "9cb620ba1b869fb793fd9ba0a99e90dcc85d9a6d62a42f48109743a7fbeda3c8",
        58154,
    ),
    "PA194P5": (
        "pa194p5_research_2026-11-14/machine/pa194p5.tm",
        "cf3a2c2d3ba8e95d5c0ea825c3f279ae529b6591cc1280264b0ba3793e77d026",
        56158,
    ),
    "PA194TDY": (
        "pa194_tdy_2026-11-14/artifacts/pa194_tdy.tm",
        "84bfe1368312c7c71c9e4706de7cb65923310e25f8d472997c9c57c5aedd7934",
        57594,
    ),
    "PA194C32": (
        "pa194_ax11hc4_c32_research_2026-11-15/construction/cycle32/pa194_cycle32.tm",
        "3af42ea9d430e5df22b69e6fc540e3530f87263372580c7c554bae37ba524ac8",
        56250,
    ),
    "PA194LCC": (
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC_C/machine.tm",
        "7de80d804e5994db6008687421b0c5b4e96c9c87097fb293269406e9009a5753",
        58320,
    ),
    "PA1944L": (
        "pa1944l_research_2026-11-14/machine/machine.tm",
        "c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253",
        58320,
    ),
}


def read_rows(table, expected):
    data = table.read_bytes()
    assert sha256(data).hexdigest() == expected, table
    rows = []
    for index, line in enumerate(data.decode("ascii").splitlines()):
        control, bit, write, direction, target = line.split()
        assert int(control) == index // 2 and int(bit) == index % 2
        assert write in ("0", "1") and direction in ("L", "R") and 0 <= int(target) <= 194
        rows.append((int(write), direction == "R", int(target)))
    assert len(rows) == 388
    return rows


def step(rows, configuration):
    control, left, right = configuration
    assert control < 194
    write, moves_right, target = rows[2 * control + right % 2]
    if moves_right:
        return target, 2 * left + write, right // 2
    return target, left // 2, left % 2 + 2 * (write + 2 * (right // 2))


def lean_tuple(values):
    return "(" + ",".join(map(str, values)) + ")"


def generate_checkpoints(variant, time, rows, out):
    current = (0, 0, 0)
    chunks = []
    for start in range(0, time, CHUNK_SIZE):
        count = min(time - start, CHUNK_SIZE)
        index = len(chunks)
        initial = current
        for _ in range(count):
            current = step(rows, current)
        chunks.append(count)
        name = f"chunk{index:02}"
        (out / f"{variant}StartupChunk{index:02}.lean").write_text(
            f"""import {variant}Numerical
set_option maxRecDepth 500000
set_option maxHeartbeats 0
namespace {variant}Startup
theorem {name} : {variant}Numerical.runFrom {lean_tuple(initial)} {count} = {lean_tuple(current)} := by decide +kernel
#print axioms {name}
end {variant}Startup
""",
            encoding="utf-8",
        )
    assert current == SEED
    return chunks


def generate_assembly(variant, time, chunks, out):
    imports = "".join(f"import {variant}StartupChunk{i:02}\n" for i in range(len(chunks)))
    time_expr = str(chunks[-1])
    for count in reversed(chunks[:-1]):
        time_expr = f"{count} + ({time_expr})"
    rewrites = ", ".join(f"run_add, chunk{i:02}" for i in range(len(chunks) - 1))
    (out / f"{variant}StartupComplete.lean").write_text(
        imports + f"""set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {variant}Startup
open {variant}Numerical
theorem startup : runFrom (0,0,0) {time} = {lean_tuple(SEED)} := by
  have ht : {time} = {time_expr} := by decide
  rw [ht]
  rw [{rewrites}]
  exact chunk{len(chunks) - 1:02}
#print axioms run_add
#print axioms startup
end {variant}Startup
""",
        encoding="utf-8",
    )


if len(sys.argv) != 4 or sys.argv[1] not in variants:
    raise SystemExit(f"usage: generate-indexed-startup.py {{{','.join(variants)}}} REPO OUTPUT")
variant = sys.argv[1]
repo, out = map(Path, sys.argv[2:])
relative, digest, time = variants[variant]
table = repo / "Computability/BusyBeaver/Research/PA/docs" / relative
out.mkdir(parents=True, exist_ok=True)
chunks = generate_checkpoints(variant, time, read_rows(table, digest), out)
generate_assembly(variant, time, chunks, out)
print("Generated", len(chunks), "chunks ending at", SEED)
