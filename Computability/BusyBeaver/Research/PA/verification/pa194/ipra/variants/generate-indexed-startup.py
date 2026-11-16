#!/usr/bin/env python3
"""Generate numerical startup checkpoints for Lean to verify."""

from hashlib import sha256
from pathlib import Path
import sys

CHUNK_SIZE = 4096
SEED = (24, 1, 152919395647067130113387679226998336721518593)
RESTRICTED_CONTROLS = [107, 123]
variants = {
    "PA194M5": (
        "pa194_radix_family_2026-11-13/machines/5/machine.tm",
        "180a0fd1f046d4cbd687b43979f0605619ad5f53054d32b9f62f33e7a3bccab8",
        58320,
    ),
    "PA194LCB": (
        "pa194_loop_continuation_research_2026-11-14/machines/PA194LC_B/machine.tm",
        "4b2b45e97fdd5f8a6e22c4f552dc3f26252c170e85cdb5ddb27ad5d5c580982a",
        58320,
    ),
    "PA194AX11H": (
        "pa194_ax11h_research_2026-11-14/machine/machine.tm",
        "c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a",
        57922,
    ),
    "PA194LCAX11H": (
        "pa194_loop_continuation_research_2026-11-14/additional/PA194LC_AX11H/machine.tm",
        "5f10f071e7118ff33aba822e05bae0331b4c78508656c3e945c31b0c6788f9c5",
        57922,
    ),
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


def checkpoints(time, rows, excluded=()):
    current = (0, 0, 0)
    chunks = []
    for start in range(0, time, CHUNK_SIZE):
        count = min(time - start, CHUNK_SIZE)
        initial = current
        for _ in range(count):
            assert current[0] not in excluded, (start, current[0])
            current = step(rows, current)
        chunks.append((count, initial, current))
    assert current == SEED
    return chunks


def generate_checkpoints(variant, chunks, out):
    for index, (count, initial, final) in enumerate(chunks):
        name = f"chunk{index:02}"
        (out / f"{variant}StartupChunk{index:02}.lean").write_text(
            f"""import {variant}Numerical
set_option maxRecDepth 500000
set_option maxHeartbeats 0
namespace {variant}Startup
theorem {name} : {variant}Numerical.runFrom {lean_tuple(initial)} {count} = {lean_tuple(final)} := by decide +kernel
#print axioms {name}
end {variant}Startup
""",
            encoding="utf-8",
        )


def time_expression(chunks):
    time_expr = str(chunks[-1][0])
    for count, _, _ in reversed(chunks[:-1]):
        time_expr = f"{count} + ({time_expr})"
    return time_expr


def generate_assembly(variant, time, chunks, out):
    imports = "".join(f"import {variant}StartupChunk{i:02}\n" for i in range(len(chunks)))
    rewrites = ", ".join(f"run_add, chunk{i:02}" for i in range(len(chunks) - 1))
    (out / f"{variant}StartupComplete.lean").write_text(
        imports + f"""set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {variant}Startup
open {variant}Numerical
theorem startup : runFrom (0,0,0) {time} = {lean_tuple(SEED)} := by
  have ht : {time} = {time_expression(chunks)} := by decide
  rw [ht]
  rw [{rewrites}]
  exact chunk{len(chunks) - 1:02}
#print axioms run_add
#print axioms startup
end {variant}Startup
""",
        encoding="utf-8",
    )


def generate_restricted(time, chunks, out):
    excluded = RESTRICTED_CONTROLS
    for index, (count, initial, final) in enumerate(chunks):
        (out / f"PA1944LRestrictedChunk{index:02}.lean").write_text(
            f"""import PA194IndexedRunRestriction
import PA1944LData

set_option maxRecDepth 500000
set_option maxHeartbeats 0

namespace PA1944LRestricted
open PA194IndexedRunRestriction

theorem chunk{index:02} :
    restrictedRun PA1944LData.rows {excluded} {lean_tuple(initial)} {count} = (true, {lean_tuple(final)}) := by
  decide +kernel

#print axioms chunk{index:02}
end PA1944LRestricted
""",
            encoding="utf-8",
        )
    imports = "".join(f"import PA1944LRestrictedChunk{i:02}\n" for i in range(len(chunks)))
    rewrites = "".join(
        f"  rw [append PA1944LData.rows {excluded} {lean_tuple(initial)} {count} _ "
        f"(congrArg Prod.fst chunk{index:02}), chunk{index:02}]\n"
        for index, (count, initial, _) in enumerate(chunks[:-1])
    )
    (out / "PA1944LRestrictedComplete.lean").write_text(
        imports + f"""
set_option autoImplicit false
set_option maxRecDepth 65536

namespace PA1944LRestricted
open PA194IndexedRunRestriction

theorem certificate :
    restrictedRun PA1944LData.rows {excluded} (0, 0, 0) {time} =
      (true, {str(SEED)}) := by
  have count : {time} = {time_expression(chunks)} := by decide
  rw [count]
{rewrites}  exact chunk{len(chunks) - 1:02}

#print axioms certificate
end PA1944LRestricted
""",
        encoding="utf-8",
    )


restricted = len(sys.argv) == 5 and sys.argv[1] == "PA1944L" and sys.argv[4] == "--restricted"
if not restricted and (len(sys.argv) != 4 or sys.argv[1] not in variants):
    raise SystemExit(
        f"usage: generate-indexed-startup.py {{{','.join(variants)}}} REPO OUTPUT\n"
        "   or: generate-indexed-startup.py PA1944L REPO OUTPUT --restricted"
    )
variant = sys.argv[1]
repo, out = map(Path, sys.argv[2:4])
relative, digest, time = variants[variant]
table = repo / "Computability/BusyBeaver/Research/PA/docs" / relative
out.mkdir(parents=True, exist_ok=True)
chunks = checkpoints(time, read_rows(table, digest), RESTRICTED_CONTROLS if restricted else ())
if restricted:
    generate_restricted(time, chunks, out)
else:
    generate_checkpoints(variant, chunks, out)
    generate_assembly(variant, time, chunks, out)
print("Generated", len(chunks), "chunks ending at", SEED)
