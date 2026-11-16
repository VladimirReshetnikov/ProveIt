#!/usr/bin/env python3
"""Generate AD numerical startup checkpoints for Lean to verify."""

from hashlib import sha256
from pathlib import Path
import sys

STARTUP_TIME = 58122
CHUNK_SIZE = 4096
SEED = (24, 1, 152919395647067130113387679226998336721518593)
TABLE_PATH = Path(
    "Computability/BusyBeaver/Research/PA/docs/"
    "pa194_conpa_2026-11-13/construction/tables/pa194_AD.tm"
)
TABLE_SHA256 = "27613aa92da79ba2ec6e2e88e0ac909fda218e06495ecc0af27201eac0e26c8f"


def read_rows(table):
    data = table.read_bytes()
    assert sha256(data).hexdigest() == TABLE_SHA256, table
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


def generate_checkpoints(rows, out):
    current = (0, 0, 0)
    chunks = []
    for start in range(0, STARTUP_TIME, CHUNK_SIZE):
        count = min(STARTUP_TIME - start, CHUNK_SIZE)
        index = len(chunks)
        initial = current
        for _ in range(count):
            current = step(rows, current)
        chunks.append(count)
        name = f"chunk{index:02}"
        (out / f"PA194ADStartupChunk{index:02}.lean").write_text(
            f"""import PA194ADStep
set_option maxRecDepth 500000
set_option maxHeartbeats 0
namespace PA194ADStartup
theorem {name} : PA194ADTable.run PA194ADTable.adRows {lean_tuple(initial)} {count} = {lean_tuple(current)} := by decide +kernel
#print axioms {name}
end PA194ADStartup
""",
            encoding="utf-8",
        )
    assert current == SEED
    return chunks


def generate_assembly(chunks, out):
    imports = "".join(f"import PA194ADStartupChunk{i:02}\n" for i in range(len(chunks)))
    time_expr = str(chunks[-1])
    for count in reversed(chunks[:-1]):
        time_expr = f"{count} + ({time_expr})"
    rewrites = ", ".join(f"run_add, chunk{i:02}" for i in range(len(chunks) - 1))
    (out / "PA194ADStartupComplete.lean").write_text(
        imports + f"""set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194ADStartup
open PA194ADTable
theorem run_add (rows : List Action) (c : Conf) (n m : Nat) :
    run rows c (n+m) = run rows (run rows c n) m := by
  induction m with
  | zero => simp only [Nat.add_zero, run]
  | succ m ih =>
    change next rows (run rows c (n+m)) = next rows (run rows (run rows c n) m)
    rw [ih]
theorem startup : run adRows (0,0,0) {STARTUP_TIME} = {lean_tuple(SEED)} := by
  have ht : {STARTUP_TIME} = {time_expr} := by decide
  rw [ht]
  rw [{rewrites}]
  exact chunk{len(chunks) - 1:02}
#print axioms run_add
#print axioms startup
end PA194ADStartup
""",
        encoding="utf-8",
    )


repo, out = map(Path, sys.argv[1:])
out.mkdir(parents=True, exist_ok=True)
chunks = generate_checkpoints(read_rows(repo / TABLE_PATH), out)
generate_assembly(chunks, out)
print("Generated", len(chunks), "chunks ending at", SEED)
