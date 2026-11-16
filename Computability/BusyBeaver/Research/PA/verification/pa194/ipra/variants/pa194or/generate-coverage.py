"""Generate finite PA194OR check batches and indexed coverage aggregation."""

from pathlib import Path
import sys

out = Path(sys.argv[1])
step = 72
segments = [(0, 224), (291, 3554), (3621, 3673)]
pieces = [
    (start, min(start + step, end))
    for minimum, end in segments
    for start in range(minimum, end, step)
]

def subdivided(module, start, end, size):
    chunks = [(lo, min(lo + size, end)) for lo in range(start, end, size)]
    lemmas = [
        f"private theorem chunk{i} : blockCheck {lo} {hi - lo} = true := by decide +kernel"
        for i, (lo, hi) in enumerate(chunks)
    ]
    proof = [
        "  unfold blockCheck",
        "  apply List.all_eq_true.mpr",
        "  intro j hj",
        "  have hb := List.mem_range.mp hj",
    ]
    for i, (_, hi) in enumerate(chunks):
        line = f"exact block_sound chunk{i} (by omega) (by omega)"
        if i == len(chunks) - 1:
            proof.append(f"  {line}")
        else:
            proof += [f"  by_cases h{i} : j < {hi - start}", f"  · {line}"]
    return (
        f"namespace {module}\nopen PA194ORChecks\n\n"
        + "\n".join(lemmas)
        + f"\n\ntheorem checked : blockCheck {start} {end - start} = true := by\n"
        + "\n".join(proof)
        + f"\n\n#print axioms checked\nend {module}\n"
    )


header = """import PA194ORChecks

set_option maxRecDepth 65536
set_option maxHeartbeats 0

"""
for index, (start, end) in enumerate(pieces):
    module = f"PA194ORCoverage{index:02}"
    if index == 23:
        # Shorter reductions avoid high peak memory in this interval.
        body = subdivided(module, start, end, 18)
    else:
        body = (
            f"theorem {module}.checked : PA194ORChecks.blockCheck {start} {end - start} = true := by\n"
            f"  decide +kernel\n\n#print axioms {module}.checked\n"
        )
    (out / f"{module}.lean").write_text(header + body)

ranges = [
    (a, b, f"PA194ORChecks.block_sound PA194ORCoverage{i:02}.checked (by omega) (by omega)")
    for i, (a, b) in enumerate(pieces)
]
ranges += [
    (224, 291, "PA194ORMovedFirst.allMoved i (by omega) (by omega)"),
    (3554, 3621, "PA194ORMovedSecond.allMoved i (by omega) (by omega)"),
]
ranges.sort()
proof = []
for i, (minimum, end, expression) in enumerate(ranges):
    if i == len(ranges) - 1:
        proof += [f"  exact {expression}"]
    else:
        proof += [f"  by_cases end_{minimum} : i < {end}", f"  · exact {expression}"]

imports = [f"import PA194ORCoverage{i:02}" for i in range(len(pieces))]
imports += ["import PA194ORMovedFirst", "import PA194ORMovedSecond"]
(out / "PA194ORCoverage.lean").write_text(
    "\n".join(imports)
    + """

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem PA194ORCoverage.checked (i : Nat) (bound : i < 3673) :
    PA194ORChecks.checkAt i = true := by
"""
    + "\n".join(proof)
    + "\n\n#print axioms PA194ORCoverage.checked\n"
)
