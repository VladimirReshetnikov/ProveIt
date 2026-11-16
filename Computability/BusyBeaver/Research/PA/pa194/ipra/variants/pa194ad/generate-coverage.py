"""Generate kernel-reduced finite source checks for the literal PA194-AD table."""

from pathlib import Path
import sys

out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
sites = 3673
block_size = 64
kernel_size = 16
blocks = [(base, min(base + block_size, sites)) for base in range(0, sites, block_size)]


def choose_block(ranges):
    proof = []
    for index, (end, conclusion) in enumerate(ranges):
        if index == len(ranges) - 1:
            proof.append(f"  exact {conclusion}")
        else:
            proof += [f"  by_cases before{end} : i < {end}", f"  · exact {conclusion}"]
    return proof


imports = []
entire = []
for index, (base, end) in enumerate(blocks):
    name = f"PA194ADCoverage{index:02}"
    imports.append(f"import {name}")
    entire.append((end, f"{name}.checked i (by omega) (by omega)"))
    lines = [
        "import PA194ADCompressedChecks",
        "set_option autoImplicit false",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        f"namespace {name}",
        "open PA194ADCompressedChecks",
        "",
    ]
    part = []
    for start in range(base, end, kernel_size):
        stop = min(start + kernel_size, end)
        lines.append(f"private theorem chunk{start} : blockCheck {start} {stop - start} = true := by decide +kernel")
        part.append((stop, f"block_sound chunk{start} (by omega) (by omega)"))
    lines += [
        "",
        f"theorem checked (i : Nat) (lo : {base} ≤ i) (hi : i < {end}) : checkAt i = true := by",
        *choose_block(part),
        "",
        "#print axioms checked",
        f"end {name}",
    ]
    (out / f"{name}.lean").write_text("\n".join(lines) + "\n")

aggregate = imports + [
    "",
    "set_option autoImplicit false",
    "set_option maxHeartbeats 0",
    "namespace PA194ADCoverage",
    "",
    f"theorem checked (i : Nat) (bound : i < {sites}) : PA194ADCompressedChecks.checkAt i = true := by",
    *choose_block(entire),
    "",
    "#print axioms checked",
    "end PA194ADCoverage",
]
(out / "PA194ADCoverage.lean").write_text("\n".join(aggregate) + "\n")
