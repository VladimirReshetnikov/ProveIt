"""Generate kernel-reduced coverage for each bounded source site."""

from pathlib import Path
import sys

checkers = {
    "PA194AD": "PA194ADCompressedChecks",
    "PA194LC": "PA194LCChecks",
    "PA194LCC": "PA194LCCChecks",
    "PA1944L": "PA1944LChecks",
    "PA194LCA": "PA194LCAChecks",
    "PA194M4R": "PA194M4RChecks",
    "PA194LCB": "PA194LCBChecks",
    "PA194AX11H": "PA194AX11HChecks",
    "PA194LCAX11H": "PA194LCAX11HChecks",
    "PA194M5": "PA194M5Checks",
    "PA194M6": "PA194M6Checks",
}
if len(sys.argv) != 3 or sys.argv[1] not in checkers:
    raise SystemExit(f"usage: generate-linear-coverage.py {{{','.join(checkers)}}} OUTPUT")
candidate, destination = sys.argv[1:]
checker = checkers[candidate]
coverage = f"{candidate}Coverage"
out = Path(destination)
out.mkdir(parents=True, exist_ok=True)
sites = {"PA194AX11H": 3671, "PA194LCAX11H": 3671, "PA194M5": 3734, "PA194M6": 3795}.get(candidate, 3673)
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
    name = f"{coverage}{index:02}"
    imports.append(f"import {name}")
    entire.append((end, f"{name}.checked i (by omega) (by omega)"))
    lines = [
        f"import {checker}",
        "set_option autoImplicit false",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        f"namespace {name}",
        f"open {checker}",
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
    f"namespace {coverage}",
    "",
    f"theorem checked (i : Nat) (bound : i < {sites}) : {checker}.checkAt i = true := by",
    *choose_block(entire),
    "",
    "#print axioms checked",
    f"end {coverage}",
]
(out / f"{coverage}.lean").write_text("\n".join(aggregate) + "\n")
