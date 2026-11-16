"""Generate sequential finite checks for all 3,673 instructions of a selector variant."""

from pathlib import Path
import sys


def main():
    checkers = {"PA194P5": "PA194P5Representative", "PA194TDY": "PA194TDYChecks"}
    if len(sys.argv) != 3 or sys.argv[1] not in checkers:
        raise SystemExit("usage: generate-selector-coverage.py {PA194P5,PA194TDY} OUTPUT")
    candidate, destination = sys.argv[1:]
    checker = checkers[candidate]
    out = Path(destination)
    out.mkdir(parents=True, exist_ok=True)
    chunks = [(base, min(base + 64, 3673)) for base in range(0, 3673, 64)]
    modules = []
    for index, (base, end) in enumerate(chunks):
        module = f"{candidate}Coverage{index:02}"
        modules.append(module)
        lines = [
            f"import {checker}",
            "set_option autoImplicit false",
            "set_option maxRecDepth 65536",
            "set_option maxHeartbeats 0",
            f"namespace {module}",
            f"open {checker} PA194SourceContracts",
        ]
        blocks = [(j, min(8, end - j)) for j in range(base, end, 8)]
        for lo, count in blocks:
            lines.append(f"private theorem block{lo} : blockCheck check {lo} {count} = true := by decide +kernel")
        lines.extend([
            "",
            f"theorem checked (i : Nat) (lo : {base} ≤ i) (hi : i < {end}) : check i = true := by",
        ])
        for lo, count in blocks:
            bound = lo + count
            proof = f"exact block_sound block{lo} (by omega) (by omega)"
            if bound < end:
                lines.extend([f"  by_cases h{bound} : i < {bound}", f"  · {proof}"])
            else:
                lines.append(f"  {proof}")
        lines.extend(["#print axioms checked", f"end {module}"])
        (out / f"{module}.lean").write_text("\n".join(lines) + "\n")

    lines = [f"import {candidate}SourceEndpoint"] + [f"import {mod}" for mod in modules]
    lines.extend([
        "set_option autoImplicit false",
        "set_option maxRecDepth 65536",
        f"namespace {candidate}CoverageAll",
        f"theorem checked : {candidate}SourceEndpoint.Covered := by",
        "  intro i hi",
    ])
    for module, (_, end) in zip(modules, chunks):
        proof = f"exact {module}.checked i (by omega) (by omega)"
        if end < 3673:
            lines.extend([f"  by_cases h{end} : i < {end}", f"  · {proof}"])
        else:
            lines.append(f"  {proof}")
    lines.extend(["#print axioms checked", f"end {candidate}CoverageAll"])
    (out / f"{candidate}CoverageAll.lean").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
