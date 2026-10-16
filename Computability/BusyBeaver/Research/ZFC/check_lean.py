"""Check the ZFC minimization lemmas serially, rebuilding their source closure.

Uses the repository's pinned Lean through elan. Outputs stay in a fresh scratch
directory. No Lake worker pool, shared build cache, or Coq compiler is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--include-no-quotient", action="store_true",
                        help="also kernel-check the larger finite refinement certificate")
    args = parser.parse_args()
    repo = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
    scratch = Path(tempfile.mkdtemp(prefix="zfc-lean-check-"))
    units = [
        ("Logic/FirstOrder/Lean", "FirstOrder/Fol.lean"),
        ("Logic/FirstOrder/Lean", "FirstOrder/Calculus.lean"),
        ("Logic/FirstOrder/Lean", "FirstOrder/Completeness.lean"),
        ("SetTheory/ZF/Lean", "ZF/Zf.lean"),
        ("Computability/BusyBeaver/Lean", "BusyBeaver/Core.lean"),
        *( ("Computability/BusyBeaver/Lean", f"BusyBeaver/ZFC/{name}.lean")
           for name in ("ProfileCongruence", "PositiveClosure", "Bootstrap", "DeepPositiveClosure",
                        "DefinableClosure", "ProfilePairs", "ProfileCollection", "ProfileSyntax",
                        "ProfileModel", "ProfileComposition", "CompositionModel", "QuotientModel",
                        "ProfileAxioms", "PowerSyntax", "PSCSaturation", "RawPSCProfile", "RawPSCModel",
                        "StateReduction", "Table254", "Table252", "Table253", "Table248",
                        "FiniteZipper", "Boot253",
                        "RegisterBisimulation", "FormulaRPN", "Base3Encoding",
                        "Base3Syntax", "Bottom3Syntax", "PartialTotalization", "WadeMachine",
                        "PSCCalibration", "Kalmar", "TarskiCalculus", "TarskiDerived",
                        "TarskiLeibniz", "TarskiClean", "TarskiComplete", "Lukasiewicz",
                        "RegisterPath", "Prog254", "Prefix330", "TarskiFalsity",
                        "Numeric254", "NamedNumeric254", "BootstrapFrame253", "Code254", "OutgoingProfile") ),
        ("Computability/BusyBeaver/Lean", "BusyBeaver/ZFC.lean"),
    ]
    if args.include_no_quotient:
        units.append(("Computability/BusyBeaver/Lean", "BusyBeaver/ZFC/NoQuotient254.lean"))
    env = dict(os.environ, LEAN_PATH=str(scratch))
    version = subprocess.check_output(["lean", "--version"], cwd=repo, text=True).strip()
    print(version, flush=True)
    records = []
    for source_root, module in units:
        output = scratch / Path(module).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(
            ["lean", "-o", str(output), module], cwd=repo / source_root,
            env=env, capture_output=True, text=True,
        )
        log = output.with_suffix(".log")
        log.write_text(result.stdout + result.stderr)
        records.append({"source": f"{source_root}/{module}",
                        "source_sha256": hashlib.sha256((repo / source_root / module).read_bytes()).hexdigest(),
                        "returncode": result.returncode, "log": str(log),
                        "audit_output": result.stdout.strip()})
        print(f"{module}: exit {result.returncode}", flush=True)
        if result.returncode or "sorryAx" in result.stdout or "declaration uses 'sorry'" in result.stdout:
            print(result.stdout + result.stderr, flush=True)
            raise SystemExit(result.returncode or 1)
    (scratch / "verification.json").write_text(
        json.dumps({"lean_version": version, "modules": records}, indent=2) + "\n"
    )
    print(f"All {len(units)} source modules checked. Evidence: {scratch}")


if __name__ == "__main__":
    main()
