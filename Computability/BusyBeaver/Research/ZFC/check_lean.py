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
        ("SetTheory/BoundedConsistency/Lean", "BoundedZFCConsistency/Basic.lean"),
        ("SetTheory/BoundedConsistency/Lean", "BoundedZFCConsistency/OmegaRecursion.lean"),
        ("SetTheory/BoundedConsistency/Lean", "BoundedZFCConsistency/Choice.lean"),
        *(("SetTheory/BoundedConsistency/Lean", f"BoundedZFCConsistency/{name}.lean")
          for name in ("Coding", "CodePredicate", "FormulaClosedSet", "InternalSat", "InternalSatTotality")),
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
                        "Numeric254", "NamedNumeric254", "BootstrapFrame253", "Code254", "Code254Proof", "OutgoingProfile",
                        "Code254Containers", "ZipperRuns", "RegisterBoxes253", "Code254GIC",
                        "Code254Models", "NumericCode254", "RegisterMark253", "RegisterIncrement253",
                        "Enum254", "Code254ProofCompiler", "Code254History", "QuotientSeparation", "QuotientPower", "QuotientReplacement",
                        "RegisterDecrement253", "QuotientBasic", "SingletonInfinity", "BreakSite253", "FiniteSets", "InductiveAttempts", "QuotientZF0",
                        "RMDag", "Dag254", "L2Lib254", "L2Macros254", "L2Control254", "L2Axioms254", "L2AxiomsEval254", "L2Root254", "RMEquiv", "RMEquiv254", "ProgramZF0", "DecodeFresh254", "NamedForm254",
                        "DuplicateProfiles", "WritingRuns", "ZeroSite253", "EqualityGIC", "QuotientCPGIC", "NativeDecoded254", "NativeTheory254",
                        "EnumSafeStart254", "EnumStackBarrier254", "EnumStackCount254", "DirtyRoot254", "DirtyProgram254", "WellFoundedPart", "SeedInvariant254", "RMBisim", "ActualTree254", "Bisim254", "NamedZF", "InternalOrd", "InternalRank", "ZFRank", "ZFNative", "WFRelativization", "WFModel", "WFTheory", "Endpoint254",
                        "TransRec", "ConstructibleDef", "Constructible", "ConstructibleReflect", "ConstructibleZF", "SatSupport", "ConstructibleAbs", "InternalWO", "OrderRec",
                        "TablePerm252", "BootPerm252", "RegisterBoxesPerm252", "RegisterMarkPerm252",
                        "RegisterIncrementPerm252", "RegisterDecrementPerm252",
                        "Permutation252Frame", "BootstrapFramePerm252", "SymbolicPerm252", "SitePerm252",
                        "RegisterPathClean", "Permutation252Simulation", "InstructionPerm252",
                        "SiteCoverage", "RuntimePerm252", "RuntimeInstancePerm252", "Permutation252Program",
                        "SitesPerm252Checks0", "SitesPerm252Checks1", "SitesPerm252Checks2", "SitesPerm252Checks3",
                        "SitesPerm252Checks4", "SitesPerm252Checks5", "SitesPerm252Checks6", "SitesPerm252Checks7",
                        "SitesPerm252", "BinaryPerm252", "ZFCBoundPerm252") ),
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
