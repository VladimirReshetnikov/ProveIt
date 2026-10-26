SHORTER, CLEARER LEAN PROOFS: DIOPHANTINECONSISTENCY
Prepared for Vladimir Reshetnikov, 26 October 2026

Read report.pdf for the complete source-grounded analysis and priorities.
report.tex plus validation_summary.tex are the complete editable report source.

REVIEWED SOURCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 60e9c5d620c6c387d932876cfa2d9376f64ea56c
Lean: leanprover/lean4:v4.32.0
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997
The original repository source was not modified. No patch was applied or
published remotely. This archive is a proposal/prototype deliverable.

WHAT IS INCLUDED

report.pdf / report.tex
    Detailed review: priorities; exact source locations; proof-only changes;
    witness layouts; checked-history folds; scanners; residual aggregation;
    existing DAG certificates; native arithmetic; object-model semantics;
    import-layer changes; adoption and validation criteria.

lean/
    Modules selected for successful Lean 4.32.0 replay. The authoritative
    per-file status and scope are in evidence/validation_manifest.json.
    LookupAPI.lean and ValidatedFold.lean use Std only.
    NativeRefactorCore.lean uses the core omega tactic.
    WitnessLayout.lean imports the actual Representation module and includes
    rfl checks of equality with the original constructor expressions.
    SplitPowerCertificate.lean uses the actual SplitCircuit59 module.
    GapExactDataFixture.lean contains a byte-for-byte extracted naturalNodes
    definition and checks only the needed topology, power, and dispatch facts.
    It is not a full rebuild of the original GapCircuit66 module.

proposals/
    Additional production integration candidates. These files are explicitly
    not all replayed as full project modules. Do not treat their presence as
    a claim of compilation. Consult the validation manifest before adoption.
    Compile them individually; the Gap fixture and its production candidate
    intentionally expose some corresponding declaration names.

patches/lookup-api.patch
    Exact proof-only patch: seven list-lookup induction proofs become calls
    to existing Lean library lemmas, saving 40 physical lines across five
    source files. The generic replacement terms compile; git apply --check
    passes. The five entire patched modules have not been replayed here.

evidence/
    Source hashes and inventory; import graph; declaration index; exact
    component metrics; Lean compiler/axiom logs; fixture byte-identity data;
    independent source-review notes; validation limits.

scripts/
    inventory.py: comment-aware, reproducible lexical source measurements.
    replay.py: focused replay of the checked modules, without applying patch.
    check_gap_fixture.py: verify exact fixture/source definition bytes.
    generate_power_certificate.py: regenerate exponent-label certificates.
    generate_gap_fixture.py: regenerate the exact-data Gap validation fixture.

REPLAY

Use a complete ProveIt checkout at the commit above and its pinned Lean.
Install/copy dependencies and the matching Mathlib compiled cache using the
repository's usual setup. The following focused cache command was used:

    lake exe cache get Mathlib.Algebra.MvPolynomial.Eval Mathlib.Tactic

From this archive directory:

    python3 scripts/replay.py /absolute/path/to/ProveIt --core-only
    python3 scripts/replay.py /absolute/path/to/ProveIt

The script refuses a different commit, checks the Lean version, runs patch
applicability, builds only needed parent imports for the selected examples,
and saves new logs under replay-results/. It does not modify packaged evidence
or apply the patch. Use the Python 3 executable name appropriate to your OS.

Reproduce the inventory:

    python3 scripts/inventory.py /absolute/path/to/ProveIt --output new-inventory

Regenerate certificates into a separate temporary directory:

    python3 scripts/generate_power_certificate.py \
      /absolute/path/to/ProveIt/Computability/DiophantineConsistency/Lean/DiophantineConsistency \
      /absolute/path/to/temporary-certificates

The fixture generator also needs CircuitDispatch.lean in that temporary
prototype directory (copy it from proposals/ first). The generated fixture
contains the copied naturalNodes definition and a uniform power certificate.
Python label checks are diagnostic. Lean checking is the proof.

After ordinary repository checks pass, the small patch may be reviewed/applied
with git apply. Rebuild its affected project modules and their public audit
endpoints before merging it. This review did not perform that final integration.

REBUILD THE REPORT

XeLaTeX, fontspec, unicode-math, fvextra, and the Latin Modern / DejaVu Sans
Mono fonts are required. Run twice in this directory:

    xelatex -interaction=nonstopmode -halt-on-error report.tex
    xelatex -interaction=nonstopmode -halt-on-error report.tex

INTERPRETING THE MEASUREMENTS

546 active Lean files contain 73,971 physical lines. The two generated Steps
files contain 6,567 lines, 999 step declarations, and 193 power declarations.
Their old pure-power components span 1,538 lines. The two compact production
certificate templates use 117 lines, before migrating named consumers or
adding compatibility wrappers. This is a component comparison, not an applied
project-wide saving. The witness constructors shrink from 59 to 32 declaration
lines, with an additional common helper cost that must also be counted.

No compilation-speedup benchmark is claimed. An unmodified GapCircuit66
compilation was terminated with exit code 137. Its exact-data fixture is a
separate, narrower validation route with an explicit byte-identity manifest.

MATHEMATICAL SCOPE

The proposals preserve the intended semantic boundaries: host arithmetic,
arbitrary-model internal naturals, and syntactic ZFC derivability are distinct.
The offset-19 theorem excludes 510 while permitting the actual 511 self-loop;
offset-20 works for an arbitrary function. Cyclic geometry includes N=1 and
arbitrary wrapped shifts. These proof refactorings do not establish any new
end-to-end consistency equivalence or complete pending machine/label binding.

All successful theorem audits in the final ledger use only the standard
propext, Classical.choice, and Quot.sound axioms (some use fewer or none).
The delivered checked examples do not rely on sorryAx or native-evaluation
axioms. See the manifest for which full imports and which isolated fixtures
were actually replayed.
