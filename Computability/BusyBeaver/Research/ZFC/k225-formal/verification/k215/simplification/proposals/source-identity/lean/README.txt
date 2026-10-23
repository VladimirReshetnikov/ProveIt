LEAN LOWER-CHAIN REVIEW
Pin: cbf94cb552a3b49509e0eee80e7455d4eb5974c6

Result: sharing is not automatically simplification. The optional guarded-
subtype kernel is NOT recommended as a source-size reduction for the current
two clients. Old translators/main proofs occupy 89 physical lines (99 with
tagged environment helpers); the complete uncompiled experiment adds 108 + 71
= 179 lines and still needs production API-preserving wrappers.

Start with REVIEW.md. It records the current status of previous proposals,
exact declarations, actual endpoint import paths, capture/guard obligations,
named-syntax exclusions, costs, and validation gates.

Artifacts:
  GuardedSubtype.lean           Uncompiled generic semantic induction draft.
  GuardedSubtypeAdapters.lean   Uncompiled syntax equality and semantic clients.
  source_snapshots.json         49 sources at the pin, metadata and contents.
  sources/                     Their exact on-disk source copies.
  audit_sources.py              Owned, read-only integrity and source-cost audit.
  SOURCE_AUDIT.json             Successful audit result.
  check_guarded_subtype.py      Owned finite capture/semantic regression audit.
  FINITE_CHECKS.json            Successful finite results and mutant witnesses.
  lean_negative_result.tex     Short TeX report fragment for incorporation.

Reproduce from this directory (standard-library Python only):
  python -I -B audit_sources.py --out SOURCE_AUDIT.json
  python -I -B check_guarded_subtype.py --out FINITE_CHECKS.json

Optional checkout comparison, read-only:
  python -I -B audit_sources.py --repo /path/to/ProveIt --out SOURCE_AUDIT.json

Neither script runs Lean, Git, repository generators, or upstream code.
The finite audit is not a quantified proof. No new Lean proof has been
compiled, and complete endpoint closure/build savings are unmeasured.
