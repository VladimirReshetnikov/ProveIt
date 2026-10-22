K215: COLLECTION FIRST, SHARED MACRO SLICES, AND ONE AX EFFECT PROOF
================================================================

Review date: October 21, 2026 (America/Los_Angeles).
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95

Read K215_Proof_Simplification_Report.pdf or its LaTeX source for the
complete argument, current-source review, adoption plan, and scope.

The packet provides three checked proposals:

1. Lean: transport formula-indexed Collection to the quotient once and
   derive native Separation and Replacement. Reuse partial Replacement
   to prove Separation in the well-founded model. The exact existing
   public types are checked under fresh namespaces (35-module check).

2. Rocq: share register macros through a finite closed-support theorem.
   All 53 macro roots close to 89 literal DAG rows identical in the
   215, 217, and 218 developments. The checked theorem preserves every
   register file and exit. Six modules plus recursive coqchk pass.

3. Lean: one generic checked word interpreter and an exact equality of
   the maintained Perm and Dom AX effects for all abstract states.
   The two 156-atom words differ semantically by one commuting pair.
   Thirty repository dependencies plus three proposed modules pass.

CONTENTS
--------
code/lean/collection-first/  Actual-schema and quotient adapters; WF reuse.
code/lean/macro-word/        Generic word semantics and literal AX equality.
code/rocq/macro-slice/       General run transport, concrete bindings,
                             four pinned dependency sources and notices.
code/rocq/collection-first/  Constructive mathematical core in Coq.
scripts/inventory.py        Exact current closure and guard counterexample.
evidence/                  Aggregate scope, census, counterexample, PDF QA.
MANIFEST.sha256             Integrity hashes (excluding itself).
licenses/                  Main ProveIt terms; component licenses also kept.

VALIDATION SCOPE
----------------
Lean components were checked with Lean 4.32.0. Rocq-compatible components
were checked with Coq 8.18.0 and recursive coqchk. The production Rocq lane
uses Rocq 9.1.0 / rocq-stdlib 9.0.0; adoption must use that toolchain.

These are additive checked components, not a production deletion patch.
The existing complete K215 endpoint was not rebuilt in this review. No
production file or machine table was edited. Local proof-body savings and
repeated source bodies are measured, but no net adopted byte saving,
build-time improvement, or smaller kernel term is asserted.

The quotient argument uses ordinary equality in Lean's quotient type.
The Rocq set-theory route proves object-language derivations, so the
standalone Prop-level collection lemma is not its replacement. The
Rocq macro-slice theorem applies directly to actual register semantics.

REPRODUCTION
------------
Use a local repository checkout at the pinned commit. Required source
roots are Computability/BusyBeaver/Lean, Logic/FirstOrder/Lean,
SetTheory/ZF/Lean, and (for the full inventory) SetTheory/BoundedConsistency/Lean.
Use fresh output directories or a fresh copy of this packet to preserve
the delivered receipts. No compiler binaries or compiled proof objects
are included.

  python3 code/lean/collection-first/check_repository.py REPO LEAN

  python3 code/lean/macro-word/build_prototype.py \
    --repo REPO --lean LEAN --out NEW_BUILD_DIRECTORY

  python3 code/rocq/macro-slice/build.py
  python3 code/rocq/collection-first/build.py

For Coq/Rocq, set COQC and COQCHK if they are not on PATH.

  python3 scripts/inventory.py --repo REPO --output NEW_AUDIT_DIRECTORY
  python3 scripts/verify_integrity.py

To rebuild the PDF:

  pdflatex -interaction=nonstopmode -halt-on-error K215_Proof_Simplification_Report.tex
  pdflatex -interaction=nonstopmode -halt-on-error K215_Proof_Simplification_Report.tex

INTEGRATION NOTES
-----------------
Retain the ModelsGIC-only raw trace instance used to establish QHyp.power.
Preserve any needed SubD conclusion of the old interpreted Separation API.
The well-founded-model reorder is acyclic; doing the same to inL_sep would
be circular because inL_repl calls it. Transport only the checked macro
slice: dispatcher node 141 and changed AX/root nodes are outside it.
Keep separate program-binding checks for the two AX words.

Existing normalized source certificates, quotient unification and complete
decoder/residual coverage are prior repository proposals. This report
distinguishes those results from the newly checked components in this packet.

PROVENANCE
----------
New original prose/code is supplied under the MIT No Attribution terms in
licenses/ProveIt-LICENSE. Existing source fragments retain their original
headers and terms. QuotientCollectionFirst incorporates KQ1Collect and the
environment-selection helpers. The word interpreter generalizes the current
AX developments. The macro-slice component includes its own source manifest
and upstream attribution. No authorship of the K215 machine or its existing
logical calibration is claimed.
