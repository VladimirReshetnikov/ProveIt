K215: COMMON MACROS AND SEED INTERFACES
=====================================

Reviewed ProveIt revision:
  6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95

Prepared October 21, 2026 (America/Los_Angeles).

Read paper/report.pdf for the complete proposal, proofs, current-source review,
measurements, verification scope, integration steps, and further questions.
The LaTeX source is paper/report.tex, with measurements in paper/results.tex.

RESULTS
-------

1. Rocq common macro library (checked component, production migration pending).
   The entire maintained 780-line arithmetic macro proof compiles against a
   sparse canonical graph retaining just 89 cells. Their original labels are
   retained: this is not an 89-state machine. The 58 fixed-node contracts use
   53 roots; the retained cells are their exact descendant closure.

   A new generic theorem transports all finite structured runs, preserving
   arbitrary register functions and all exit forms. Literal bindings are
   checked independently for the 215 and 217 program DAGs. All 58 concrete
   K215 macro contracts compile by transport. Root 0 is outside the footprint;
   no equivalence of the two whole enumerators is claimed.

   Fresh Coq 8.18.0 check: 13 project modules, 63 closed assumption reports
   including all 58 contracts, recursive coqchk PASS. The maintained full
   endpoint's Rocq 9.1.0 replay remains a production integration gate.

   The prototype is not yet a drop-in ProgLibPerm replacement: the common St
   record and program-specific sequence utilities need a compatible facade.
   The eight new component files total 1,300 lines / 61,524 bytes. These are
   reuse measurements, not an achieved endpoint source reduction. Use one
   parameterized adapter/functor rather than copying its 58 thin wrappers
   into each candidate. See rocq/README.md for the precise migration plan.

2. Lean envelope/comprehension sharing (small independent reduction).
   patches/01-envelope-sharing.patch changes KLowerTag and KLowerQHyp.
   It shares raw_envelope and dt_comp_env, and preserves existing interfaces.
   Total: 477 -> 457 lines; 22,580 -> 21,681 bytes (-20 lines, -899 bytes).
   This patch is independent of the functional-seed experiment.

3. Optional Lean functional-seed normalization and stronger theorem.
   patches/02-functional-seed-optional.patch adds KSeedFunctional and changes
   KLowerRaw. It proves seedProp_iff_closure without axioms, rewrites the raw
   constructions around root/image/step, and proves raw_aug_core without
   irreflexivity while retaining the old raw_aug interface.

   Full support cost: 202 -> 239 lines; 9,381 -> 11,217 bytes (+37 lines,
   +1,836 bytes). This is not an immediate source-size saving. Adopt it for
   the stronger theorem, the clearer interface, or reuse by additional clients.

   The Boolean counterexample shows that the functionality hypothesis cannot
   simply be dropped from this general normalization theorem, even with
   irreflexive membership.

VERIFICATION
------------

The final Lean combined replay freshly checks 65 project modules plus three
audit modules with Lean 4.32.0. Twelve typed examples cover old interfaces and
the strengthened theorem. Baseline and proposed elementary raw-theorem axiom
reports are byte-identical. The counterexample and generic normalization have
no axioms. tag_qhyp and zf_consistent_of_formSeed use only propext,
Classical.choice, and Quot.sound.

The envelope-only replay separately checks the patch against the ORIGINAL
KLowerRaw, with 64 project modules plus one explicit interface audit. Thus
adopting the smaller patch does not require the optional normalization.

Fresh Lean receipts and all compiler logs are in lean/evidence/combined and
lean/evidence/envelope. Rocq's fresh receipt and kernel log are under
rocq/evidence/final. Independent source reviews and census scripts are under
audit; root replays and the overall validation summary are under evidence.

These are component and semantic lower-chain checks. This packet does not
rebuild the full physical-machine endpoint, which has additional source,
bootstrap and site certificates. The existing endpoint proof and its stated
internalization boundary are documented in the pinned repository.

REPLAY
------

Run from this packet's root. Supply absolute paths for the checkout and the
pinned Lean binary. No script fetches files, runs repository generators, or
modifies the checkout. Each build needs a fresh output directory.

Source/data audits:

  python3 audit/audit_macro_footprint.py /path/to/ProveIt
  python3 audit/audit_macro_component.py /path/to/ProveIt rocq/src
  python3 rocq/audit_sources.py /path/to/ProveIt

Rocq component (Coq 8.18.0 coqc/coqchk on PATH):

  python3 rocq/build.py --build-dir /path/to/fresh-rocq-build

Combined Lean changes, all typed clients, and the counterexample:

  python3 lean/verify_lean.py --repo /path/to/ProveIt \
    --lean /path/to/lean-4.32.0/bin/lean \
    --build-dir /path/to/fresh-lean-combined --mode combined

Envelope-only patch against the original raw constructions:

  python3 lean/verify_lean.py --repo /path/to/ProveIt \
    --lean /path/to/lean-4.32.0/bin/lean \
    --build-dir /path/to/fresh-lean-envelope --mode envelope

Optional independent reproduction of the original elementary axiom reports:

  python3 lean/verify_lean.py --repo /path/to/ProveIt \
    --lean /path/to/lean-4.32.0/bin/lean \
    --build-dir /path/to/fresh-lean-baseline --mode baseline

The Lean checker requires the pinned HEAD. A full checkout suffices. For a
sparse checkout, materialize these source roots and root Lake configuration:
  Computability/BusyBeaver/Lean
  Logic/FirstOrder/Lean
  SetTheory/ZF/Lean

Patch review/application from the repository root:

  git apply --check /path/to/packet/patches/01-envelope-sharing.patch
  git apply /path/to/packet/patches/01-envelope-sharing.patch

The optional second patch changes different files and can be considered
separately. Before production adoption, rebuild unchanged endpoint clients
and synchronize relevant generators. No remote repository write is performed
by this packet or its scripts.

Rebuild the paper from its source directory:

  cd paper
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

FILE INTEGRITY AND ATTRIBUTION
-----------------------------

MANIFEST.sha256 hashes every delivered member except the manifest itself.
The receipts additionally bind source files to each compiler invocation.
Proof objects and LaTeX intermediates are omitted; the builders recreate them.

Inherited ProveIt material is under its MIT No Attribution license, included
as LICENSE.ProveIt. Rocq source attribution and inherited notices are preserved
under rocq/NOTICE.md and rocq/licenses. The canonical library is a systematic
retargeting of the maintained proof, not new authorship of its arithmetic.
New proof refactors, audits, build scripts, and manuscript in this packet may
be incorporated under the same MIT No Attribution terms.
