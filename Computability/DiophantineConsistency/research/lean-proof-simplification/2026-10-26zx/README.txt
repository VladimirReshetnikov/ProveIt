PROVEIT / DIOPHANTINECONSISTENCY -- FURTHER PROOF SIMPLIFICATION IDEAS
26 October 2026

START HERE
Read report/ProveIt_Proof_Simplification_Review.pdf. Its complete LaTeX source is
beside it. Four ideas survived the strict comparison against prior proposals:
A. Consume the actual scalar realizer instead of maintaining a second Primrec route.
B. Transport the actual unused-dummy mutation by exact equal-boundary conservation.
C. Replace shifted_Q_bounds with one discrete endpoint envelope.
D. Optional: prove the fixed constant input predicate classically recursively enumerable.

PINS AND NOVELTY SCOPE
Initial source pin: 9d9d1123b39927d30363f1dcd53c23f0575c30ee
Final comparison pin: 60fcb2a69b7f1fdd4c3592ea5f164223cad50abe
Eight target/boundary source files have identical Git blobs at both pins.
The final exclusion corpus has 43 placed packets (a-zq); docs/incoming has only
its README. All earlier optional/deferred suggestions count as prior ideas.
See audit/novelty-audit.md and audit/final-refresh-addendum.md for methodology,
closest earlier ideas, rejected duplicates, and the finite coverage boundary.

WHAT WAS VALIDATED
The four principal files in lean/ compiled successfully under Lean 4.32.0 and
the repository's pinned Mathlib revision. ConstantPredicatePost01.lean is an
additional small checked template for using the public constant predicate
without opening the original namespaces. Logs report no sorryAx. Actual
ScalarPRCode was freshly compiled; all nine cached dependency Git pins match.
The full production module import closure and migration have NOT been built.
C is a complete exact-signature theorem replacement. B's production cyclic
adapter and raw perturbation proof remain proposed. A is an unapplied candidate
migration with static import checks and an independently checked proof core.
No compiler-performance improvement is asserted.

PATCH CHOICES -- DO NOT APPLY OVERLAPPING ALTERNATIVES BLINDLY
01-certificate-dependency.patch:
  A, against either inspected pin. Creates EnumeratorSemantics and replaces
  the computability certification route while preserving the actual program.
02-shifted-numerator.patch:
  C, independent of A and D, against either pin; no new imports/helpers.
03a-constant-predicate-original.patch:
  D, against ORIGINAL Computability. Alternative to overlapping edits in 01.
03b-constant-predicate-after-01.patch:
  D, ONLY AFTER 01. Uses decide (refutationInputs 0), avoiding namespaces
  that are no longer open in the extracted module. Do not also apply 03a.
No production patch is supplied for B; read the integration argument first.

All patches are proposals. No repository changes were pushed. In a clean,
separate checkout, typical application after review is:
  git apply /absolute/path/to/package/patches/02-shifted-numerator.patch
  git apply /absolute/path/to/package/patches/01-certificate-dependency.patch
Optionally, if classical proof provenance is acceptable:
  git apply /absolute/path/to/package/patches/03b-constant-predicate-after-01.patch
Then rebuild the affected production modules and existing project checks.

COUNTING
A: 608 -> 395 physical lines across ALL affected files, net -213, including
   the new module. This is a raw snapshot comparison, NOT an incremental
   estimate after all earlier proposals. 32 private pr_* declarations removed.
B: no net line count; remove the magnitude chain from mutation/rank clients.
   The broader no-unused-dummy theorem and exported helper checks need a
   separate compatibility decision. Do not advertise automatic deletion.
C: theorem 39 -> 29 and complete module 501 -> 491, net -10, no helper/import cost.
D: original theorem 14 -> 3, but corrected documentation makes full 03a net -10.
   After01, full 03b is -9 (Computability 36 -> 27). These are alternatives,
   not additive estimates of all prior-work-adjusted savings.

REPRODUCTION
Use a full checkout with the pinned Lean toolchain and Mathlib dependencies.
Do not run lake update merely to reproduce this review; preserve the manifest.
From this package:
  python3 scripts/check_patches.py --repo /absolute/path/to/ProveIt --with-after-01
  python3 scripts/check_lean.py --repo /absolute/path/to/ProveIt
The latter builds ScalarPRCode, then uses lake env lean for each supplied core.
It is a portable reproduction route; the existing receipts document the direct
compiler invocations actually used in this session. Passing the core checks
alone is not a full production migration build. If dependencies are absent,
normal Lake setup/download is required before reproduction.

PDF REBUILD
  cd report
  pdflatex -interaction=nonstopmode -halt-on-error ProveIt_Proof_Simplification_Review.tex
  pdflatex -interaction=nonstopmode -halt-on-error ProveIt_Proof_Simplification_Review.tex
The TeX source is self-contained and uses standard TeX Live packages. Fonts:
Latin Modern; PDF is searchable, with pinned clickable source links.

PACKAGE LAYOUT
report/       PDF and TeX source
lean/         four principal checked cores + small post01 template
patches/      candidate diffs with explicitly documented order/alternatives
validation/   successful receipts, exact counts, environment/static evidence
reference/    full A candidate files, original C theorem, integration notes,
              pinned toolchain and Lake manifest
scripts/      portable reproduction and nonmutating patch checks
audit/        prior-work ledger and identity/coverage manifests
MANIFEST.sha256  checksums of all deliverable files except the manifest itself

IMPORTANT SCOPE DETAILS
B: binary rotation is reduced separately on old/new Boolean assemblies; no
   global additivity claim for arbitrary numeric arrays. The current stronger
   normalized_nonwrap_of_safe lacks dummy j=0, so its old statement is not a
   direct consequence of the actual 0-to-1 update. All three actual mutation/
   rank consumers have that premise. A possible two-normalization compatibility
   proof is discussed but not checked or counted.
D: no consistency decision, no effective choice of constant program from an
   arbitrary proposition, and no new explicit polynomial coefficient recipe.
   Proof irrelevance applies only when replacing a proof of the SAME proposition.

The bibliography and evidence refer to the exact cutoff above; later repository
changes are outside this report. Novelty is relative to the requested corpus,
not a claim that the mathematical facts are new.

Repository license/reference attribution: reference/repository-LICENSE
