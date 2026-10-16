# ZFC closure kernels: intake reconciliation

Intake findings, 16 October 2026. Batch 143 combines three manuscripts from
arrival `9e5b610259cd42c88e2cf6c862fb876a7c6d6fcd`, placed in `b07d1a27b`.
This is the reconciliation-note option in `docs/incoming/README.md`, section 2:
the delivered base article is preserved, rather than rewritten as a unified article.
No merged PDF is built. These are ordinary mathematical arguments and finite
regression checks; none of the new kernels is formally verified in this repository.

The user's current machine target is an equivalence **provable in ZFC** between
blank-tape non-halting and Con(ZFC), with fewer than 254 nonhalting states on a
binary, two-way infinite, single tape. The sources discuss the stronger PA
metatheory. Their missing proof compilers remain missing; changing our target
does not turn their experiments into a formal equivalence proof.

## Sources, overlap and base

| Source | Delivered archive | Contribution |
|---|---|---|
| 01, BIC | `zfc_closure_research.zip` | Extensionality + inhabited membership + subset-bounded positive image closure; equality-free QBC using profile congruence; an executable Hilbert certificate checker; deletion diagnostics. |
| 02, seeded closure (base) | `zfc_closure_research (1).zip` | Reflexive point/subset seeds remove the separate inhabitedness axiom; mixed member/subset bounds; two-cycle Pairing and Russell-root Replacement; equality-free subset control; alternative calibrations and implementation questions. |
| 03, exact fibers | `zfc_exact_fiber_hulls.zip` | Extensionality + a transitive rooted hull containing exact output fibers; subset-bounded rooted-closure intermediate; direct equality-free control and deletion diagnostics. |

All three calibrate a closure kernel against ZF with Foundation and Choice
omitted, using functional Replacement, then invoke the usual effective
Foundation/Choice consistency reductions. Their converse arguments collect
**unique exact fibers**, rather than silently choose a family of arbitrary
local bounds. All allow matrices of arbitrary complexity and arbitrary finite
parameter tuples, with fresh auxiliary variables. These are infinite schemas.

02 is the base because its reflexive seed removes 01's separate inhabitedness
sentence. 03 offers a complementary mechanism rather than an improvement of
that same expanded formula. Each manuscript's own definitions and proof route
remain attributable to that source. The following controls and limitations are
retained, without treating formula-size rankings as machine-size rankings:

- 01: guarded images, partial functional images, singleton-decoding Union,
  Infinity from repeated closure, direct profile equality elimination, and
  the certificate format. Removing inhabitedness admits the empty one-object
  structure; removing range purity admits the universal one-object structure;
  removing repetition admits hereditarily finite sets; member-only bounds
  admit the hereditarily countable model. Unrestricted unbounded images are
  inconsistent. Congruence-free RBC0 remains uncalibrated in the source.
- 02: exact constant classes, two-cycle Pairing, membership closure for Union,
  Russell-root Replacement, successor Infinity, exact-fiber converse, a
  reflexive-seed criterion, `Ext + Separation + SBC`, and
  `Ext + nonempty-membership + ISI` calibrations. Its empty-membership one-object model satisfies `Ext + ISI` without
  nonempty membership and `Ext + Separation + set-seeded closure` without
  Power Set; its full-membership model satisfies `Ext + SBC` without
  Separation. These deletion models are preserved in its experiments.
  Membership-arm deletion, congruence deletion, restricted matrix grammars,
  shared seed/fiber code, and proof-certificate engineering are research
  questions in the delivered article. Any subsequent answer belongs to new
  research, not to this intake finding.
- 03: the corrected MathOverflow seed convention, the gated singleton decoder,
  subset-rooted closure, EFH, its equality-free profile interpretation,
  container/subset-image consequences, successor Infinity, and the exact-fiber
  converse. Pure membership bounds and dropping exactness have explicit
  countermodel diagnoses. Removing transitivity and profile congruence are
  not calibrated by the delivered theorem. Finite-class/ground-refutation
  alternatives and full machine compilation remain further work.

No historical priority, global minimality, ZFC inconsistency, finite
first-order axiomatization, serialized PA proof, verified Python checker,
complete bridge certificate, new TM table, or new state bound is claimed.
Source 02 inherits the full raw RCC/bisimulation calibration rather than
reconstructing it; this intake did not reconstruct it either.
No claim was found demonstrably false requiring a repository retraction.

## Current-tree overlap and missing provenance

None of the three deliveries states the ProveIt commit it was written against.
This fails the requested pin provenance; **no pin has been inferred**. Their
`zfc-consistency.zip` input provenance refers to a different attachment, which
is not supplied here. Sources 01/02 instead pin their external machine audit
to `jeff87654/busy-beaver` commit
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`; 03 records an upstream README
blob. Neither is a ProveIt pin or an independently rerun benchmark build.

The current tree already says, in `SetTheory/ClosureAxiomatization/README.md:3`:
“The project proves, independently in Lean and Coq, that the theory retaining
Extensionality, Regularity, Separation, and Powerset while replacing Pairing,
Union, Infinity, and Replacement by a single set-like-relation Closure schema
is exactly ZF.” Its `Lean/ClosureAxiomatization/Equivalence.lean:624` declares `T_iff_ZF`.
The directions at lines 547–555 and 595–597 already use Foundation-free
components; `Lean/ClosureAxiomatization/Forward.lean:7` explicitly notes Regularity is unused.
Thus reconstruction of the linked MathOverflow closure proposal is a
predecessor/control, not a new repository gap. These declarations do not
formalize BIC, seeded positive closure, EFH, their equality-free variants,
the paper-level PA calibration, or a small consistency-search machine.

## Placement and unchanged delivery paths

`article.tex` is source 02's delivered `article/seeded_closure_zfc.tex`, unchanged.
It retains its existing labels, with no common intake label prefix. No labels
were renamed. The source 02 delivery README was staged unchanged in the
placement commit; this reconciliation replaces it afterward.

The other articles, all three PDFs, and original READMEs are recoverable from
the arrival archives. Under the intake placement table they are not duplicated
here. Ancillary files are preserved with `01-bic-`, `02-seeded-`, and
`03-fibers-` prefixes: executable files under `code/`, records under `data/`,
and audit/provenance Markdown at the report root. The exact 53-file rename
map is `data/placement-map.json`. The placement was checked against fresh,
untouched extractions, and all 60 extracted blobs were searched in history
with `git log --all --find-object`; there was no previous placement hit.
Checksums and line endings received no special treatment.

All prefixed scripts retain their delivered import names and directory
assumptions. In particular `*-build.py` expects the original `article/`,
`code/`, and `results/`; the BIC checker imports `logic`, seeded scripts
import `formulas`, and fiber scripts import `syntax` / `prior_templates`.
The prefixed audit notes, provenance files, templates and build/QA records
likewise name the original package paths, PDFs and the unbundled input ZIP.
They describe delivery-time artifacts, not a promise that those paths exist
in this flattened placement. Run from recovered scratch packages as below.

## Verification and reproduction

All advertised Python checks ran on separate copies, without touching the
extractions used for placement:

| Source | Executed evidence |
|---|---|
| 01 | 12 unittest methods; 66,066 graphs and 1,052,740 graph/seed pairs; metrics; a valid identity certificate explicitly **not** a refutation. |
| 02 | 66,066 graphs, 1,052,740 relation/seed pairs, 16,810,248 candidate witnesses, 263,714 point-seed checks; 4,096 HF roots, 531,429 local-bound checks, 555,198 hull members, 65,536 singleton-decoding families; 4,000 randomized expansions and 4,160 model/template expansion checks. |
| 03 | 262,404 membership/matrix pairs; four unittest methods and 5,600 formula-semantics comparisons. |

Source 02 and 03's delivered PDF builders also completed on scratch copies.
This reproduced their builds, not a merged-report PDF or a formal proof.
Expanded metrics differ between sources and normalization policies: 01 gives
QBC 58/56 versus RCC 60/50; 02 gives T_pt 69, T_sub 72, Q_sub 83;
03 gives equality-free EFH control 65 versus prior extensional control 78
(raw nonextensional prior 61). Source 02 excludes variable payloads, arbitrary parameter closure, logical
equality machinery, the proof engine, and the TM backend. These rankings do
not predict machine states. Compare only within a declared metric.

From the repository root, reproduce all Python checks with:

```sh
uv run --no-project python SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/reproduce.py
```

The helper recovers each archive from the committed arrival into its own
new directory **outside** the repository, then runs the delivered commands
using the invoking Python. It reports the scratch location and retains run
logs there. Repository files and the intake extractions stay untouched; regenerated
outputs and logs remain in the recovered scratch packages. To recover the
full manuscripts without running suites, add `--prepare-only`. For a source's
PDF, run its recovered `build.py` there with a suitable TeX installation.

No external machine table, Coq end-to-end development, proof-producing theory
translator, enumerator correctness theorem, or ZFC endpoint was rebuilt here.


## Subsequent minimization research

After intake, [the ZFC machine project](../../../../../../Computability/BusyBeaver/Research/ZFC/README.md)
answered source 02's membership-arm deletion question at the mathematical
level by combining its positive hull with the gated singleton decoder.
`BusyBeaver/ZFC/PositiveClosure.lean` checks the key bootstrap lemmas;
`DeepPositiveClosure.lean` defines the actual equality-free first-order
wrapper and proves its semantic specification. `ProfileCongruence.lean`
checks that the symmetric congruence conclusion can be replaced by one
implication. These are partial formal results, not a completed deductive
calibration or a new small-machine theorem. The delivered source 02
article remains unchanged, including the question it left open.
