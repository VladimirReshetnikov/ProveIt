# Category Theory in Intuitionistic Primitive Recursive Arithmetic

Research report and reproducibility package, 20 November 2026.

## Start here

Read `category_theory_ipra.pdf`. Its complete LaTeX source is
`category_theory_ipra.tex` together with `sections/` and `references.tex`.

The report develops arithmetic presentations of categories and gives full
human-readable constructive proofs of the principal structural results:

- functors, natural transformations, composition, interchange and duality;
- Yoneda, full faithfulness, representability, uniqueness and universal elements;
- explicit co-Yoneda normal forms and density;
- universal-object uniqueness, products, equalizers, pullbacks, fixed finite limits and dual colimits;
- uniform finite-set limits, colimits and exponentials, including empty sets;
- adjunction hom correspondences and triangle identities, uniqueness and preservation;
- equivalences from displayed hom lifts and object isomorphisms;
- idempotent completion;
- monads, Kleisli and Eilenberg–Moore categories and adjunctions, and algebra limits;
- pointwise Kan extensions with supplied comma (co)limits, including uniform finite-set existence;
- Lawvere's fixed-point argument, the PR evaluator obstruction, and the two-class skeleton obstruction.

## Exact foundational scope

iPRA is first-order intuitionistic arithmetic with a symbol for each fixed
primitive recursive definition and induction only for quantifier-free formulas.
A presented category has fixed arithmetic predicates for objects, arrows and
hom equality, and PR code operations. Its equality may be undecidable.
Structural results are schemas yielding iPRA proofs for fixed presentations
whose law proofs and chosen universal operations are supplied. Uniform finite
table results quantify over numerical codes and use bounded Boolean invariants.

No universal total PR evaluator, arbitrary set universe, unrestricted choice,
general induction, or internal soundness/reflection principle is assumed.
The report does not claim all advanced results in every branch of category
theory; its scope and remaining hypotheses are listed explicitly.

## Verification status

1. **Human mathematics:** proofs and stated computational hypotheses are in the report.
2. **Reused upstream object-language sources:** 104 Lean files form the complete
   in-repository import closure of selected categorical modules from ProveIt
   commit `72d37f6d06fa7b5bd0a46732060446d1cffa3f2d`. The categorical derivation
   statements use `Prf PRAAx`. The upstream library reports kernel verification, but it
   was not rebuilt here.
3. **New Lean sources:** `LocalYoneda.lean`, `Representability.lean`, and
   `Density.lean` are explicitly **uncompiled integration drafts**. There was
   no Lean executable in the generation environment. Absence of placeholders
   is not a compilation or verification claim.
4. **Executable validation:** all exact finite-model checks described in
   `code/README.md` passed; the JSON receipt records case counts. These checks
   are neither a general proof nor an iPRA proof checker.

The local Yoneda interface is intentionally weaker than the upstream uniformly
parameterized transformation law record, so it applies to one specified
transformation. The finite-set development handles zero cardinalities that
require additional work beyond the inspected upstream positive-size results.

## Reproduce

### PDF

Run `bash build_pdf.sh` from this directory. It prefers pdfLaTeX and falls back
to Tectonic when pdfLaTeX is absent. Standard LaTeX packages are required.
For a minimal Debian-style TeX installation with package files but no generated
format or font map, the script builds these in a temporary directory; it does
not modify the system installation. This path was used for the delivered PDF.

### Exact model checks

Run `python3 code/finite_models.py --json code/verification_results.json`.
Only the Python standard library is needed. The finite-colimit code uses
bounded Warshall closure; the report proves sequential merging. Both give
the same finite-path quotient.

### Lean

The target toolchain and Mathlib release are both `v4.32.0`, matching the pinned
repository. See `lean/README.md` for exact commands and
`lean/formalization_roadmap.md` for the definitions, already available lemmas,
remaining modules, and required verification steps. The standalone Lake
package includes its in-repository sources but not Mathlib, Lean, or compiled
caches. Network access is required to obtain those external dependencies.

## Contents and provenance

- `proof_status.json`: theorem-family status and assumptions.
- `code/`: exact finite models and successful-run receipt.
- `lean/CategoryIPRA/`: new object-language integration drafts and audit entry point.
- `lean/Upstream/`: pinned repository dependency closure, with upstream license.
- `provenance/`: source inventory, original dependency-lock snapshot and source hashes.
- `audit/`: independent mathematical review notes and a precise chosen-limit interface.
- `validation/`: PDF build/quality records.
- `MANIFEST.sha256`: checksums of delivered files, excluding itself.

This is a source-and-report deliverable. No commit, issue, or pull request was
created in ProveIt. The archive can be reviewed and integrated into the
repository's existing research-packet workflow.
