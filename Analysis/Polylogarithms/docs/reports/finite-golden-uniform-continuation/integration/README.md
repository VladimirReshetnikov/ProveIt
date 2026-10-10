# Integration guide for the ProveIt manuscript

This guide maps the completed article to the manuscript at commit
[`28357e8ca63dd78327db91d9be239d75e4462879`](https://github.com/VladimirReshetnikov/ProveIt/tree/28357e8ca63dd78327db91d9be239d75e4462879/Analysis/Polylogarithms/docs/manuscript).
It describes proposed local edits. No remote repository files have been
changed.

The standalone master is
`article/polylogarithms_uniform_continuation.tex`. Its six content inputs
are `golden`, `geometry`, `real_boundary`, `moments`, `depth`, and
`discussion`, followed by `references`. The master supplies the preamble,
front matter, introductory status guide, and global conventions. The
chapter fragments themselves contain no document preamble or bibliography
environment.

Preserve the complete bundle as the source and verification record. A
repository location consistent with the existing report layout is:

`Analysis/Polylogarithms/docs/reports/polylogarithms-uniform-continuation-20261010/`

The placements below use that report directory and copy selected TeX
fragments into the canonical manuscript. All chapter paths in the next
section are relative to `Analysis/Polylogarithms/docs/manuscript/`.

## 1. Concrete chapter placements

| Bundle input | Proposed canonical fragment |
|---|---|
| `article/golden.tex` | `chapters/03-golden-seeds.tex` |
| `article/geometry.tex` | `chapters/05-real-order-signed-kernels.tex` |
| `article/real_boundary.tex` | `chapters/05-critical-signed-boundary.tex` |
| `article/moments.tex` | `chapters/07-joint-reflected-moments.tex` |
| `article/depth.tex` | `chapters/04-sixth-weight-obstruction.tex` |
| `article/discussion.tex` | `chapters/10-uniform-research-programme.tex` |

### Golden seeds

In `chapters/03-algebraic.tex`, insert the new golden fragment immediately
after the existing `\input{chapters/03-complement-rigidity}` and before
the section **The modified polylogarithm**. The existing cubic/quartic
certificates and complementary-power classification then precede the
new complete multiplicative-seed theorem; the modified-polylogarithm
and Bloch-group discussion follows it.

The new fragment begins **Complete multiplicative seeds at the golden
base**, label `golden:sec:complete-seeds`. It is mathematically
self-contained apart from its stated external primitive-divisor input.
Its six-generator integral lattice, the four-generator even-power
lattice, and the restriction to powers of the base should remain
together. Preserve the final distinction between a specified symbol
kernel and an analytic identity among higher polylogarithm values.

### Real-order signed kernels

In `chapters/05-signed-kernels.tex`, insert the new real-order fragment
immediately after `\input{chapters/05-affine-signed-moments}` and before
the section **An exact kernel and the sharp Euler error**. This places
the real-order classification after the existing integer-order
one-crossing theorem and the affine real-order measure construction.
The parent `chapters/05-certified-computation.tex` already inputs
`05-signed-kernels`; no additional top-level chapter is needed.

The fragment starts **Real-weight signed kernels and a sharp measure
threshold**, label `real:sec:kernels`. It extends the domain to all real
`a,b > 0`, classifies finite signed measures by `a+b >= 1`, and includes
the interior-disk zero arc. It belongs with these signed kernels, rather
than the separate Stieltjes-constant zero chapter
`09-zero-geometry.tex`.

### Critical boundary

Insert the boundary fragment immediately after the new real-order
fragment at the same location in `05-signed-kernels.tex`, before the
existing sharp-Euler-error material. It starts **The critical boundary:
a power-law crossing and an exponential mass law**, label
`real:sec:boundary`.

This input depends on `geometry.tex`: it uses the definitions of
`k_{a,b}`, `g`, `I`, the beta-integral identity, and the finite-measure
theorem. Keep the real-order fragment before it. The power-law location
of the density crossing and the exponentially rescaled mass law describe
different scales; neither statement should be substituted for the other.

### Joint reflected moments

In `chapters/07-integration.tex`, insert the new moment fragment
immediately after `\input{chapters/07-reflected-moments}` and before
the section **The Stieltjes layer**, label `integral:sec:stieltjes`.
The existing order is `07-loggamma-moments`, `07-sharp-moments`,
`07-reflected-moments`; retain that sequence before the addition.

The new input begins **A joint transition for reflected log-gamma
moments**, label `moment:sec`. Its notation matches the reflected
moments and residue array already defined in
`07-reflected-moments.tex`, in particular
`reflected:gam:eq:residue-coefficients`. The joint limit is an extension
of the fixed-reflected-exponent theory, not a replacement for it.
Keep the weighted-localization proof with the transition theorem: it
is what justifies uniformity when both exponents grow.

### Weight-six formal depth obstruction

Append the new depth fragment at the end of
`chapters/04-shuffle-parity.tex`, immediately after its final
`\input{chapters/04-complementary-depth}`. That file is already
included by `chapters/04-depth.tex`. This places the obstruction after
the constructive complementary-depth theorem that explains why triples
at weight six are the first critical case.

The fragment starts **A sharp formal obstruction at weight six**, label
`depthnew:sec:obstruction`. Preserve the specified quotient, its letter
action, and its endpoint/product convention. The dimension statement
and the two congruences concern this formal quotient. They do not assert
numerical independence after special-point evaluation and do not resolve
the manuscript's `S_6` conjecture, whose total weight is seven.

### Discussion and further research

Append the discussion fragment to `chapters/10-discovery.tex`, after
the final section **A certified rejection beyond the discovery
precision**, label `research:sec:S8-rejected`, and its concluding
paragraph about the coordinate-equivalent `S_6` conjecture.

The input contains three peer sections: **Corrections and status
revisions for the manuscript**, **Further research questions and
proposed relations**, and **Reproducibility and integration**. If the
whole input is retained, make its references to “the source” explicitly
refer to the pinned pre-integration snapshot. After applying
`corrections.patch`, the incorrect historical wording no longer describes
the current integrated chapter.

For a more compact book, the first section can instead inform
`EDITORIAL-LEDGER.md`, the second can extend the existing research
programme in `10-discovery.tex`, and the last can inform the manuscript's
verification documentation. Preserve the actual conjecture statements
and their evidence limits. This selective option requires updating the
cross-references described below; the standalone article remains the
complete record.

## 2. Heading levels, preamble, and conventions

Every primary mathematical input starts with `\section`; its internal
divisions use `\subsection`. At the placements above, these are peer
sections inside an existing book chapter and can retain their present
levels. If an editor instead makes one input a separate chapter, promote
its top section to a chapter and its subsections to sections consistently.
If an input is nested under an existing section, demote both levels
consistently. Do not change labels merely to change heading depth.

Reuse the manuscript's theorem and equation counters. Do not import the
standalone master's `\documentclass`, title matter, page geometry,
headers, `\newtheorem` declarations, or `\numberwithin` command into a
chapter file. The content uses standard `amsmath`, `amssymb`, `amsthm`,
and `mathtools` constructs, the existing `\Li` operator, ordinary
theorem/proposition/lemma/corollary/proof environments, plus example,
remark, and conjecture environments. The numerical table in
`moments.tex` uses `booktabs`; figures use `graphicx`; `\path`,
`\href`, and `\texorpdfstring` use the existing URL/hyperlink support.
The fragments require no new mathematical macro namespace.

Retain these conventions when the standalone introduction is omitted:

- Multiple polylogarithms use strict inequalities, with the largest
  summation index first; the real-order coefficients are
  `H_{n-1}^{(b)}/n^a`.
- At `a+b=1`, the unit-circle function is the signed-measure analytic
  continuation or a radial Abel value away from `1`. The original
  boundary series does not converge there because its terms fail to
  tend to zero.
- The depth input interprets the outer letter first and explicitly
  specifies its quotient by products and endpoint constants.
- Algebraic seed identities, formal quotient congruences, and numerical
  special-value identities retain their separate meanings.

## 3. Labels and cross-file dependencies

An exact comparison of `\label{...}` names in the six delivered
fragments against the downloaded pinned chapter sources found **no
collisions**, and no label is duplicated within the six new inputs.

| Input | Label prefix | Integration note |
|---|---|---|
| `golden.tex` | `golden:` | The source already uses this prefix for six displayed golden/tetralogarithm equations. All 31 new full label names differ from those existing names. |
| `geometry.tex` | `real:` | Shared intentionally with `real_boundary.tex`. |
| `real_boundary.tex` | `real:` | References definitions and theorems in `geometry.tex`. |
| `moments.tex` | `moment:` | Different from the source's `reflected:`, `sharp:`, and `integral:` names. |
| `depth.tex` | `depthnew:` | Different from the existing Gaussian/shuffle prefixes. |
| `discussion.tex` | `editorial:`, `future:`, `repro:` | Contains references to the other new inputs. |

The boundary input specifically references `real:eq:beta`,
`real:eq:critical-density`, `real:eq:level`,
`real:eq:scaled-integral`, and `real:thm:measure`. A prefix change must
therefore update both real-order files and the discussion, not just one
fragment. A global textual replacement of `golden:` would also touch
the proposed bibliography keys; update labels and citation keys
deliberately as separate operations.

`discussion.tex` refers to results in `geometry`, `real_boundary`,
`moments`, and `depth`. If only some mathematical inputs are integrated,
retain the others as cited report sections or revise those references
and the related agenda paragraphs. The standalone master's introductory
table also refers to the new theorem labels; it should not be copied
without its referenced inputs. Recheck exact names against the actual
target revision, since the no-collision result concerns the pinned
snapshot only.

## 4. Bibliography merge and de-duplication

Both `article/references.tex` and the manuscript's `references.tex` use
`thebibliography`. Merge selected `\bibitem` blocks into the existing
environment; do not nest one bibliography environment inside another.

The recommended sequence is to review/apply `corrections.patch`, then
merge the research citations. The patch supplies four complete keys:
`golden:AbouzahraLewin1985`, `golden:AbouzahraLewinXiao1987`,
`golden:BaileyBroadhurst1999`, and `golden:Gangl2013`.
Its inserted chapter citations resolve with those keys without any
additional article files.

Use the following citation mapping to avoid duplicate works when the
article is integrated as well:

| Article key | Recommended integrated key | Action |
|---|---|---|
| `ProveIt` | `ProveIt` | Add the pinned-snapshot entry, or replace its few uses by precise internal provenance references. If kept, replace “full hash on the title page” with the full pinned hash in the entry; the book has a different title page. |
| `Flatters2009` | `Flatters2009` | Add this new entry. Retain the journal year 2009 and the identified Theorem 1.4 in the inspected preprint. |
| `BaileyBroadhurst1999` | `golden:BaileyBroadhurst1999` | Reuse the entry supplied by the patch; update the imported citations. Both entries identify the same 1999 preprint. |
| `AbouzahraLewinXiao1987` | `golden:AbouzahraLewinXiao1987` | Reuse the patch entry; preserve the corrected publication and page range 23–45. |
| `Amdeberhan2011` | `gaussian:ACEMKM` | Reuse the existing manuscript entry for the same six-author paper. |
| `Li2026` | `Li2026` | Add the new preprint entry, preserving its inspected version and date. |
| `depthnew:Radford` | `gaussian:Radford` | Reuse the existing manuscript entry for the identical 1979 paper and DOI. |
| `DLMF` | `hstruct:DLMF` | Reuse and broaden this existing general DLMF entry to include Sections 5.7 and 25.11, while retaining its already cited Sections 2.11, 5.11, and 25.15. Update the imported citations. |
| `Gangl2013` | `golden:Gangl2013` | Reuse the patch entry and its published volume year 2013. |
| `Campbell2024` | `Campbell2024` | Add the inspected 2024 preprint entry as supplied; do not silently change the cited version when merging. |

The patch-only key `golden:AbouzahraLewin1985` has no duplicate in the
article bibliography and should be retained. The source has several
other section-specific DLMF entries, such as `zeros:DLMFGamma` and
`hergjet:DLMF`; those cite different formulas. A broader bibliography
consolidation is optional and must preserve their section and equation
details. If the DLMF entry is left separate instead, keeping the supplied
`DLMF` key is a valid alternative to the mapping above.

If the editorial patch is not applied, the three `golden:` entries
created by it will not exist. In that case import the corresponding
article entries under their original keys, or create the selected
integrated keys explicitly before changing citations. Do not change a
citation key without also preserving a matching bibliography item.

## 5. Figures and relative paths

The standalone article is built from `article/`, so its three figure
paths start with `../figures/`. LaTeX resolves these relative to the
compilation directory, not automatically relative to each included
chapter. Under the proposed report location, replace the three paths
in the canonical manuscript copies as follows:

| Input | Current figure path | Path from the manuscript build directory |
|---|---|---|
| `geometry.tex` | `../figures/measure_geometry.pdf` | `../reports/polylogarithms-uniform-continuation-20261010/figures/measure_geometry.pdf` |
| `real_boundary.tex` | `../figures/boundary_two_scales.pdf` | `../reports/polylogarithms-uniform-continuation-20261010/figures/boundary_two_scales.pdf` |
| `moments.tex` | `../figures/moment_transition.pdf` | `../reports/polylogarithms-uniform-continuation-20261010/figures/moment_transition.pdf` |

The PDF figures are the publication assets; accompanying PNGs are
previews. Preserve captions and figure labels with the corresponding
input. `code/make_figures.py` provides figure generation in the archived
bundle. If a different report directory is chosen, adapt all three
paths together; the mathematical text does not need a new graphics
package to accomplish this.

The prose paths to `code/...`, `data/...`, `README.md`, and
`integration/README.md` refer to the delivered report directory. When
those paths appear in an integrated book chapter, qualify them by the
report location or add one explicit statement giving that base path.
Preserve the `code/` and `data/` sibling layout for replays: several
programs derive output locations from their own file paths. Moving
scripts into the manuscript's verification directory without adapting
those assumptions would change where they read or write artifacts.

## 6. Review records and mathematical status

`EDITORIAL_NOTES.md` explains every proposed correction and the exact
canonical-ladder reconstruction; `corrections.patch` remains a separate
reviewable artifact against the original snapshot. Neither file should
be overwritten merely to record the subsequent integration.

The bundle's main `README.md` is the authority for article builds and
verification commands. After canonical integration, use the repository's
existing manuscript build and verification workflow and create fresh
receipts for the changed manuscript. Preserve the original bundle's
receipts as records of the delivered computations. In particular:

- Exact golden and depth scripts certify finite algebraic operations;
  the infinite golden support bound also depends on the cited theorem.
- Numerical kernel, boundary, moment, and canonical-ladder replays remain
  diagnostics with the error scope stated in their records.
- The proposed angular-monotonicity and correction-polynomial statements
  remain conjectures. The existing `S_6` special-value conjecture also
  remains open.

The article supplies ordinary mathematical proofs and finite exact
certificates. Integration into a repository named ProveIt does not by
itself turn those proofs into proof-assistant formalizations.
