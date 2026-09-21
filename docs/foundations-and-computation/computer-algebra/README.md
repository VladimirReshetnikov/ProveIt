# Surreal and Surcomplex Numbers in Symbolic Computer Algebra

**Exact Representation Tiers, Effective Cores, Certified Supports, Analytic and
Contour Layers, Branch and Phase Conventions, and Three Delivered Wolfram
Prototypes**

A single merged research report, 95 pages, built from three independently
written source articles that answer the same question: *which surreals and
surcomplexes admit exact finite representation in a computer algebra system,
which operations on them terminate, and how should Wolfram Language be
extended?*

---

## What this report is

All three sources give the same architectural answer — not one universal numeric
type but a **layered family of exact domains with separately advertised,
independently queryable capability contracts**: an aggressively decidable
algebraic core surrounded by explicitly partial extensions. All three separate
exact denotation from effective coefficient access from decidable
equality/order from certified approximation.

Roughly the first third of each source is genuine duplication; the remaining
~60% of the combined page count is single-source. Printed separately the three
read as three overlapping drafts. Merged, they are one report whose three
specialist halves do not otherwise exist in one place.

The merge rule was **union, not selection**:

* A result all three prove is printed once.
* A result two prove by genuinely different routes keeps **both**, marked as
  such (the zero-test obstruction has two reductions with different morals; the
  finite-grid functional has two independent constructions; the analytic
  observable `e^z mod (z^2 - t)` has two routes).
* Anything one reached that the others did not **survives**.
* **Every honest limitation survives.** Dropping a non-claim would silently
  upgrade the report's apparent strength, and is the worst failure available in
  a merge of this kind.
* Nothing is strengthened beyond what a source proves.

## Contents

| Path | What it is |
|---|---|
| `article.tex` | The merged report. Standalone LaTeX, internal `thebibliography` (40 entries), no external `.bib`, no graphics. Every `\label` carries the prefix `cas:`. |
| `article.pdf` | Built output (95 pages). |
| `sources/` | The three source articles, their READMEs and one verification record. **Ships verbatim.** |
| `code/` | The executable files of all three delivered prototypes. **Ships verbatim, including the defective one.** |
| `data/` | The recorded verification reports of the prototypes. **Ships verbatim.** |

## Which archives it came from, and what each contributed

| Member | Archive | What it contributed to the merge |
|---|---|---|
| **04** | `layered-exact-representations-and-wolfram-adapter` | **The spine, plus the obstruction, polynomial-root and host-audit half.** Section order and table apparatus; all three negative results (zero test, support admissibility, the high-rank leading-term/sign obstruction with its rank-one contrast); the effective core with both closures and the rational-exponent refinement inside one theorem; the grid lemma in the construction that is actually exercised in code; the initial polynomial, Newton profiles, Hensel clusters and sharp univariate root-error thresholds; the four incompatible "infinitesimals"; the Conway-monomial vs generic-power collision; the residue-vs-trace pairing distinction; the blind-substitution failure; the 14-citation Wolfram documentation audit with its self-correction on `Root`'s scope; the notation and reproducibility appendices. |
| **05** | `gaussian-rational-monomial-wolfram-prototype` | **An entire analytic-geometry, residue and contour half** that 04 lacks, plus the only positive decidability result in the group. The six promises (refining the others' four); the ISSAC 2026 D-algebraic transseries zero-test with its hypotheses intact; the radius-free Hahn-germ algebra with `H(z)` and the `A_1` non-membership example; evaluation, translation and finite jets; Weierstrass preparation/division as operator algorithms with three executability caveats; normal forms, multiplication matrices, the perturbed residue and the trace identity; the two-scale coupled system and the separating determinant; algebraic periods, microscopic rescaling, the separating torus, Stokes as a certificate rewrite, the three-circles example; the multivariate root-separation certificate; the Archimedean impossibility proof and the three numerical request kinds; the serialization code-execution risk; the simplest-number cut semantics; the finite-union grid definition. |
| **02** | `capability-tiers-and-rational-hahn-kernel` | **An entire trigonometry, branch and phase half** that neither 04 nor 05 has, plus the capability-contract framing. The finite-angle circle and the exact cut-free phase; the Cayley coordinate, used twice; the canonical strips with `Sin(iω)` canonical while `sin(ω)` is not; `arctan(ω)` needing no infinite phase; the strip algebraization with the 2n root bound; the positivity-unsoundness example with the Cayley and Fejér–Riesz remedies; near-tangency valuation loss; the **complete classification of circular group-law extensions by characters**, with its converse and the infinite-period proposition; the two-logarithm branch analysis with its policy tokens; the Π⊕Z floor construction; Lambert W as an exact implicit constructor; the exp/log splits and why the naive series fails at a purely infinite part; `st` vs `fin` non-multiplicativity; the three-kinds-of-power constructor list; the five-valued result protocol with named standing obligations; the "10⁻⁶ specialization is a simulation" framing. |

Six distinct supplied research manuscripts stand behind the three articles, one
of them in **two different revisions**: the surcomplex analysis manuscript in
revision (2) for 02 and revision (3) for 04 and 05. The report names all six and
attributes every imported result to the specific manuscript and revision that
supplies it; it never writes "the supplied manuscript" in the singular. Only 02's
archive bundled its sources; those two files are already committed elsewhere in
this repository and are cited at their paths rather than re-shipped.

## The central hazard, and how the report guards against it

**There are three shipped Wolfram packages here, not one.** They invite
collapse: two are near-anagrams of each other (`RationalHahn.wl` in 02,
`HahnRational.wl` in 05), two export *six identical public symbol names* with
incompatible signatures, and all three are described in their own source
articles as implementing "the effective rational monomial core".

The report **never writes "the prototype"**. Section 17 names all three and
gives each its own envelope subsection, followed by a comparison table with a
row per divergent property, an explicit symbol-collision warning, four
cross-attribution warnings, and a shared-boundaries subsection.

| | **RationalHahn** (02) | **SurrealCASCore** (04) | **HahnRational** (05) |
|---|---|---|---|
| Coefficient field | **Q only** — no `i` anywhere | Q(i) | Q(i) |
| Exponent lattice | Z^d | **Q^r — rational, exercised** | Z^d |
| Coordinate significance | **REVERSED** (highest index first) | first coordinate most significant | first coordinate most significant |
| Data model | reduced quotient | canonical sparse sum **+ deliberately unreduced fraction** | reduced quotient |
| Standard part | yes | **no** | yes |
| Conjugation / Re / Im / \|z\|² | **none at all** | conjugation only | all four |
| gcd-reduced fractions | yes | **no** (`REqual`, not `SameQ`) | yes |
| What was executed | definitions submitted as code; 31/34 then three corrected | real files `Get`-loaded; 110/110 | `Get[StringToStream[…]]`; 88/88 |

Any sentence asserting a union of these capabilities is **true of no delivered
artifact**.

### The variable-order convention is reversed between two of them

02 lists variables **least**-significant-valuation first; 05 lists them
**most**-significant first, and 05's own README warns that a reversed variable
list is a different parent. The report flags this wherever both conventions
appear (§17.4.4, Appendix C), quotes each kernel's comparison in that kernel's
own convention, and never rewrites them into a common form. **A reader who
carries one convention into the other gets every inequality backwards.**

### Proposed architecture is kept apart from delivered code

All three articles propose object layers named `SurrealDomain`, `ExactSurreal`,
`CertifiedHahn`, `HahnParent`, `AnalyticGerm`, `CoherentLift`, and more — and two
of them propose the **same head with different argument shapes**
(`SurrealDomain` in 02 and 04; `AnalyticGerm` in 02 and 05). **Nothing of any of
those names exists in any shipped file.** Section 16 opens with an explicit
scope block, uses proposal-voice verbs only, prints the three syntax sketches
side by side with both head collisions flagged, and prints all three result
protocols rather than picking one. No capability from an architecture table is
reported as implemented anywhere in the report.

## What is NOT claimed

The report carries the deduplicated union of all three sources' honest-limitation
lists. In summary:

* **No universal surreal simplifier, no complete surcomplex analytic system, no
  complete surreal CAS.**
* No complete zero/equality algorithm for arbitrary computable coefficient
  streams; no total support-admissibility validator; no universal leading-term or
  sign algorithm for high-rank program-described grid series, even under a
  nonzero promise.
* The real-closure theorem establishes *implementability*, not acceptable
  complexity. Quantifier elimination is a sound foundation, not a guarantee of
  low cost.
* A finite valuation-cutoff request need not have a finite term-list answer. No
  algorithm prints an infinite cutoff prefix as a finite list — an
  output-representation limitation, not poor complexity. No time budget turns
  the halting reductions into decision procedures.
* The grid functional is **not** an order embedding of the higher-rank value
  group into Q or R, and must never replace the lexicographic valuation.
* Cited literature (Poonen, Gonshor, van den Dries–Ehrlich, Berarducci–Mantova,
  Mantova 2026, Bagayoko–van der Hoeven, Bournez–Guilmant, Costin–Ehrlich,
  Richardson, Chen–Fang–van der Hoeven) is carried as **semantic theorems for
  specified classes**, not as universal decision algorithms or finite encodings.
  The 2026 D-algebraic transseries zero-test holds only under its
  effective-field, transbasis and solution-selection hypotheses.
* All-scale rigidity is a **category boundary**, not a prohibition on
  transcendental surreal functions; no global atlas is claimed implemented.
* **No canonical infinite circular phase.** The trivial character
  (`sin_0 ω = 0`) is a convention and never a default. 02's character
  classification is complete *within the trigonometry manuscript's framework*
  and is **not** extended to SA's `E_α` family; `E_α` is an explicit family
  demonstrating nonuniqueness, carried with both carriers' explicit non-claims
  of uniqueness.
* Host prohibitions: never redefine `Infinity` to mean ω; do not mark surreal
  wrappers `NumericQ`; `Normal` discards omitted-order data and is not a proof;
  `PossibleZeroQ` is documented as heuristic and is never a proof of
  (non)vanishing; do not globally unprotect `Plus`/`Times`/`Power`.
* Each package's non-implementation list **stands separately and is not pooled**.
  Rejection by a backend means that core does not implement that representation,
  not that the value cannot be defined. None of the three is a hardened parser;
  forged internal heads are outside contract.
* **Test counts are not additive** — not 34+110+88 for Wolfram, not 69+323 for
  Python. Different suites check different things.
* **Nothing here is machine-verified.** No Lean file, formalization blueprint or
  formalization audit exists in any of the three packages, and no git commit,
  Lean toolchain or mathlib revision is pinned anywhere. The executed checks are
  exact finite algebra and formal-series checks only.
* Compatibility with Wolfram versions other than 15.0.1, and with Mathics, was
  not tested.

## What was executed, and what was independently reproduced

The report keeps these two things apart (§18).

**Recorded by the archives** — all three on the same connected evaluator, the
same kernel (*Wolfram Language 15.0.1 for Linux x86 (64-bit), July 2, 2026*),
the same date (September 21, 2026), with **no local installation exercised by
any of the three**; two of them additionally under Python 3.13.5 / SymPy 1.14.0.
Each record keeps its own disclosed imperfection: 02's 31/34-then-corrected run
plus an uncounted unevaluated identity plus its warning disclosure; 04's
105-checks-with-warning exploratory run; 05's message-emitting preliminary run.

**Independently reproduced for this merge**, on this machine, on
*Wolfram 15.0.1 for **Microsoft Windows** (64-bit) (July 2, 2026)* — the same
release and build date on a different platform — with **Python 3.14.4 / SymPy
1.14.0**, so the Python results reproduce across a minor Python version too:

| Package | Wolfram recorded | Wolfram reproduced | Python recorded | Python reproduced |
|---|---|---|---|---|
| **RationalHahn** | 34 checks, corrected suite | **does not parse as shipped** (12/34); **34/34** after a one-character fix | — | — |
| **SurrealCASCore** | 110/110 | **110/110** | 69/69 | **69/69** |
| **HahnRational** | 88/88 | **88/88** | 323/323 | **323/323** |

Every recorded claim reproduces.

### The one real defect

`code/02-capability-tiers-and-rational-kernel-rationalhahn.wl` **does not
parse**. `RHInverse` opens an `If[` that is never closed, and the kernel reports
`Syntax::sntue: Unexpected end of file`. Running the shipped driver unrepaired
returns `Checks -> 34, Passed -> 12` — the twelve passing checks being exactly
the ordinary `Series`/`Together`/`Simplify` identities that never call the
kernel. **The fix is one character** (`...a[[1]]]];` for `...a[[1]]];`), after
which the same driver returns 34/34 with no warnings.

So, as delivered, that archive's "expected 34/34 local run" is not merely
unverified but currently **impossible**. This is consistent with — and explains —
its own verification record, which states that the definitions were submitted as
code and that the local package path was never loaded into a separately
installed kernel: the package was never `Get`-loaded because it *cannot* be. The
unparseable file **ships verbatim here**; the report states the defect, gives
the one-character repair, and repeats the archive's `wolframscript` instruction
only together with that repair.

02's README also lists `SHA256SUMS.txt`. That is not a defect in the archive,
which did ship one. This repository carries no checksum manifests, so it was
removed on unpacking, and the verbatim README still names it.

04's and 05's packages both `Get`-load cleanly and their reported numbers are
the numbers you get from running their own harnesses.

## How to build

```sh
cd docs/foundations-and-computation/computer-algebra
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

Standard TeX Live or MiKTeX with the packages listed in the preamble. No
bibliography processor, no external graphics, no data files. The final build is
clean: **0 errors, 0 warnings, 0 undefined references, 0 undefined citations, 0
multiply-defined labels, 0 duplicate PDF destinations, 0 overfull boxes**,
95 pages.

## How to re-run the prototypes

Do not modify `code/`. The files there carry `02-`, `04-` and `05-` prefixes,
while each harness expects its archive's own basename, so copy them to a scratch
directory under those original names first — `RationalHahn.wl`, `Checks.wl`,
`RunChecks.wl`; `SurrealCASCore.wl`, `TestCore.wls`, `verify_examples.py`;
`HahnRational.wl`, `test_HahnRational.wl`, `verify_examples.py`. `RationalHahn.wl`
also needs the one-character repair of the report's §18.3 before it will load.
Then, from that scratch directory:

```sh
# RationalHahn (02) — apply the one-character repair to the COPY first
wolframscript -file RunChecks.wl            # 34/34 after the repair

# SurrealCASCore (04)
wolframscript -file TestCore.wls                 # 110/110
python verify_examples.py                        # 69/69

# HahnRational (05)
wolframscript -file test_HahnRational.wl    # 88/88
python verify_examples.py                   # 323 exact checks
```

Randomized cases use `SeedRandom[20260921]` (Wolfram) and
`random.Random(20260921)` (Python). Run the 02 suite in a fresh kernel or a
disposable context: its check file uses named global variables and the package
rejects variables that have already evaluated to nonsymbolic values.

## Structure of the report

1–3 the layered answer, the objects software must distinguish, and the limits
of finite representation (countability, both zero-test reductions, support
admissibility, the high-rank obstruction, and the positive counterweights) ·
4–7 the representation taxonomy, the effective core with its three
specializations, certified supports and the grid lemma in two constructions,
and precision as a mathematical type · 8–11 polynomial algebra and root
clusters, exact functions in four separate analytic categories, finite quotient
algebras and residues, integration and contour operations · 12–14 exponentials
and transserial scales, surcomplex angles/branches/infinite phases, and the
three derivative operators · 15–16 host integration and the proposed (not
delivered) architecture · 17–18 the three prototypes and what was actually
executed · 19–21 priorities, the capability matrix, and conclusions ·
Appendices A–D: the merged source audit with an origin column and a preserved
"what is not inferred" column; minimal backend contracts; notation including
the per-kernel coordinate conventions; and reproducibility with the defect note
and three separate run instructions.
