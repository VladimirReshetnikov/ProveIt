# Exact Precision and Algebraic Rigidity of Omnific Continued Fractions

**Full Hahn-field realization, valuation ideals, periodic codes, and surcomplex fibers**

This is a single-source research report dated 23 September 2026. It is built
from one manuscript, manuscript 09 of batch 33 (archive
`surreal_continued_fractions_research`, inner directory `surreal_cf_article`,
a 22-page PDF). The manuscript is pinned to repository commit `958b5c4`; the
archive was delivered in `73043eb` and placed in `aa9c891`. Author line:
AI-assisted research draft.

This directory holds one manuscript. It is not a merge: there was no second
source, and nothing was selected out of a larger body of work. Every result,
proof, example, question and limitation of the manuscript is printed. The
report is AI-assisted and unrefereed. **Independent proof review and
formalization are pending.**

```
article.tex             the report, standalone LaTeX with an internal bibliography
article.pdf             the compiled report, 31 pages (unnumbered title page,
                        contents pages i–ii, then pages 1–28)
README.md               this guide
proof_and_scope.md      the source's proof and scope self-audit, as delivered
source_audit.md         the source's attribution and repository comparison, as delivered
code/verify.py          the source's exact finite checks (Python, SymPy)
code/Makefile           the source's Makefile (delivered at the package root)
data/requirements.txt   the source's pin, sympy==1.14.0
data/verification.json  the source's recorded run of code/verify.py
data/build_and_layout.json  the source's record of its own 22-page build
```

`code/`, `data/`, `proof_and_scope.md` and `source_audit.md` are
byte-identical to the delivery. They were delivered under other paths:
`audits/proof_and_scope.md`, `audits/source_audit.md`,
`audits/verification.json`, `audits/build_and_layout.json`, and `Makefile` and
`requirements.txt` at the package root. The delivered README and PDF are not
shipped: this README replaces the delivered one, and `article.pdf` is a build
of this text. The package had no checksum manifest.

The shipped delivered files still use the delivery paths:

- the docstring of `code/verify.py` and the Makefile's `check` target write
  `audits/verification.json`, which is not a shipped path;
- the Makefile's `pdf` and `check` targets assume they run from the package
  root (`article.tex`, `code/verify.py`), so `code/Makefile` does not work
  from `code/`;
- `proof_and_scope.md` names `verification.json` without a directory, and
  the delivered README named `audits/proof_and_scope.md`,
  `audits/source_audit.md` and `audits/verification.json`;
- `data/build_and_layout.json` records the delivered 22-page build, with
  its table of contents on one page, not this 31-page build.

Every label in `article.tex` carries the prefix `ocf:`. The source's 77
labels are kept, unchanged after the prefix. Thirty-five were added, for 112
in all:

- new sections and subsections: `ocf:sub:known`, `ocf:sec:conventions`,
  `ocf:sec:collection`, `ocf:sec:nonclaims`, `ocf:sec:conclusion`,
  `ocf:sub:artifact`, `ocf:sub:formal`, `ocf:app:notation`,
  `ocf:app:report`, `ocf:app:onesource`, `ocf:app:pinned`,
  `ocf:app:literature`, `ocf:app:checked`, `ocf:app:suite`,
  `ocf:app:files`;
- existing unlabelled environments: `ocf:def:Oz`, `ocf:def:digits`,
  `ocf:def:ideal`, `ocf:rem:projection`, `ocf:rem:twocases`,
  `ocf:cor:convergence`, `ocf:rem:independence`,
  `ocf:cor:complexindependence`;
- the twelve research questions: `ocf:q:priority`, `ocf:q:subfields`,
  `ocf:q:nonperiodic`, `ocf:q:lagrange`, `ocf:q:simplicity`,
  `ocf:q:transfinite`, `ocf:q:integerparts`, `ocf:q:primary`,
  `ocf:q:surcomplex`, `ocf:q:effective`, `ocf:q:birthday`, `ocf:q:formal`.

No theorem, section or equation number changed: the `.aux` numbers of all 77
source labels were compared with a build of the delivered text. No `ocf:`
label has a Lean mapping in the [formalization ledger](../../FORMALIZATION.md).

Text added when the manuscript joined the collection is marked `[write]`.
Sections 1.4, 1.5 and 15 and Appendix B are new. Short `[write]` notes sit
on the title page, at the end of Section 1.1, after Lemma 2.2, after
Theorem 8.4, after Remark 10.2, in Sections 12.1 and 12.2, after research
question 12 and in the notation table of Appendix A. No mathematical
statement was changed.

## Setting and notation (Section 1.4)

Digits are Conway omnific integers `a_0 ∈ Oz` and `a_n ∈ Oz`, `a_n ≥ 1` for
`n ≥ 1`; the sequence has length exactly `ω` and every index is an ordinary
natural number. The floor is the exact omnific floor. `q_n` are the continuant
denominators and `d_n = deg q_n = Σ_{j=1}^n deg a_j` (the first digit never
contributes). `deg` is the greatest growth exponent and `v = −deg`, as in
[NOTATION.md](../../NOTATION.md); a *large* valuation means a *small* element.
`K_G = R((ω^G))` is the **full** Hahn field on a set-sized additive subgroup
`G ⊆ No` (not necessarily divisible), `Oz_G = K_G ∩ Oz`, and
`K_a = Q(a_0, a_1, …)` is the countable field generated by the digits.

**Renamed symbol.** The ring of finite surreals, written `𝒪` in the source,
is written `𝒪_fin` here, as in the omnific Diophantine report, where `O` is an
orthogonal group and `𝒪_𝕜(Γ)` a Hahn valuation ring. Its complex counterpart
`𝒪_C = 𝒪 + i𝒪` is written `𝒪_fin[i]`. `𝔪` is the infinitesimal ideal. No
normalization changed.

Watch for these readings:

- **The precision ideal** `I_a = {0} ∪ {e : v(e) > 2d_n for every n}` is a
  convex ideal of the valuation ring `𝒪_fin`, inside `𝔪`. It is **not** an
  ideal of `Oz` or of `No`, not the purely infinite ideal `Π`, and not one of
  the ideals `I_κ` of `Oz` in the quotient report. "Prime" always refers to
  `𝒪_fin` (or `𝒪_fin ∩ K_G`).
- **`K_a` is not a Hahn field.** It is generated by the digits; `K_R` in
  Section 9 is `K_G` at `G = R`.
- **Fibre versus Fibonacci.** `𝓕(a)` (calligraphic) is the fibre; `F_k`
  (italic) are Fibonacci numbers.
- **Local letters.** `D` is an entry of the period matrix and, in the proof
  of Theorem 6.2, the lower set `⋃[0, 2d_n]`; neither is `D_0` or `D_*`. `E`
  is the period degree in Section 8 but a set-sized subfield in Lemma 7.1,
  Section 10 and Section 11. `t` is the variable of `Φ_n`, the period-fixed
  root of Theorem 8.1, and an ordinary index in (8.7): `E_t` is not `E` at
  the root. A bare `q ∈ Q` is a rational multiplier: `ξ + qδ` is not
  `ξ + q_n δ`. `C_n` are cylinders, `C` a matrix entry, `C_k` Catalan
  numbers. In Proposition 11.3, `a, b, c, d` are complex coefficients and `d`
  is not a degree. `κ` is a set cardinal, not the scale `κ` of the
  expanding-polynomial report. Section 1.4 lists every use.
- **Maps.** `Φ_n` is a finite prefix map, not the monomial lift `Φ_h` of
  the independent-copies report. The support projection `π_G` keeps the
  terms with exponents in `G`: additive, **not** multiplicative
  (`π_Z(ω^{1/2})² = 0 ≠ ω = π_Z(ω)`).
- **Topologies.** The continuants never converge in the order topology of
  the class `No` (Proposition 4.6) but do converge in the set `K_G` in the
  unique case (Corollary 5.5). No conflict.

## What the report claims

Theorem numbers are those of the built `article.pdf`; they agree with the
delivered PDF. Definitions, remarks and examples share the theorem counter,
so the floor lemma is Lemma 2.2 (after Definition 2.1).

- **Exact floor (Lemma 2.2).** `⌊x⌋_Oz` with the negative-infinitesimal
  correction: `⌊−e⌋ = −1` for `0 < e ∈ 𝔪`. This is the collection's
  integer-part theorem (see below).
- **Cylinders (Lemma 3.2, Proposition 3.3, Corollary 3.4).** Matrix and
  determinant identities, `q_{n+k} ≥ F_{k+1} q_n`; the prefix cylinder
  `C_n = Φ_n((1,∞))` is an open interval of width `1/(q_n(q_n+q_{n−1}))`
  with exact endpoint distances, and `𝓕(a) = ⋂ C_n`; the Conway cut of the
  endpoints realizes every code in `No`.
- **Exact fibre (Lemma 4.1, Lemma 4.2, Theorem 4.4).** A uniform two-step
  buffer `1/(4q_{n+2}²)` from both endpoints; `v(x − r_n) = d_n + d_{n+1}`;
  and **`𝓕(a) = x + I_a`** for every realization `x`. The fibre in `No` is a
  proper class (Corollary 4.5); continuants never converge in the order
  topology of `No` (Proposition 4.6).
- **Full Hahn realization (Theorem 5.1).** Every admissible code in `Oz_G`
  has a realization in `K_G`, unique iff `(2d_n)` is cofinal in `G_{≥0}`;
  no divisibility is needed. Proof: an ordinary real tail when degrees stop
  growing, otherwise support projection of a surreal realization.
  Corollary 5.4: some code is unique in `K_G` iff `G` has countable
  cofinality. Corollary 5.5: in the unique case the continuants converge in
  `K_G`.
- **Precision ideals (Proposition 6.1, Theorem 6.2, Corollary 6.3).** Every
  countable nondecreasing cut is realized; `I_a` is prime iff (P): for every
  `n` some `d_m ≥ 2d_n`; otherwise `ω^{−2d_n}` is a nonzero square-zero
  class; nilpotency index and a prime radical.
- **Algebraic rigidity (Lemmas 7.1, 7.2, Theorem 7.3).** Over `K_a`: at most
  one algebraic realization iff (P) and (V): some `2d_n ≥ D_0 = deg a_0`;
  otherwise the algebraic part of the fibre is empty or countably infinite,
  closed under rational translations inside one finite extension.
- **Periodic codes (Theorems 8.1, 8.2, Corollary 8.3, Theorem 8.4).** A
  period-fixed quadratic realization always exists; exactly one algebraic
  realization iff `E = D_* = 0` or `E > 0` and `D_* ≤ NE` for an ordinary
  `N`, otherwise countably many; a purely periodic code with positive first
  digit has exactly one; periodic uniqueness in `K_G` holds iff the period
  degree `E` is an order unit, so some periodic code is unique in `K_G` iff
  `G` has an order unit.
- **Examples (Section 9).** The golden ratio fibre `φ + 𝔪`; an initial
  scale invisible to a periodic tail; a nonreduced error quotient; the
  constant period `ω` with the Catalan expansion
  `ρ = ω + ω^{−1} − ω^{−3} + 2ω^{−5} − 5ω^{−7} + …`; a bounded cut whose
  rank-one boundary is attained but whose surreal boundary is not; and
  `G = ⊕ Q ω^j`, countable cofinality without an order unit.
- **Hidden independence (Theorem 10.1).** Every fibre in `No` contains
  algebraically independent families of every set cardinality over every
  set-sized subfield.
- **Surcomplex (Theorem 11.1, Corollary 11.2, Proposition 11.3).**
  Coordinatewise fibres `(x+iy) + (I_a + iI_b)`, an ideal of `𝒪_fin[i]` iff
  the two ideals agree; hidden independence; the exact precision transport
  `v_C(f(z+e) − f(z)) = v_C(ad−bc) + v_C(e) − 2v_C(cz+d)` for a small
  perturbation.
- **Research questions 1–12** (Section 13) and a proposed formalization
  route (Section 12.2).

## What the report does not claim

Section 15 collects every non-claim with its location: 26 from the source
(S1–S26) and 8 added when the report joined the collection (W1–W8). In brief:

- **Not new.** Basic nonuniqueness and large (proper-class) fibres are
  Roggeman's (1985); continuant identities, real periodicity, the periodic
  fixed-point mechanism and the radical argument are classical.
- **Priority and status.** Novelty and priority of the proposed
  classifications are not independently certified; no named longstanding
  problem is claimed solved; the questions are proposals; no referee review,
  no Lean file, the repository was not built.
- **Finite tests** check finite identities only, not the class-sized or
  arbitrary-support theorems, countable cofinality, the absence of all
  polynomial relations, the proof or novelty.
- **Scope.** Length exactly `ω`, no limit-stage continuation; no
  nearest-Gaussian-integer algorithm (Section 11 is coordinatewise only);
  realization only in *full* Hahn fields; `π_G` is not multiplicative; no
  algebraic existence for nonperiodic codes; no Lagrange converse; not every
  periodic itinerary is quadratic; the simplest separator is not claimed to
  be the period root; unrestricted fibres are never unique; countable
  cofinality does not imply an order unit; no proper-class transcendence
  basis, and the families of Section 10 are not definable or computable; no
  large cardinals, class-length recursion or proper-class cosets.
- **Added at the write.** (W1) no `ocf:` Lean mapping; only the floor is
  formalized. (W2) Lemma 2.2 is not new to the collection. (W3) the coset
  mechanism is credited to the independent-copies and bounded-support
  reports, and the comparison with the expanding-polynomial report is a
  parallel of shape, not a derivation. (W4) no named question answered.
  (W5) the source's repository statements are those of its pin (still
  true). (W6) reading the proofs at the write is not a proof review. (W7) a
  passing rerun certifies finite identities only. (W8) Roggeman's paper was
  not read for this report.

## Relation to the neighbouring reports

Section 1.5 gives these relations with labels. Nothing in the collection
treated surreal or omnific continued fractions before this report, and
Roggeman is cited nowhere else.

- **Integer part.** Lemma 2.2 is `odg:thm:floor` / `odg:eq:floor` of
  [omnific-diophantine-geometry](../omnific-diophantine-geometry/), also
  `dsn:prop:floor`, `cas:eq-floor`, and `onot:eq:floor` (where the
  omnific-notations report prints it once). It is printed once here, with
  the source's proof, as an independent re-derivation. The ledger marks
  `odg:thm:floor` **Proved** in `Surreal/Foundations/OmnificFloor.lean`; it
  is the only formalized ingredient of this report.
- **[expanding-polynomial-dynamics](../../surcomplex/expanding-polynomial-dynamics/)**
  (`epd:`). Its itinerary fibres are a centre plus
  `I_κ = {h : v(h) > nκ for all n}` (`epd:lem:ideal`, `epd:thm:fibers`), and a
  word determines one point iff `κ` is an order unit. Theorem 4.4 has the
  same shape for the omnific floor coding with an arbitrary countable degree
  cut; for a periodic code with `E > 0` and `Σ_{j<r} deg a_j ≤ NE`, `I_a` is
  that ideal at `κ = E`, and Theorem 8.4 is the same order-unit threshold.
  Independent proofs; neither report uses the other. The same
  countable-cofinality/order-unit line divides the trichotomy of
  [entire-functions-at-arbitrary-rank](../../surcomplex/entire-functions-at-arbitrary-rank/).
- **[independent-surreal-copies](../independent-surreal-copies/)** (`isc:`)
  and **[transcendence-over-bounded-support](../transcendence-over-bounded-support/)**
  (`bst:`). Theorem 10.1's support-coset argument is their standard
  mechanism (`isc:lem:slice`, `isc:thm:sliceddisjoint`, `bst:eq:projection`,
  `bst:lem:projection`), credited; `π_G` is `bst`'s coset projection at the
  zero coset.
- **Workspaces.** The set-sized Hahn workspaces are `K_G`'s; those of
  `found:thm:workspace` in [foundations](../../foundations-and-computation/foundations/)
  are the divisible case.
- **Unrelated.** `dyn:prop:cf` of
  [dynamics-and-normal-forms](../../surcomplex/dynamics-and-normal-forms/)
  concerns real continued fractions of a rotation number;
  `scale:eq:continuantval` of
  [matrix-scaling-at-surreal-scales](../matrix-scaling-at-surreal-scales/)
  concerns tridiagonal determinant continuants.
- **Questions.** None of the collection's named questions is answered. All
  twelve research questions here are new and open; question 12 can start
  from the proved floor.

## Provenance (Appendix B)

| Manuscript | Archive | Pin | Contributes |
|---|---|---|---|
| batch 33, 09 | `surreal_continued_fractions_research` (`surreal_cf_article`), "Exact Precision and Algebraic Rigidity of Omnific Continued Fractions", 22 pp. | `958b5c4865819bd55ea1f5ffc050282aea7ef570` | everything outside `[write]` |

- **Placement.** A new report, not an addition: the floor lemma is one
  imported ingredient of the Diophantine report, and the
  expanding-polynomial report shares only the shape of the fibre theorem for
  a different coding; no report names a question this manuscript answers.
  It is a surreal report because its fields are subfields of `No`.
- **Renamed symbols.** `𝒪 → 𝒪_fin`, `𝒪_C → 𝒪_fin[i]`.
- **Printed once.** Lemma 2.2 (the collection's integer-part theorem).
- **Merge and write additions.** Sections 1.4, 1.5, 15, Appendix B, the
  `[write]` notes listed above, and one corrected cross-reference: the source's
  "Theorems 6.2 and 6.3" in research question 8 names a theorem and a
  corollary (footnote there).
- **Repository statements at the pin.** The pin is an ancestor of `aa9c891`
  (71 commits earlier). The source's statement that the catalogue has no
  continued-fraction report is still true; no stale statement needed
  correction.
- **References.** A web search finds Roggeman's author-hosted record and
  PDF under the stated title; the paper was not read for this report and its
  journal was not established. Conway, Gonshor, Krishnan and Eberl were not
  checked.
- **Proofs read.** Every proof was read line by line at the write, with the
  buffer identity, the degree induction, the periodic valuation bound, the
  Catalan coefficients, the rank-one boundary and the order-unit example
  rechecked; no mathematical error was found. This is not an independent
  proof review.

## Build and reproduce

TeX Live or MiKTeX with pdfLaTeX, `latexmk`, newtxtext/newtxmath, amsmath,
amsthm, mathtools, geometry, microtype, booktabs, array, longtable, xcolor,
enumitem, fancyhdr, tcolorbox and hyperref. No external figures or
bibliography file.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

This build (MiKTeX) has 31 pages and no errors, LaTeX or package warnings,
undefined references or citations, multiply defined labels, duplicate
destinations, or overfull or underfull boxes; the delivered text builds
equally cleanly at 22 pages. A clean compile proves nothing about the proofs.

`code/verify.py` needs Python 3.10 or later and SymPy
(`data/requirements.txt` pins 1.14.0). It uses exact rational arithmetic,
finite generalized polynomials with rational exponents and SymPy identities,
with the fixed seed 20260923, and raises on the first failed check. It prints
its JSON report to standard output and **writes a file only when given
`--output`**; it never rewrites `data/verification.json` unless pointed at it.
Do not use `make check` from `code/Makefile`: it writes
`audits/verification.json`. Run it on a copy, from this directory:

```sh
python -m pip install -r data/requirements.txt
T=$(mktemp -d)
cp code/verify.py "$T"/ && (cd "$T" && python verify.py --output out.json > run.txt)
diff <(grep -v python_version "$T/out.json") \
     <(grep -v python_version data/verification.json)
```

(On Windows the written file has CRLF line endings; compare with
`diff --strip-trailing-cr`.) This was run for this report under Python
3.14.4 with SymPy 1.14.0: exit code 0, `"status": "passed"`, **81,256
assertions** in the same 20 categories with the same counts as
`data/verification.json` (among them 28,268 Fibonacci inequalities, 4,294
two-step buffers, 5,694 each of digit recovery, cylinder widths and endpoint
distances, 1,260 generalized-polynomial degree and determinant checks, and
50 Catalan coefficients). The only difference is the recorded Python version
(3.13.5 in the delivery). The checks cover finite instances only; they do
not implement `No` and do not test any class-sized or infinite-support
statement.

## Page counts

`article.pdf`: 31 pages (title page, contents i–ii, pages 1–28). The
delivered PDF, not shipped, had 22 pages.
