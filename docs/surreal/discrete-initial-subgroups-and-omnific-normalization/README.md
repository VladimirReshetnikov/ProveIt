# Discrete Initial Groups and Omnific Normalization

**Sign-tree surgery, a sharp image classification, and an Ehrlich–Kaplan question**
Single-source research report, 23 September 2026, written from one manuscript
(batch 28, manuscript 09), placed in `c6359e4`. AI-assisted draft prepared for
Vladimir Reshetnikov.

```
article.tex        the report, standalone LaTeX with an internal bibliography
article.pdf        the compiled report, 29 pages
README.md          this guide
source_audit.md    the manuscript's source and verification audit, as delivered
code/
  verify.py        finite regression checks (Python 3.10+, standard library only)
  build.sh         the delivered build script (see "Rerunning the checks": run it only on a copy)
data/
  verification_report.json   recorded run of verify.py: PASS, 450,862 assertions
```

Every label in `article.tex` carries the prefix `isg:`; the report has 84
labels. The 69 labels of the delivered manuscript were given the prefix during
this write, before anything cited them (for example `thm:A` is now
`isg:thm:A`), and 15 labels were added: the new sections
(`isg:sec:conventions`, `isg:sec:provenance`, `isg:sec:nonclaims`,
`isg:sec:conclusion`) and previously unlabelled statements (among them the
questions `isg:q:*` and the corollaries `isg:cor:relative`, `isg:cor:linear`).
The source manuscript itself, its PDF and its delivery README are not shipped;
`code/`, `data/` and `source_audit.md` are byte-identical to the delivery.

## Status

The report proposes an **affirmative answer** to a published question of
Ehrlich and Kaplan: *is every discrete initial subgroup of `No` isomorphic to an
initial subgroup of `Oz`?* It is Question 2 of arXiv:1512.04001v1 (Section 9,
printed page 18) and Question 9.1 of the journal version, *J. Symbolic Logic* 83
(2018), 617–633.

This is a **proposed solution in an unrefereed AI-assisted draft**. When the
manuscript was placed in the collection, every step of the argument was
checked by hand and no gap was found (Section 11.5). That check is not a
refereeing. The literature search, the manuscript's and the placement
review's, was **targeted, not exhaustive**; no prior resolution was found,
which is limited evidence. No priority is claimed and nothing is verified in
Lean.

The whole argument rests on one imported result, the Ehrlich–Kaplan criterion
for initial subgroups (arXiv v1 Theorem 1, journal Theorem 5.1; Imported fact
2.2 here). It is used in its concrete form: the *specified canonical
normal-form image* is initial. The journal statement says this outright
("via the canonical isomorphism"); in the arXiv version it is the content of
the sufficiency proof. The criterion was checked as a statement against both
texts, not re-proved.

## Numbering of the cited paper

The article uses the arXiv v1 numbering throughout (as the manuscript did).
The correspondence with the journal version was read at placement in the
author-hosted text of the journal version (the publisher's typeset pages were
not compared) and is printed in Section 1.1:

| arXiv v1 | journal | role here |
|---|---|---|
| Lemma 3 | Lemma 5.1 | initial subgroups of `R` (Imported fact 2.3) |
| Theorem 1 | Theorem 5.1 | the initiality criterion (Imported fact 2.2) |
| Proposition 9 | Proposition 5.2 | shape of the least positive element |
| Question 2 | Question 9.1 | the question addressed |
| Question 3 | Question 9.2 | the initial-monoid problem, not addressed |

The delivered `source_audit.md` says that no equivalence of numbering between
versions was assumed; that remains true of the manuscript, and the table above
is the report's addition.

## What the report claims

Let `A ⊆ No` be a nonzero discrete initial additive subgroup. *Initial* means
closed under proper sign-sequence prefixes; *isomorphic* means as ordered
abelian groups.

- **Bottom structure** (Proposition 3.2, Corollary 3.3). The least positive
  element is `ε = 2^(−n) ω^(−α)` for unique `α ∈ On`, `n ∈ N`; the exponent
  class has minimum `p = −α`, the bottom coefficient group is `2^(−n) Z`, and
  every `D ω^(−β)`, `β < α`, lies in `A` (`D = Z[1/2]`).
- **Root relocation** (Definition 4.1, Theorem 4.4). An explicit order
  isomorphism `Θ_α` from the cone `[−α, ∞)` onto `No_{≥0}` sends `p` to `0`
  and satisfies `Pred(Θ_α x) = Θ_α[Pred x ∪ {p}]` for `x > p`; right ancestors
  are preserved away from `p`, and the right ancestors of `p` itself are lost
  exactly (Remark 4.5). Inverse initiality holds exactly when the spine
  `{0} ∪ {q_β : β < α}` is present (Proposition 4.7), `q_β = +⌢−^β`.
- **Ambient transport** (Theorem 5.2). The map `N_{α,n}`, which reindexes
  exponents by `Θ_α` and multiplies only the bottom coefficient by `2^n`, is a
  real-linear order isomorphism of Hahn spaces that preserves support order
  types, leading truncations and set-indexed strong summability in both
  directions.
- **Theorem A (omnific normalization)** and **Corollary 6.2**. `N_{α,n}`
  restricts to an ordered-group isomorphism of `A` onto an initial subgroup
  `H ⊆ Oz` with `N(ε) = 1`. Hence every discrete initial subgroup of `No` is
  isomorphic to an initial subgroup of `Oz`: the proposed answer.
- **Theorem B (sharp image classification).** For fixed `α, n`, the images are
  exactly the initial `H ⊆ Oz` containing the dyadic-spine group
  `K_α = Z ⊕ ⊕_{β<α} D ω^(q_β)` (Lemma 7.1); the correspondence preserves and
  reflects inclusion. Counterexamples `H = Z` and `H = Z + Zω` at `α = 1`
  show that both the exponent and the coefficient part of the condition are
  needed (Section 10.5).
- **Extremal groups and scales** (Theorem 7.3, Corollaries 7.4, 7.6). The
  smallest and largest initial groups with least positive element `ε` are
  `L_{α,n}` and `M_{α,n} = ε Oz`, with images `K_α` and `Oz`;
  `|A| ≥ max(ℵ0, |α|)`, attained; and `N^(−1)[H]` is initial exactly for
  `α ≤ d(H)`, the dyadic-spine depth.
- **Theorem C (bottom cyclic layer)** with Lemma 8.1 and Proposition 8.3.
  `Zε` is convex, `A ≅ B ×_lex Z` for an explicit initial `B ⊆ No` realizing
  `A/Zε`, and the splitting is canonical relative to the normal forms. Finite
  iteration follows (Corollary 8.4).
- **Suspension** (Theorem 8.5, Corollary 8.6). `B ↦ Z ⊕ σ_*[B]` is an
  inclusion-preserving bijection between initial subgroups of `No` and nonzero
  initial subgroups of `Oz`; a nonzero discrete ordered group is initially
  realizable iff its quotient by the least positive cyclic subgroup is and the
  extension splits.
- **Surcomplex modules** (Theorem 9.2, Corollary 9.3). The coordinatewise map
  is a `Z[i]`-linear isomorphism `A[i] → H[i] ⊆ Oz[i]` with the same exact
  range; integral and Gaussian-integral linear systems transport exactly.
- Worked examples (Section 10): Ehrlich and Kaplan's own example
  `D + Z ω^(−1)`, where the construction recovers their map `d + mω^(−1) ↦ dω + m`;
  why scalar rescaling (`½Z + Zω`) and exponent translation (an exponent class
  containing `ω`) fail; a support of order type `ω + 1`; failure of
  multiplicativity.

## What the report does not claim

Section 12.1 collects every limitation of the manuscript and its audit as
N1–N15; each also stands at its place in the text. In brief:

- The solution is **proposed, unrefereed**, with no certified correctness,
  novelty or priority; the placement check is not a refereeing (N1). The
  literature and repository searches were targeted; a question posed in 2015
  and 2018 is not thereby shown to have been open on the review date (N2).
- The Ehrlich–Kaplan criterion is imported, not re-proved, and is never
  replaced by the false shortcut that an initial exponent class suffices (N3).
  The two-level example, the criterion, the classification of initial real
  groups and Conway normal forms are not claimed as new (N4).
- `N_{α,n}` is **not** a simplicity isomorphism (already `½Z → Z` cannot be),
  not multiplicative, not norm preserving, and does not fix ordinary constants
  (N5); `Θ_α` is not an exponent-group homomorphism, and Proposition 4.8 bounds
  exponent lengths, not birthdays (N7). Strong sums live in the ambient spaces,
  with no internal summation on `A` (N8). `α` is not an invariant of the abstract
  group, and uniqueness in Theorem B is relative to the fixed map (N9).
- No classification of all ordered abelian groups with initial embeddings; the
  initial-monoid problem (arXiv Question 3, journal Question 9.2) is not
  addressed (N6). No claim that every convex quotient is initially realizable,
  and no claim at limit stages of iteration (N10).
- The surcomplex statements are Gaussian-linear and coordinatewise only: no
  field isomorphism, no simplicity relation on `No[i]`, no modulus (N11).
- The finite checks do not verify limit cases, arbitrary Hahn supports, the
  imported criterion or the absence of transfinite gaps; building the PDF
  establishes its integrity, not its correctness (N12). No Lean formalization
  or Lean build (N13). The manuscript's repository review was targeted and the
  argument relies on no repository manuscript (N14). The questions of Section 12
  are not claimed to be published open problems (N15).

The article's own open questions are Questions 12.1–12.4 (other convex
quotients, limit iteration, multiplicative compatibility, formal certification
and uniqueness).

## Relation to neighbouring reports

No other report names Ehrlich–Kaplan Question 2 / 9.1, and none treats initial
subgroups: at placement, a search of `docs/` and of the Lean sources for
"initial subgroup", "discrete initial" and "discretely ordered initial" found
nothing outside this directory.

- **[omnific-diophantine-geometry](../omnific-diophantine-geometry/)** and
  **[set-sized-quotients-of-omnific-integers](../set-sized-quotients-of-omnific-integers/)**
  study the ring `Oz = Z ⊕ Π`. This report uses the same `Oz`
  (`odg:def:rings`, `osq:eq:Ozdef`), its discreteness (`odg:prop:units`) and the
  constant coefficient `ct` (`osq:lem:ct`), but only additively: its groups
  `H ⊆ Oz` are additive subgroups and its normalization is not multiplicative.
  The Diophantine report cites a *different* Ehrlich–Kaplan paper, *Surreal
  ordered exponential fields*, Lemma 11.1 (the initial integer part of an
  initial subfield; status note after `odg:thm:floor`); there is no overlap or
  conflict. Its "initial forms" (`odg:prop:initial`) are leading forms, a
  different use of the word.
- **[foundations](../../foundations-and-computation/foundations/)** cites
  Ehrlich–Kaplan II as background on initial embeddings next to its sign-tree
  categoricity (`found:sub:signtree`), and has `Oz = Π ⊕ Z` as
  `found:eq:omnific`.
- **[definable-surreals-and-omnific-integers](../../foundations-and-computation/definable-surreals-and-omnific-integers/)**
  cites Ehrlich–Kaplan II for simplest separators (`dsn:sec:foundations`, where
  "initial" is defined as here). Its maximal initial elementary exponential core
  (`dsn:thm:core`) concerns initial *subfields* of definable surreals; related
  in spirit, no overlap.
- The symbols `Θ_α`, `Ψ_α`, `q_β`, `N_{α,n}` are local (Section 1.4) and
  unrelated to theta series or the nome `q` of the surcomplex reports.

No `isg:` statement has a Lean implementation mapping in the
[formalization ledger](../../FORMALIZATION.md).

## Provenance

One manuscript, *Discrete Initial Groups and Omnific Normalization* (24 pages,
23 September 2026), delivered with a README, `source_audit.md`, `verify.py`,
`verification_report.json` and `build.sh`. With one source there was no merge
and no choice between sources. The manuscript has **no pinned commit**; it
records the blobs it read (`README.md` `391afd7…`, `docs/FORMALIZATION.md`
`6a89497…`) and a later commit `173eb52`, an ancestor of the placement commit
`c6359e4`. It makes no claim about the content of any report, so no stale
statement had to be corrected.

The write added, without changing any mathematical statement, proof or
example: the `isg:` prefix; the journal numbering and the wording of journal
Theorem 5.1 (Sections 1.1 and 2.2); the conventions shared with the collection
(Section 1.4); the provenance and placement-review subsection (Section 11.5); the
collected non-claims (Section 12.1); a definition of `ct`, which the manuscript
used undefined; the shipped file names; and labels on previously unlabelled
statements. The build now names each theorem-like environment correctly in
cross-references (in the delivered source every reference to a lemma,
proposition, corollary, remark or imported fact printed as "theorem"), keeps
the title page on one page and has no duplicate title-page destination.

The citations of Kaplan's thesis (Sections 6.2, 7.1) and of the Oberwolfach
Report 60/2016 (pp. 3355–3356) are the manuscript's and were not re-checked at
placement.

## Build

From this directory, with a TeX distribution providing pdfLaTeX, `newtx`,
`microtype`, `tikz`, `tcolorbox`, `aliascnt`, `hyperref` and `cleveref`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 29 pages with no errors, warnings, overfull or underfull boxes,
undefined references, multiply defined labels or duplicate destinations. Remove
the auxiliary files afterwards (`latexmk -c`).

## Rerunning the checks

**Run the checks only on a copy.** `code/verify.py` writes its report to
`--output`, whose default is `verification_report.json` *in the current
directory*; the delivered `build.sh` calls it with exactly that name, and in the
delivered flat layout both overwrote the shipped record (and `build.sh` also
rebuilt the PDF in place). In this directory `build.sh` changes into `code/`,
writes a stray `code/verification_report.json`, and then stops, because it
compiles `omnific_normalization.tex`, the delivered name of `article.tex`.

```sh
cp -r . /path/to/scratch/isg && cd /path/to/scratch/isg
python code/verify.py --output rerun.json
python -c "import json; print(json.load(open('rerun.json')) == json.load(open('data/verification_report.json')))"
```

The placement rerun passed with 450,862 assertions in about 2 seconds, and the
comparison printed `True`. To use `build.sh`, first restore the delivery layout
in a scratch directory: put `code/verify.py`, `code/build.sh` and
`data/verification_report.json` side by side with `article.tex` copied to
`omnific_normalization.tex`, then run `sh build.sh` there.

The suite covers finite sign words up to length seven, all 677 prefix-closed
trees of depth at most three (the empty tree included), inverse-spine and
coefficient-spine conditions in those finite ranges, and 1,500 random pairs of
finite rational normal forms (seed 20260923). It is a regression test of the
formulas, not a verification of the transfinite argument.
