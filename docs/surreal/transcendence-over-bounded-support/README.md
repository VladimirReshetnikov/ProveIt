# Bounded-Support Hahn Arithmetic

**Cofinal descent, optimal support thresholds, and maximal transcendence**
Single-source research report, 22 September 2026, built from one manuscript
(item 07 of batch 19, a research draft prepared with ChatGPT). Its own
repository audit is pinned to `048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`; its
raw source and artifacts were placed in `30dfb4f`, and the editorial article
and first repository PDF were assembled in `ed88b8f`.

```
article.tex         the report, standalone LaTeX with an internal bibliography
article.pdf         the compiled report, 32 pages
README.md           this guide
research_audit.md   the manuscript's repository and literature audit, as delivered
code/  build.py          three-pass pdfLaTeX builder (expects the flat delivered layout, see "Build")
       coefficients.py   the explicit countable coefficient code; standard library only
       verify.py         exact finite regression checks; imports coefficients.py
data/  verification.json the delivered run: 3,163 assertions in 12 groups, all passed
       build_audit.json  layout audit of the delivered 24-page PDF (not of this PDF)
       manifest.json     SHA-256 digests of the delivered files (see "Provenance")
```

Every label in `article.tex` carries the prefix `bst:`. The source manuscript
itself is not shipped. The code and data files are the delivered bytes.

## What the report claims

Numbers refer to the built `article.pdf`. Throughout, `G` is a nonzero
set-sized ordered abelian group, `B_G(K)` is the ring of Hahn series in
`K((t^G))` whose support is **bounded above in G**, `F_G(K)` is its fraction
field, and `κ = cf(G)` is the least cardinality of a subset of `G` unbounded
above.

1. **The sharp support theorem, Theorem 5.3** (`bst:thm:independent`; preview
   Theorem 1.1). For `K` of characteristic zero there are a strictly increasing
   cofinal sequence `a_α` (α < κ) and positive integers `c_A(α)` such that
   the `2^κ` series `Y_A = Σ_{α<κ} c_A(α) t^{a_α}` (A ⊆ κ) are algebraically
   independent over `F_G(K)`. All have the one support `{a_α}`, of order
   type κ. The mechanism is a separated exponent system (Lemma 4.2), a
   support-band estimate (Lemma 4.4) and a finite-pattern coding lemma
   (Lemma 5.1) with integer-grid detection (Lemma 5.2).
2. **Optimality, Corollary 5.4.** The least support cardinality, and the least
   support order type, of an element transcendental over `F_G(K)` are both κ.
   So countable supports suffice exactly when `cf(G) = ℵ_0`.
   Corollary 5.5 (bounded perturbations) and Corollary 5.6 (`2^κ` independent
   elements in every valuation ball) follow.
3. **Exact degrees.** `trdeg_{F_G(K)} K((t^G)) = 2^κ` when `|G| = cf(G) = κ`
   and `|K| ≤ 2^κ` (Corollary 5.8), and `= 2^{ℵ_0}` for every nonzero
   `G ⊆ R` and `|K| ≤ 2^{ℵ_0}` (Corollary 5.9). The upper bounds are a
   separate cardinality count.
4. **Simultaneous descent, Theorem 3.2** (preview Theorem 1.2). For fields
   `K ⊆ L` and a nonzero **cofinal** subgroup `H ⊆ G`, `K((t^H))` and
   `F_G(L)` are linearly disjoint over `F_H(K)`, in any characteristic.
   Corollary 3.3: `F_G(L) ∩ K((t^H)) = F_H(K)`, relation ideals and finite
   algebraic degrees are preserved. Corollary 3.4: at an order unit `u`,
   `K((t^u)) ∩ F_G(L) = K(t^u)`. In characteristic zero cofinality is also
   necessary (Section 3.4, using Theorem 5.3).
5. **Explicit witnesses.** Corollary 4.6 (one lacunary series); Theorem 6.1:
   `Σ_{n≥2} q_j^n t^{n!u}` for multiplicatively independent `q_j > 0`, e.g.
   primes, are independent over `F_G(L)` for `L ⊇ R`; the integer family `W_A`
   of equation (18) is a continuum-sized independent family, each member
   computable relative to `A`.
6. **Rank structure, Section 7.** `B_G(K)` is a field iff `G` has no order
   unit, and is then the union of the Hahn fields over proper convex subgroups
   (Theorem 7.1); it is real closed or algebraically closed when `G` is
   divisible and `K` is (Corollary 7.2). With an order unit and `G` divisible,
   the top-rank presentation (Proposition 7.3) and the **imported**
   upper-support theorem of L'Innocente–Mantova (Proposition 7.4) give the
   units: support in one coset of the maximal proper convex subgroup
   (Corollary 7.5).
7. **Actual surreal numbers, Section 8.** Via `t^g ↦ ω^{-g}`: continuum many
   positive infinitesimals `η_A = Σ c_A(n) ω^{-n!}` and the explicit `η_p`,
   independent over the bounded fraction field `𝓕_C` of real-exponent,
   complex-coefficient series, with exact degrees `2^{ℵ_0}` (Theorem 8.1);
   for every infinite regular κ, in `G_κ = ⊕_{α<κ} Q ω^α`, `2^κ` positive
   infinitesimals `Σ c_A(α) ω^{-ω^{α+1}}` and exact degrees `2^κ` (Theorem
   8.2). Section 8.4: along the noncofinal embedding `R ⊂ Rω + R` every
   real-exponent series becomes a bounded-support coefficient.
8. **Conditional GCD descent, Appendix A.** *Assuming* the hypothesis
   `(GCD_{R,K̄})` that `B_R(K̄)` is a GCD domain, `B_H(K)` is a GCD domain for
   every nonzero `H ⊆ R` (Theorem A.1), which would answer the pre-Schreier
   question after Example 9.1.3 of L'Innocente–Mantova; a universal form of the
   hypothesis gives the GCD property at every divisible rank.

## What the report does not claim

No non-claim of the manuscript was dropped. The article states each at its
point of use; Section 10.3 and Appendix B collect the principal ones, and the
delivered `research_audit.md` repeats most of them. There are 24, grouped here.

**Status and verification (4).** Not refereed. No Lean implementation mapping for its results. The 30 standard statements
are listed in the collection's source inventory, which is not proof coverage. 3,163 is an assertion count, not a
count of theorems; finite checks do not prove any transfinite, cardinal or
summability statement. PDF byte-for-byte reproducibility is not claimed.

**Priority (5).** Proposed contributions only; the literature search was
targeted, not an exhaustive MathSciNet, Zentralblatt, thesis or
citation-network audit. The cofinality/nonrationality obstruction is
L'Innocente–Mantova's Proposition 2.4.5 and is **not** claimed new; their
Fact 2.1.1, Fact 2.4.2 and Proposition 3.5.1 are imported. The coding lemma,
linear-disjointness algebra, Hahn-field closedness and Conway normal form are
background. Gonshor's book was not freshly audited. The repository audit was
not line by line, the later revision `6e34651` it observed was not re-audited,
and a negative indexed search is not proof of absence.

**GCD appendix (3).** The hypothesis `(GCD_{R,K̄})` is **not** proved; no
unconditional answer to the pre-Schreier question and no resolution of
Conway's refinement conjecture. The external Lean project
`gaearon/conway-refinement` was read, not built or validated, and is not a
premise. Proving GCD would not remove the transcendental extension, and the
transcendence theorems do not use the appendix.

**Scope of the theorems (12).** Nothing is transcendental over all of **No**
or `No[i]`: every statement is relative to named set-sized subfields, and
"bounded" is relative to the named exponent group. A family of maximal
cardinality is not asserted to be a transcendence basis. The transcendence
degree for arbitrary `G` is not determined (`2^{cf(G)}` may be smaller than
the Hahn field's cardinality). Finite coefficient fields are not covered; the
positive-integer form is characteristic zero. No differential-independence
theorem. Hahn partial sums are not claimed to converge in the full fine
topology. The bounded-truncation remark after Corollary 5.6 is
information-theoretic, not an undecidability claim; the integer family is not
asserted to consist of computable streams; `coefficients.py` decides no
algebraicity question. The regularity of κ in Theorem 8.2 is genuine; no CH
or GCH is used. No arbitrary-rank supremum formula is assumed for units.
Density is not an algebraicity statement.

## Relation to the neighbouring reports

Section 9 of the article states this in full, with the labels it quotes.

**[tail-spans-and-differential-transcendence](../tail-spans-and-differential-transcendence/)**
(Section 9.1). Different base-field problems, neither implying the other.
There the base is a *full* Hahn field `M((t^Γ))` and transcendence comes from
the coefficients (`tail:thm:coefficient`, for `M` of characteristic zero: algebraic iff the coefficients
generate a finite extension of `M`); here the base keeps the coefficients and
transcendence comes from the support. The witnesses `η_A`, `η_p` here have
integer coefficients and exponents, so they are *elements* of that report's
base `Q((t^Q))`; conversely `√2 ∈ F_R(R)` is not in `Q((t^Q))`. At uncountable
cofinality a countable-support series `Σ √p_n t^{γ_n}` lies in the bounded
ring here but is transcendental over `Q((t^G))` there.
*Overlap:* both prove a relative transcendence degree `2^{ℵ_0}` with explicit
actual surreal witnesses and a separate cardinality upper bound
(`tail:thm:surreal`; Corollary 5.9, Theorem 8.1); both deny that maximal
cardinality means a basis; both show a noncofinal enlargement changing the
answer for the same surreal expansion (its `Q ↪ Q²` example in
`tail:thm:closure`, which loses algebraic approximability; Section 8.4 here,
which erases transcendence over the bounded base).
*Differences:* differential and analytic independence and the exact relation
classification (`tail:thm:tail`) are only there; the simultaneous descent theorem
and exact cofinality-dependent support threshold are only here. Its general
coefficient and tail-span theorems also allow arbitrary ordered groups. Its `(ξ_A)` over all
subsets satisfies `ξ_{A∪B} + ξ_{A∩B} = ξ_A + ξ_B` (`tail:rem:indexfamily`),
whereas `(η_A)` here is independent over all subsets because `c_A` is a
finite-pattern code; this is why the manuscript's `ξ_A`, `ξ_p` were renamed
`η_A`, `η_p`.

**[entire-functions-at-arbitrary-rank](../../surcomplex/entire-functions-at-arbitrary-rank/)**
(Section 9.2; terminology in Section 2.3). **`cf(G)` here is exactly that
report's `cf(Γ)`**, the least cardinality of a cofinal subset of the value
group, and the order unit is its `ent:def:order-unit`. That report
(`ent:rem:one-name`) excludes the ordinal-index sense of "cofinal"; here that
sense occurs only in Lemma 5.1 (a set of indices cofinal in the ordinal κ),
and is flagged there. The parallels are the threshold `ℵ_0`
(`ent:cor:cofinality`: nonpolynomial entire series exist iff `cf(Γ) = ℵ_0`;
Corollary 5.4 here), the order unit (`ent:thm:main`, `ent:thm:units`;
Theorem 7.1 here), and cofinal versus noncofinal enlargement
(`ent:thm:main-extension`(b); Theorem 1.2 here). The objects differ: entire
power series over `C((t^Γ))` with divisible `Γ` there, the bounded-support Hahn
ring here. Its entire ring is proved GCD; that does not supply the hypothesis
of Appendix A, which concerns a different ring.

**[hidden-negative-hermitian-directions](../../surcomplex/hidden-negative-hermitian-directions/)**
(Section 9.3), placed in the same commit, proves independence over the field
`𝒫_Γ` of series supported in finitely generated subgroups (the Puiseux field
for `Γ = Q`) by prime denominators in the exponents. Its prime-tail series have
support bounded above, so they lie in the base `B_Γ(C)` here; the witnesses
`W_A` here (with `u = 1`) lie in `C((t^Z)) ⊆ 𝒫_Q` and are
transcendental over `F_Q(C)`. Thus for `Γ = Q` the two *fields* `𝒫_Q` and
`F_Q(C)` are incomparable. The prime-tail statement uses the chosen
almost-disjoint family, not all infinite prime sets. Without an order unit,
every finitely generated subgroup is bounded above and `𝒫_Γ ⊆ B_Γ(C)`.

**[independent-surreal-copies](../independent-surreal-copies/)** (`isc:`;
Section 9.5 and the paragraph after Corollary 4.6, both added in batch 31).
Its `isc:thm:cofinalgap` prints the root count of Corollary 4.6 at every
cofinality over an arbitrary field, finite fields included, for the series
`1 + Σ_{α<cf(G)} t^{a_α}`; Corollary 4.6 needs countable cofinality and
Theorem 5.3 characteristic zero, so the single-series case at uncountable
cofinality in positive characteristic is not stated here. Its
`isc:thm:sliceddisjoint` (full Hahn fields on two subgroups are linearly
disjoint over the full Hahn field on the intersection) uses the projections
of Lemma 3.1 and is not stated here.

**Notation.** The collection's [notation guide](../../NOTATION.md) writes
`F_Γ = R((t^Γ))`, and the tail-span report writes `B`, `B_0` for full Hahn
fields; the calligraphic `𝓑_G(K)`, `𝓕_G(K)` here always carry both arguments and
mean the bounded ring and its fraction field. The workspace-versus-fine
topology distinction is the guide's "Topologies and strong summation"; the
Lean normal-form bridge is tracked in
[NORMAL_FORM_BRIDGE.md](../../NORMAL_FORM_BRIDGE.md).

Cardinally bounded Hahn fields, which this report excludes, are studied in
[first-kappa-coefficients](../../surcomplex/first-kappa-coefficients/): omitted
types, completion and spherical completeness of the fields of series with fewer
than `κ` terms.

## Main-text proof review

Sections 1–10 and the conditional implication in Appendix A have received a
mathematical proof review. It expands the support and projection arguments,
tensor-product consequences, polynomial support bands, coefficient coding,
top-rank grouping and normalized GCD descent. The explicit factorial-family
proof now uses a finite Vandermonde matrix over the Hahn field, eliminating
the ordinary-limit step while keeping the theorem's hypotheses.

The convergence wording is corrected: bounded initial Hahn truncations of
the constructed families converge in the named workspace. At countable cofinality these are finite
partial sums; at uncountable cofinality finite subsums do not converge, even
though the family is strongly summable. The article gives the obstructing
valuation neighborhood. Local comparisons now distinguish a sufficient
almost-disjoint construction from a necessary condition and restrict the
prime-tail base comparison to `Γ = Q`.

The 30 standard result statements retain their mathematical content; two
wording clarifications specify extension of relation ideals and that the
integer-grid coefficient object is a field. All 73 labels and result numbers
are preserved. The imported Hahn closedness, iterated presentation,
nonrationality obstruction and upper-support theorem were checked against
L'Innocente–Mantova's cited v5. The GCD input remains a hypothesis; no external
Lean proof was built or adopted. Remaining foundational/source reconciliation
and literature priority remain separate obligations. See
[the review record](../../REVIEW.md); this review adds no Lean mapping.

## Provenance

One manuscript; nothing was merged, so no result is printed twice and no
proof was chosen over another. It contributed every theorem, proof, example,
appendix and non-claim. Editorial changes (Section 1.4): the `bst:` prefix on
all 67 delivered labels (none lost; 6 labels added, 73 in all); the renaming
`ξ → η` above; the terminology conventions of Section 2.3; the comparison of
Section 9 and its four bibliography entries; one tagged display changed to
`equation*` to remove a duplicate PDF destination present in the delivered
source. No theorem statement was changed at editorial assembly. The later main-text
review clarifies two statement wordings without changing their intended scope.

**Stale statements corrected**, keeping the pin as provenance:

- "The catalogue contains 36 reports": true at the pin `048b72c`. Raw
  placement `30dfb4f` brought that historical count to 40; assembly followed
  in `ed88b8f`. The former `52c7ab6` citation is unavailable in local history;
  the guide and article now distinguish the two retained commits.
- At the pin, a literal case-insensitive search in tracked documentation
  excluding `docs/new` finds no `lacunary` and two `bounded support` matches,
  in the analytic-geometry guide and article, concerning one unrelated topic.
  At assembly `lacunary` occurs in this report and its audit, though not
  outside this report. The three-duals example `duals:ex:bounded-support` is
  a related concept, not a literal match for `bounded support` at assembly.
  These dated searches make no absence claim about the current collection.
- The normal-form transport "must be linked to the repository's exact proved
  normal-form bridge": the article now points to `docs/NORMAL_FORM_BRIDGE.md`
  and distinguishes the source statement inventory from the Implementation
  mappings table, which has no `bst:` result mapping.
- The fine-topology distinction was cited to the catalogue only; the notation
  guide's table is now cited too.
- File paths: the delivered text and README used the flat delivered layout
  (`verify.py`, `verification.json`, `python build.py`); the article and this
  README now use `code/` and `data/`.

`research_audit.md` is kept as delivered and speaks at its pin (for example
"The catalogue describes 36 reports"). `data/manifest.json` lists digests of
the delivered files: those of `code/*.py`, `data/verification.json`,
`data/build_audit.json` and `research_audit.md` still match; those of
`article.tex` and `README.md` no longer do, because both were rewritten here,
and the delivered `article.pdf` is not shipped. `data/build_audit.json`
describes the delivered 24-page PDF.

## Build

MiKTeX or TeX Live with pdfLaTeX, the AMS packages, New PX text/math,
`geometry`, `microtype`, `booktabs`, `tabularx`, `longtable`, `array`, `xcolor`,
`enumitem`, `fancyhdr`, `needspace`, `titlesec`, `hyperref` and `bookmark`.
Internal bibliography: no BibTeX, no shell escape, no images, no network.
From a copy of this directory (to keep auxiliary files out of it):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times.
Last build: exit 0, **32 pages** (31 before the batch-31 reciprocal
remarks; every earlier statement, section and equation number unchanged),
no errors, no LaTeX or package warnings, no
undefined or multiply defined references or citations, no duplicate PDF
destinations, no overfull or underfull boxes.

The delivered `code/build.py` looks for `article.tex` **beside itself**, as in
the flat delivered package, so `python code/build.py` in this directory stops
with "Missing LaTeX source". To use it, copy `article.tex` and `code/build.py`
into one scratch directory and run `python build.py` there; it writes
`.build/` and `article.pdf` in that directory. Run that way on this
`article.tex` it succeeds; with its `-no-shell-escape` flag MiKTeX prints the
harmless `epstopdf` shell-escape warning that the delivered README mentions
(the article has no EPS graphics). `build.py` is kept byte-identical.

## Rerun the checks

Python 3.10 or later, standard library only. From this directory:

```sh
python code/verify.py --output <scratch>/verification-local.json
python code/coefficients.py
```

`verify.py` writes `verification.json` **in the current directory** by
default; pass a scratch `--output` path, and never run it from `data/`, so
the delivered record is not overwritten. Seed `20260922`; exact integers and
`fractions.Fraction`, no floating point. At placement it was run on a copy
under Python 3.14.4: **3,163 assertions, all passed**, identical to
`data/verification.json` in every field except `python_version` (the
delivered run used 3.13.5). `coefficients.py` prints a 12-term formal prefix
of `W_A` for `A` the even numbers; it computes coefficients, not Hahn sums,
and uses a surjective finite-table code with a repetition coordinate rather
than the bijection of Lemma 5.1, which has the one property the theorem needs.

The main-text review reran the delivered verifier under Python 3.13.14:
all 3,163 assertions passed, with JSON identical apart from `python_version`.
All seven delivered audit/code/data files, including the manifest, remain
byte-identical; its six recorded digests for retained historical files match.
The current PDF was rebuilt with three clean `pdflatex` passes.
