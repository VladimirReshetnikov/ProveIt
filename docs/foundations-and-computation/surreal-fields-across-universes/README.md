# Surreal Fields Across Set-Theoretic Universes

**Omitted cuts, fresh-sign gaps and saturation spectra of old surreal fields;
first new birthdays; surcomplex real forms; and a Boolean completion of reverse
simplicity**
Merged research report, 22 September 2026, from four manuscripts: 01 (the base),
03, 04 and 08, all dated 22 September 2026 and all pinned to repository commit
`4f2645599121fa872c7104995e47f86f0382351f`.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 50 pages (title page, 2 contents pages, 47 numbered pages)
README.md     this guide
03-fresh-sign-gaps-PROOF_STATUS.md               source 03: proof and verification status
code/
  01-forcing-omitted-cuts-Makefile               source 01's LaTeX Makefile (see "Build and reproduce")
  03-fresh-sign-gaps-check_finite_signs.py       source 03 finite sign and block-code checks
  04-universe-saturation-Makefile                source 04's Makefile (written for its own file names)
  04-universe-saturation-verify_finite_models.py source 04 finite interval-code checks
  08-forcing-saturation-verify_sign_code.py      source 08 finite sign-code checks
data/
  03-fresh-sign-gaps-finite_checks.json          recorded run of the source 03 checks
  04-universe-saturation-finite_check_results.txt  recorded run of the source 04 checks
  08-forcing-saturation-verification_results.txt   recorded run of the source 08 checks
```

Every label in `article.tex` carries the prefix `univ:`. Source 01's labels keep
their names behind the prefix (for example `univ:thm:main-summary`). Code and data
files keep the numbers of the sources they came from; they are byte-identical to
the delivered files. No source manuscript, source README or source PDF is shipped.
`03-fresh-sign-gaps-PROOF_STATUS.md` describes source 03's own 21-page
manuscript, not this report; its page count and build statements refer to that
manuscript.

## Why one report

All four manuscripts prove the same spine in the same setting: transitive
universes `M ⊆ N` of ZFC with the same ordinals, the old field `No^M` viewed as a
proper class of `N`, and all sizes computed in `N`. They share the cut and
saturation criterion, the regular first new length `δ`, an omitted `(δ,δ)` gap,
the `ω` boundary, the pure/conjugation contrast, the distributivity corollary and
the Cohen and Prikry examples. **01 is the base**: it has the weakest hypotheses
(plain ZFC with a definable inner model; Global Choice only for one negative
Boolean result) and the strongest criterion (one small side suffices). The other
sources' unique results form their own parts and sections:

- **03**: the fresh-sign classification of all set-presented gaps (Part II), old
  ordinal bounds, the ordinal-bound cut criterion, the Prikry fresh sign, and the
  real-form invariant with agreement on `C^N` and finite forcing towers.
- **04**: the absolute all-ordinal interval code with closed finite-branch
  formulas (Section 5.2), cuts inside `(0,1)`, `Add(κ,1)` under `κ^{<κ}=κ`,
  elementarily equivalent nonconjugate involutions, open cones, and
  nowhere-denseness of `No^M[i]` in `No^N[i]`.
- **08**: the ordinal block code with its exact separator class (Section 5.3),
  the dense-linear-order clause, the first new birthday `β` with
  `δ ≤ cf^N β ≤ β` (Part III), `β` in the forcing examples, the lottery-sum
  caution, non-definability of conjugation, and the saturated back-and-forth
  route.

Results proved by two or more sources are printed once with every proving source
named at the statement (Section 1.6 lists them). The converse direction of the
spine has three genuinely different constructions: 01's interval tree is the main
route (Section 5.1), and 04's absolute code and the block codes of 08 and 03
(Section 5.3, Proposition 9.1) are marked second routes. Two existence proofs for
`δ` and two class back-and-forth routes are also kept.

**Notation.** One symbol per notion (Section 1.3, with a table of every renaming):
`No^M`, `No^N` for the old and new fields; `SC^M = No^M[i]`, `SC^N` for the
surcomplex fields (`K` is not used for these proper classes, since the collection
reserves `K` for set-sized fields); `δ` for the first new *length* of an
ordinal-valued sequence (03's `ν`, 04's `d(M,W)`); `β` for the first new
*birthday*, as in 08; `ρ` for the measurable cardinal. The sibling report also
writes the first new birthday as `β`; several of its source manuscripts wrote `δ`
for it, and that `δ` is this report's `β`, not its `δ`.

## Hypotheses

- **(H)**: `N ⊨ ZFC` and `M` a parameter-definable transitive inner class
  containing all ordinals and satisfying ZFC (or an available class predicate with
  the needed Separation and Replacement instances). Everything is proved under (H)
  except what is listed next.
- **(GC)**: `GBC` with Global Choice, `M` a class. Needed only for the class
  isomorphisms and real forms of Part V and for the impossibility of a
  class-complete Boolean algebra (Theorem 17.3).

Sources 03 and 08 were written in `GBC` with Global Choice. Their proofs used
outside Part V were re-read for this merge and use only set-sized choices, Choice
in `M` and Replacement for `M`; source 03's gaps, which it quantified over as class
partitions, are given by their set presentations (Definition 6.1).

## What the report claims

- **Theorem 1.1 (main spectrum; 01, 03, 04, 08).** For every infinite `N`-cardinal
  `κ`: no new ordinal-valued sequences of length `< κ` ⇔ every `N`-set cut
  `L < R` in `No^M` with `min(|L|,|R|) < κ` is filled ⇔ every such cut with
  `|L ∪ R| < κ` is filled. For uncountable `κ` these are equivalent to
  `κ`-saturation of `No^M` as an ordered field and as a dense linear order. Failing
  cuts can be chosen inside `(0,1)`. The key lemma is Theorem 3.5: a cut with one
  side in `M` is always filled.
- **Theorem 1.2 and Sections 4–7.** `δ` is a regular cardinal of both universes
  (Proposition 4.2); `No^M` has a set-presented gap of exact cofinality pair
  `(δ,δ)` and none smaller (Theorem 6.2); it is `κ`-saturated for uncountable `κ`
  exactly when `κ ≤ δ`, and set-saturated only if `M = N` (Corollary 6.4); it is
  `ω`-saturated exactly when no reals are added, while the pure order is always
  `ω`-saturated (Theorem 7.1).
- **Codings (Section 5).** The interval tree and branch decoder (Lemma 5.1,
  Theorem 5.2); the absolute all-ordinal code (Theorems 5.3, 5.4, Proposition 5.5);
  the block code whose separators are exactly `Cone(code(f))` (Lemma 5.6,
  Theorem 5.8).
- **Fresh signs (Part II, source 03).** Set-presented gaps correspond bijectively
  to fresh signs; each gap is symmetric with both cofinalities `cf^N b(s)`
  (Theorem 8.4); its fillers are exactly `Cone(s)` and `No^N \ No^M` is the disjoint
  union of fresh cones (Theorem 8.5); the gap spectrum (Corollary 8.6); the least
  omitted pair has size `δ`, also the least cofinality of a fresh sign
  (Theorem 9.2).
- **First new birthday (Part III, source 08).** `β` is the least birthday of a new
  surreal, a cardinal of `M` and `N`, and `δ ≤ cf^N β ≤ β` (Proposition 10.2). A
  merge remark observes that `β` is also the least length of a fresh sign
  (Remark 10.4).
- **Surcomplex (Section 11).** `SC^M` is saturated over every `N`-set in the pure
  field language (Theorem 11.2); `(SC^M, c_M)` has exactly the spectrum of `No^M`
  and is an elementary substructure of `(SC^N, c_N)` (Theorem 11.4); no order or
  field isomorphism `No^M ≅ No^N` with set-sized images exists (Corollary 11.6).
- **Bounded fragments (Theorem 12.1, source 01).** For uncountable regular `κ` of
  `M` that stays a cardinal, `(No_{<κ})^M` is `κ`-saturated in `N` iff `κ` stays
  regular and no binary signs shorter than `κ` are new.
- **Forcing (Section 13).** The distributivity characterization (Corollary 13.1);
  `Add(κ,1)` gives `δ = β = κ` with no cardinal arithmetic (Proposition 13.2);
  Prikry at a measurable `ρ` gives `δ = ω`, `β = ρ`, `ω`- but not
  `ω₁`-saturation, identical fragments below `ρ`, and a separator of birthday
  exactly `ρ` (Corollary 13.4).
- **Topology (Section 14).** Every `N`-set of old numbers is uniformly discrete and
  closed, and set-indexed Cauchy nets are eventually constant (Proposition 14.1);
  if `M ≠ N`, `No^M` is closed and nowhere dense in `No^N` with its own order
  topology as subspace topology, and likewise `SC^M` in `SC^N` (Theorem 14.3).
- **Real forms under Global Choice (Part V).** `SC^M ≅ SC^N` fixing any `N`-set
  (Theorem 15.2); the transported involution `j` has gap spectrum equal to the
  fresh-sign spectrum and least omitted pair `δ`, no set-sized cofinal subset, and
  is not conjugate to `c_N` (Theorem 16.2); `(SC^N,c_N)` and `(SC^N,j)` are
  elementarily equivalent with different spectra (Theorem 16.3); `j` can agree
  with `c_N` on `C^N` (Corollary 16.5); several grounds give several
  nonconjugate forms (Theorem 16.6), realized by finite `Add(κ_a,1)` towers with
  no large cardinals (Corollary 16.7).
- **Boolean completion (Section 17, source 01).** A set-complete class Boolean
  algebra in which reverse simplicity is dense (Theorem 17.1), answering a
  precisely interpreted Question 2 of Berenbeim's 2020 notes; no class-complete
  one under Global Choice (Theorem 17.3).

**Questions (Section 19).** Source 01's question on asymmetric gap pairs is
answered by source 03 (Corollary 8.6); what stays open is which symmetric pairs
above `δ` occur for a given forcing (Question 19.2). Source 01's question on
`SC^M ≅ SC^N` is settled under Global Choice (Theorem 15.2); only weaker
assumptions stay open (Question 19.3). Source 08's remark that it lacks "a
complete spectrum of all omitted cut characters" is answered for a fixed pair by
source 03; the completeness question stays open (Question 19.4). Questions 19.1,
19.5, 19.6 and 19.7 are open; the finite version of 19.7 is answered by
Corollary 16.7.

## What the report does not claim

Section 20 keeps every limitation of the four sources, per source: 15 items from
01, 16 from 03, 13 from 04, 11 from 08, and 5 added by the merge (60 in all). In
brief:

- The results are proposed contributions with written proofs. Priority is not
  certified, no named published conjecture is claimed solved, the report is not
  refereed, and **nothing is Lean-verified or formalized**.
- Classical surreal facts, quantifier elimination, standard forcing facts
  (distributivity, closure, the Prikry properties), the forcing notion of fresh
  functions (Fischer–Koelbing–Wohofsky), Ehrlich's absolutely saturated models,
  and the collection's class back-and-forth, conjugacy criteria and countably
  cofinal real form are credited, not claimed. The Boolean construction may be
  folklore in class forcing; Berenbeim's question comes from research notes, not
  a published conjecture.
- External means computed in `N`, not in a larger metatheory. No unrestricted class
  truth predicate, class Zorn lemma or class-valued recursion is used. The
  ground-bound lemma is not a covering property. Field elementarity is not
  `M ≼ N`.
- The gap invariant excludes cuts with proper-class cofinality; it recovers
  threshold and cofinality data, not the inner model, the forcing or sign lengths,
  and equality of spectra is not shown to classify fields. `Add(κ,1)` is analysed
  only at its first gap. Finite forcing towers only.
- The class isomorphisms are noncanonical and preserve no valuation, simplicity,
  exponential or derivation. The real-form results do not classify real forms or
  involutions.
- Exponential and differential expansions are not treated. No topological
  completion theorem is claimed; an omitted cut is not a Cauchy sequence.
- The finite checks verify finite sign and interval formulas only; there are no
  finite fresh signs, and no check tests freshness, forcing, regularity,
  saturation or any class argument.

## Corrections to the sources' repository statements

Appendix A records them, keeping the pin as provenance: the "no matches" for
`forcing`/`saturation` searches reported by 01 and 08 (the foundations report
contains "saturation for small cuts" and a subsection on class forcing, neither of
which contains these results); 01's count of forty reports plus four drafts (the
collection now has 44 report directories, including this report and its sibling);
the automorphism report's rewrite after the pin (its results are cited here by
current numbers and `saut:` labels); and the set-cut interpolation criterion
`saut:prop:conjugacycriterion`, which no source cites.

## Relation to the neighbouring reports

**[surcomplex-field-automorphisms](../../surcomplex/surcomplex-field-automorphisms/)**
proves the class back-and-forth used in Part V (its Theorem 9.1,
`saut:thm:acfhomogeneity`), the fixed-field conjugacy criterion of its Section 10,
a real form with a countable cofinal subset (Theorem 10.2), and the criterion that
an involution is conjugate to `c` iff its fixed field has the set-cut interpolation
property (Proposition B.1, `saut:prop:conjugacycriterion`). That criterion already
implies the non-conjugacy statements of Theorems 16.2 and 16.3. What is new here
(Remark 16.4): real forms with no set-sized cofinal subset, several forms separated
from one another by the gap invariant, agreement with `c_N` on `C^N`, and
elementary equivalence with different spectra. These continue, but do not settle,
that report's open real-form classification (its Section 14).

**[foundations](../foundations/)**: Proposition 14.1 is an external version of
its Theorem 12.1 (`found:thm:discrete`). It needs only old positive lower bounds,
which hold where cut filling fails; the Lean form of that theorem's Cauchy clause
assumes small cut filling (`HasSmallCutFillers`). Remark 14.4 also relates the
results to its Section 7.7 (`found:sub:countable`): for same-ordinal outer
universes, bounds of outer sets of old numbers are absolute while cut filling is
not.

**[birthday-cutoffs-and-hereditary-sets](../birthday-cutoffs-and-hereditary-sets/)**,
the sibling report of the same batch, studies bounded birthday fields with a
birthday symbol and their interpretation of hereditary sets. It proves, for every
same-ordinal outer model, that the first new birthday is the least ordinal
acquiring a new subset; this report keeps source 08's proof because 08 adds
`N`-cardinality and `δ ≤ cf^N β` (Remark 10.5).

**[computable-surreals](../computable-surreals/)**: its `prop:topology` is the
universe-relative form of set-indexed convergence; the same-ordinal setting here
needs no lower-universe smallness. **[genetic-gaps-and-primitives](../../surreal/genetic-gaps-and-primitives/)**
uses "gap" for a proper-class gap of `No`; the gaps here are set-presented gaps of
`No^M` seen from `N`.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 50 pages with zero errors, zero LaTeX or package warnings, zero
overfull or underfull boxes, zero undefined references or citations, zero
multiply defined labels and zero duplicate PDF destinations. The log contains one
TeX information line, `ignored: Infinite glue shrinkage found in box being split`,
which the `longtable` package emits when a long table breaks across pages; the
delivered source 01 produces the same line. Source 01's Makefile runs the same
`latexmk` command on `article.tex` in the current directory, so
`make -f code/01-forcing-omitted-cuts-Makefile` from this directory should build
the report in place (not tested for this merge, since no `make` was available;
its `clean` target removes auxiliary files). Source 04's Makefile names
source 04's unprefixed files, which are not shipped, so its targets do not run
here; it is kept for provenance.

The finite checks use only the Python standard library. **Run them on a copy of
this directory.** The three scripts were written for unprefixed file names in
their own packages, and source 03's documented command
`python check_finite_signs.py --output finite_checks.json` would overwrite its
recorded output (on Windows, with CRLF line endings). With the shipped names:

```sh
python code/03-fresh-sign-gaps-check_finite_signs.py                        # prints the JSON record only
python code/03-fresh-sign-gaps-check_finite_signs.py --output rerun-03.json # writes a new file
python code/04-universe-saturation-verify_finite_models.py > rerun-04.txt  # prints only
python code/08-forcing-saturation-verify_sign_code.py > rerun-08.txt       # prints only
```

Recorded runs: source 03, 127 sign strings, 16,129 comparisons, 127 cone checks,
340 block-code cases and 1,744 nested endpoint pairs; source 04, 1,365 interval
nodes, 20,475 child pairs, 1,364 decodings and 65,025 cut/prefix comparisons;
source 08, 304,000 checks. All pass. For this merge the three suites were rerun on
a copy with Python 3.14.4; each output matched its recorded file except for line
endings.
