# Notations for Omnific Integers

**Holonomic towers, shielded and rational–omega calculi, and the complexity of equality**
Merged research report, 23 September 2026, from three manuscripts written
independently on the same day (batch 27, placed in `a4dcb91`): 08 (the base),
05 and 09.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 69 pages
README.md     this guide
08-holonomic-towers-PROVENANCE.md   source 08's provenance and review record, as delivered
09-rational-omega-CLAIMS.md         source 09's claim and evidence ledger, as delivered
code/
  08-holonomic-towers-holonomic.py    08: certified Euler series, D-finite closure, fractions, guarded ring Z + U F_1[U]
  08-holonomic-towers-ordinals.py     08: hereditary Cantor normal forms below epsilon_0
  08-holonomic-towers-verify.py       08: test runner (41 groups); imports holonomic, ordinals
  08-holonomic-towers-demo.py         08: short example; imports holonomic
  05-hereditary-shielding-verify.py   05: exact-rational test runner (18,109 assertions), stdlib only
  05-hereditary-shielding-Makefile    05: delivered Makefile (names delivery paths)
  09-rational-omega-omega_notation.py 09: rational-omega prototype
  09-rational-omega-verify.py         09: test runner (197 assertions); imports omega_notation
  09-rational-omega-Makefile          09: delivered Makefile (names delivery paths)
data/
  08-holonomic-towers-verification.json          recorded run of 08's runner
  08-holonomic-towers-document_validation.json   08's PDF-quality record (for its own 31-page PDF)
  08-holonomic-towers-requirements.txt           sympy==1.14.0
  05-hereditary-shielding-verification.json      recorded run of 05's runner
  05-hereditary-shielding-provenance.json        05's pin, reviewed material, audit limits
  09-rational-omega-verification.json            recorded run of 09's runner
  09-rational-omega-provenance.json              09's pin, read paths, sources, status
  09-rational-omega-requirements.txt             sympy==1.14.0
```

Every label in `article.tex` carries the prefix `onot:`, with the sub-prefixes
`onot:hol:` (Part I, holonomic towers, source 08), `onot:sh:` (Part II,
hereditary forms and shielding, source 05), `onot:grid:` (Part III,
rational–omega grids, source 09) and `onot:neg:` (Part IV, the lower bounds,
from all three); shared material has bare `onot:`. The report has 217 labels.
The text placed in `a4dcb91` was source 08 with bare labels; no report or
ledger on `main` cited them, and they were renamed during this write (for
example `thm:tower` is `onot:hol:thm:tower`, `thm:raw-equality` is
`onot:neg:thm:rawequality`, `prop:treeequality` is `onot:neg:prop:treeequality`).
The source manuscripts are not shipped; their code and data are, under the
prefixes above, byte-identical to the deliveries. 05's `data/checksums.json`
and 09's `data/manifest.json` were pure hash lists of the delivered names and
were dropped at placement.

The two verbatim records name files by their delivery names:
`09-rational-omega-CLAIMS.md` refers to `data/verification.json` (shipped as
`data/09-rational-omega-verification.json`), and the JSON provenance records
refer to `code/verify.py`, `code/omega_notation.py`, `data/verification.json`
and to each source's own PDF, which is not shipped. 08's
`document_validation.json` and the `pdf_validation`/`pdf_quality` entries
describe the delivered PDFs, not `article.pdf`.

## Three sources, one report

| | Manuscript (pages) | Pin | Contributes |
|---|---|---|---|
| **08** | *Notations for Omnific Integers: Exact Holonomic Towers and the Complexity of Equality* (31) | `a45d722` | **The base.** Notation systems and checked equality; the integer-root algorithm, certified Euler series, holonomic towers, truncation, triangular integer parts, floor, support spectrum, ordinal slice and the ε₀-labelled union (Part I, Sections 4–10); raw `d`-block names, Π⁰₁ equality, the translator theorem, the `d`-c.e. positivity classification, checked equality of tree supports (Part IV). Files `08-holonomic-towers-*`. |
| **05** | *Equality for Omnific Notations* (26) | `a45d722` | The shielding and equality-transfer theorems (Section 3); hereditary forms, the ε₀-shielded calculus, finite and collision-aware fronts of matrix series (Part II, Sections 11–13); strict comparison, the rational-realization gap, the dyadic coding with decidable supports (Part IV); effective boundedness. Files `05-hereditary-shielding-*`. |
| **09** | *Effective Notations for Omnific Integers* (28) | `a45d722` | Rational–omega expressions: decidable equality, separated grids, the grid-ring theorem, recognition, floor, truncation at named exponents, per-depth ordinal trace, support barrier, escape and lattice obstructions, recurrence and jet certificates (Part III, Sections 14–19); the Church–Kleene barrier with its caveat. Files `09-rational-omega-*`. |

The pin `a45d722` is 30 commits before the placement.

- **Why one report.** The three prove the same spine — the omnific floor, a
  pullback integer ring of an effective field, an ε₀ ordinal trace, Π⁰₁ stream
  equality with a no-translator corollary, Π¹₁ support validity — and each has
  a large part the others lack. The subject is representation and
  computability, the family of `computable-surreals` and `computer-algebra`.
- **Base 08**, because on the shared theorems it has the weakest hypotheses
  (any effective ordered coefficient field, `d` blocks, an exact order
  classification, checked equality). Three member statements are printed as
  the main ones: 05's shielding and transfer theorems as the general embedding
  (Theorems 3.1, 3.3), with 08's triangular theorem (7.2) and 09's grid-ring
  theorem (16.2) as characterizations (Remark 3.2) — 05 proves only the
  embedding; 05's dyadic coding (Lemma 23.2, Theorem 23.3), because only it
  gives decidable supports, with 08's and 09's midpoint codings as second
  routes (Remark 23.4); and 09's per-depth ordinal trace (Theorem 17.2).
- **Printed once.** Canonicalization (Proposition 2.3; 08, 05, 09), the size
  obstruction (2.4), one-block stream equality (in Theorem 20.2), the
  no-translator theorem (20.4; 08, 09), the Cauchy-name obstruction (20.7; 05,
  09), the Kleene–Brouwer lemma (23.1), and the Church–Kleene barrier
  (Proposition 17.4; 09, with 05's Proposition 10.1 as its uniform half).
- **Renamed symbols** (Section 1.4 and Table 2): the leading exponent is the
  collection's `deg_ω` (08's `ℓ`, 09's `λ`), and support order type is
  `ord(supp x)` (09's `ℓ`); ε₀ is written out (05's `E`), 08's exponential
  series is `Ex(t)`; the coefficient field is `k` (08's `C`, 05's `K`); 05's
  `𝓕 = Frac(ℋ)` and `𝒞` are written `Frac(ℋ)` and `S_{ε₀}`; 09's `F`, `F_d`, `A` are `𝒬`,
  `𝒬_d`, `ℐ`; the shielding field is `L` (05's `F`); `h_e` is the first-halt
  spike (08, 09) and `h̄_e` 05's "halted within n steps"; further renames avoid
  clashes of `B`, `C`, `D`, `E`, `F`, `K`, `N`, `T`, `X`, `Z`.

## Printed by citation, not reprinted

All cited labels exist at HEAD and already existed at the pin.

- The floor formula (Section 2.2) is `odg:thm:floor` of the omnific Diophantine
  report and `cas:eq-floor` of the computer-algebra report (whose ring `Π ⊕ Z` is
  `Oz`, as corrected in `1e3f14b`). Only the effectivity statements of the three
  systems are proved (Theorems 7.4, 11.2, 16.3).
- 09's division with remainder (Corollary 16.4) and Diophantine transfer
  (Proposition 19.3) are `odg:prop:division` and `odg:cor:H10` /
  `odg:eq:existencetransfer`, stronger there (all of `Oz`, positive existential
  formulas, c.e.-completeness); what is kept is computability in `ℐ`.
- The two stream reductions are Reductions A and B of `cas:thm-zerotest`
  (`cas:rem-moralA`, `cas:rem-moralB`). They anticipate 09's one-term
  no-compiler claim and, in substance, 05's rational-realization gap; what is
  new from 05 is the exact minimal dimension `s+1` and the absence of a
  computable bound (Theorem 21.3), with the proof-system corollary 21.4.
- 08's two-block sign example `W_e` (Example 22.4) is `cas:prop-leading`, and
  its one-block contrast `cas:rem-rankone`; 08's `d`-c.e. completeness
  (Theorem 22.2) strengthens it. The Π¹₁ results (Theorem 23.3,
  Proposition 23.5) strengthen `cas:prop-validation` to an exact classification.
- 08's integer-root algorithm (Theorem 4.3) is the effective form of
  `hol:lem:integer` of the holonomic-rigidity report (Remark 4.4).
- 09's grid fields are `cas:thm-core` after compilation (Section 15.2).

## Results added in the merge

Each is marked `[merge]` and has a complete proof.

- **Embedding versus characterization** (Remark 3.2): the omnific parts of the
  tower fields and of the separated grids are exactly the shielded rings
  `S_{δ_r}(R_{r−1}, F_{r−1})` and `S_{γ_1}(ℐ^tail_{r−1}, 𝒦_{r−1})`.
- **The three omnific rings** (Proposition 17.3): all three systems have ordinal
  trace exactly the ordinals below ε₀ (08's union, 05's hereditary ring, 09's
  field), yet `S_{ε₀}` is incomparable with `ℐ` and with `ℛ_ε` for all
  coefficient fields, `ℐ ⊄ ℛ_ε` always, and `ℛ_ε ⊄ ℐ` when the tower's field
  `k ≠ Q`. For `k = Q` the last inclusion is **not settled** (Question 26.8).
- The credit to `hol:lem:integer` (Remark 4.4); the identification of 09's
  hereditary hierarchy `⋃H_d` with 05's `ℋ_Q`; Question 26.8.

## What the report claims

Here `k ⊆ R` is an effective ordered coefficient field (typically `Q` or the
real algebraic numbers).

- **Shielding (05).** For `L ⊆ k((t^G))` a subfield, `Z ⊆ D ⊆ L ∩ Oz` and
  `|g| < Λ` on `G`, evaluation at `X = ω^Λ` embeds `D + X L[X]` in `Oz` with unique
  coefficient lists and the sign of the top block (Theorem 3.1); with effective
  arithmetic, `Eq` of the shielded ring is many-one equivalent to `Eq_L`
  (Theorem 3.3).
- **Part I (08).** Nonnegative integer roots are computable over effective
  leading-data fields (Theorem 4.3); certified Euler names have effective
  validity, coefficients, zero test and ring operations, and every D-finite
  series has one (Theorems 5.2, 5.4); the towers `F_r` are countable subfields of
  `No` with decidable equality and order (Theorem 6.2), effective truncation
  (7.1), `F_r ∩ Oz = R_{r−1} + U_r F_{r−1}[U_r]` (7.2) and a computable floor (7.4);
  supports have type `≤ ω^r`, `< ω^r` for integers, every `η < ω^r` realized
  (8.1); `F_r ∩ On = N[U_1, …, U_r]` (8.3); the ε₀-labelled union has decidable
  equality, order, recognition, floor, canonicalization and ordinal trace
  `On_{<ε₀}` (9.2), with `ε₀` its least ordinal upper bound and `ε₀/2` a smaller
  surreal one (Corollary 9.3).
- **Part II (05).** Hereditary forms over `Q` or the real algebraic numbers have
  canonical trees, decidable order, omnific membership and floor
  (Theorems 11.1, 11.2); their ordinals are those below ε₀ (11.3). `S_{ε₀}` has
  decidable validity, equality and order, with ε₀ transcendental over
  `Frac(ℋ)` (12.2); `Frac(ℋ)` is not real closed (Proposition 12.3); one-state
  supports of type `ω^r` (Corollary 12.4). Finite fronts: total degree `< m` at
  independent scales (Theorem 13.1); the collected adjugate numerator certifies
  zero and the leading term at arbitrary positive scales, bound
  `(m−1)Σδ_i`, attained (13.2, Example 13.3); Cauchy products in dimension
  `(m+m′)^r` (Proposition 13.4).
- **Part III (09).** Decidable validity, equality and order of rational–omega
  terms (Theorem 14.2); `𝒬 ∩ R = Q` (Corollary 14.5); separated-grid compilation
  (15.2); the grid integer ring (16.2); membership in `Oz`, floor, truncation at
  every named exponent and every coefficient computable (16.3); `𝒬_d ∩ On =
  [0, β_d)`, `𝒬 ∩ On = [0, ε₀)` (17.2); supports `< ω^ω` (18.2), sharp at depth
  two (18.3); a computable strong sum outside `𝒬` (18.4); `Σ ω^{1/n} ∉ 𝒬` (18.5);
  recurrence and rectangular-jet certificates (Proposition 19.1, Theorem 19.2).
- **Part IV.** For every `d`, raw `d`-block equality is Π⁰₁-complete, even on
  values with at most one monomial; strict comparison is Σ⁰₁-complete for one
  block (Theorem 20.2; 08, with 05 and 09 for `d = 1`); no translator into any
  system with decidable equality (20.4; values in `R_2` and `𝒬_2 ∩ Oz`); an
  exact support count suffices, an upper bound does not (Proposition 20.5); the
  full-support rational switch family is Π⁰₁-hard with no translator into rational
  codes (Theorem 21.1), also inside `S_{ε₀}` (Corollary 21.2), and its minimal
  realization dimension is exactly `s+1` with no computable bound (21.3);
  positivity of `d` blocks is many-one complete for the `d`-c.e. sets
  (Theorem 22.2); support validity is Π¹₁-complete with decidable dyadic
  supports in `[1,2)` (Theorem 23.3), promised equality is co-c.e. and checked
  equality Π¹₁-complete (Proposition 23.5).

## What the report does not claim

- All three sources are AI-assisted, unrefereed drafts that call their main
  results proposed contributions; priority is not certified, and nothing is
  formalized: `docs/FORMALIZATION.md` on `main` maps no label of this report,
  and the repository has no omnific Lean module.
- The systems are specific countable languages, not notations for all of `Oz`;
  none is real closed; `Ω` is Conway's map, not the surreal exponential; 09's
  constants are rational and its separated basis fails for irrational
  coefficients; ε₀ is a design choice, not a ceiling. No uniform complexity
  bound is claimed anywhere.
- The shielding theorem gives only the embedding; the characterizations are
  08's and 09's. The midpoint codings do not give decidable supports.
- The Π¹₁ theorems classify validity, not promised equality. The `d`-c.e.
  classification is for zero-constant raw names only.
- No question named by an earlier report is answered: not the
  computable-surreals research directions ("support certificates beyond
  left-finiteness", "uniform translation complexity"), not `odg:q:roots` or
  `odg:q:search`, not `hol:nl:q:effective`.
- Appendix B keeps every limitation stated by a source, numbered per source:
  08 (27 items), 05 (26), 09 (24), and 6 for the merge (83 in all).
  Section 26 lists eight questions, all open.
- The finite checks verify finite identities and examples only.

## Corrections and stale statements

Appendix A.4 and A.5.

- **08's Proposition 13.4** said that "equality under the validity promise has a
  co-c.e. test for inequality"; its proof and its own summary table show that
  inequality is c.e., so promised equality is co-c.e. Corrected in
  Proposition 23.5 (wording only).
- 08 read the computer-algebra README and presents the one-monomial
  localization and the two-scale sign example as its own; both were
  `cas:rem-moralB` and `cas:prop-leading` at the pin. 05 and 09 do not cite the
  computer-algebra report, and no source cites `hol:lem:integer`.
- 05 read the omnific Diophantine report only to line 150; `odg:thm:floor`,
  `odg:prop:division` and `odg:cor:H10`, which its and 09's results duplicate,
  were already there. 09's reference to "the repository's omnific arithmetic
  program" is made precise as `odg:cor:H10`.
- At the pin, the computer-algebra report called an omnific-integer convention
  "a different target again" from its `Π ⊕ Z` floor; `1e3f14b` corrected this.
- 08's Chen–Fang–van der Hoeven reference (arXiv) is completed with its ISSAC 2026
  publication, as recorded in the computer-algebra report. 05's matrix zero test
  is additionally attributed to Schützenberger's rational series.
- No theorem was found false; the placement dossier re-read every proof and
  independently rechecked 30 finite instances.

## Relations to neighbouring reports

- [`computer-algebra`](../computer-algebra/): stream reductions
  (`cas:thm-zerotest`), sign obstruction (`cas:prop-leading`), validation
  (`cas:prop-validation`, strengthened), the core (`cas:thm-core`), the floor
  (`cas:eq-floor`); its positive-counterweights section asks for a certified
  recurrence start with exceptional indices, which Part I supplies over
  non-Archimedean fields.
- [`computable-surreals`](../computable-surreals/): the Cauchy-name constants of
  `thm:inversehard`(iv), structural validity `prop:validity`, and the no-go
  theorem `thm:nogo`, whose "more informative real representation" is the route
  taken here. Its research directions are not answered (Section 25).
- [`omnific-diophantine-geometry`](../../surreal/omnific-diophantine-geometry/):
  floor, division, Diophantine transfer, the non-terminating Euclidean
  algorithm (`odg:ex:euclid`); `odg:q:roots` and `odg:q:search` stay open.
- [`holonomic-rigidity-for-entire-hahn-functions`](../../surcomplex/holonomic-rigidity-for-entire-hahn-functions/):
  `hol:lem:integer`; `hol:nl:q:effective` stays open.
- [`foundations`](../foundations/): `Oz = Π ⊕ Z` (`found:eq:omnific`).
- [`definable-surreals-and-omnific-integers`](../definable-surreals-and-omnific-integers/),
  written from the same batch: set-theoretic definability, not computability;
  cited by directory only.

## Build

From this directory, or better from a copy in a scratch directory:

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build has no errors, no LaTeX or package warnings, no overfull or underfull
boxes, no undefined references and no duplicate destinations. Commit only
`article.pdf`, not the auxiliary files.

## Reproducing the finite checks

The scripts need Python 3 and, for 08 and 09, SymPy (the recorded runs used
Python 3.13.5 and SymPy 1.14.0; the reruns for this report used Python 3.14.4
and SymPy 1.14.0 and passed with the same counts). Run them **on a copy with
the delivery names restored**: 08's runner and demo import `holonomic` and
`ordinals`, and 09's runner imports `omega_notation`, by their delivery names;
and every runner writes `data/verification.json` next to its `code/` directory,
an unprefixed file that must not be created here. Each source gets its own
directory:

```
D=/path/to/this/report; S=/path/to/scratch     # a fresh directory
mkdir -p $S/05/code $S/05/data $S/08/code $S/08/data $S/09/code $S/09/data
cp $D/code/05-hereditary-shielding-verify.py       $S/05/code/verify.py
for m in holonomic ordinals verify demo; do
  cp $D/code/08-holonomic-towers-$m.py             $S/08/code/$m.py; done
cp $D/code/09-rational-omega-omega_notation.py     $S/09/code/omega_notation.py
cp $D/code/09-rational-omega-verify.py             $S/09/code/verify.py
python -m pip install -r $D/data/08-holonomic-towers-requirements.txt
cd $S
python 05/code/verify.py       # writes 05/data/verification.json
python 08/code/verify.py       # writes 08/data/verification.json
python 08/code/demo.py         # prints Section 10's examples (in 08's names E, G)
python 09/code/verify.py       # writes 09/data/verification.json
```

Expected: 05 prints a JSON record with `"status": "PASS"` and
`"total_assertions": 18109` in the same 16 categories as
`data/05-hereditary-shielding-verification.json`; 08 prints 41 `PASS` lines and
a record with `"status": "passed"`, `"check_groups": 41`, 521 change schedules,
780 priority assignments and 121 dyadic nodes; 09 prints a record with
`"status": "PASS"` and `"assertions": 197`. The rewritten records differ from
the shipped ones only in timestamps, timings and interpreter versions. Do not
pipe 08's runner into a command that closes its output early (such as `head`):
the runner then records a write error as a failure. The delivered Makefiles
(`code/05-hereditary-shielding-Makefile`, `code/09-rational-omega-Makefile`)
name the delivery layout (`article.tex`, `code/verify.py`) and work only in a
directory arranged that way. The checks do not compute halting sets, verify the
Π¹₁ reduction, enumerate infinite supports, or prove any completeness, support,
ordinal or termination theorem; those are proved in the text.
