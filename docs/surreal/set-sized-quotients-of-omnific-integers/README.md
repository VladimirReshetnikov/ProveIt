# Set-Sized Quotients of the Omnific Integers

**The universal constant-term quotient, exact cardinal thresholds, support
thresholds, and what survives in large quotients**
Merged research report, 23 September 2026, from eight manuscripts of
22 September 2026 (batch 24, placed in `be06fc8`): 06 (the base), 03, 04, 07,
08, 09, 10 and 11. Manuscript 05 of the same batch proves the unital universal
theorem too; it is merged into the sibling report
[`omnific-diophantine-geometry`](../omnific-diophantine-geometry/) and credited
here.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 90 pages
README.md     this guide
03-cardinality-normalization-SOURCE_NOTES.md   source 03: repository pin, companion draft, literature
04-universal-residue-SOURCE_AUDIT.md           source 04: repository pin, prior manuscript, novelty, checks
06-universal-quotient-source_audit.md          source 06: repository scope, inputs, proof checkpoints
07-quotient-rigidity-SOURCE_AUDIT.md           source 07: repository inspection, precedents, novelty
08-small-rings-BUILD_REPORT.md                 source 08: build and finite-check record
08-small-rings-SOURCE_AUDIT.md                 source 08: repository pin, literature, novelty
09-set-shadows-SOURCE_AUDIT.md                 source 09: repository pin, literature, novelty
11-set-sized-algebra-SOURCE_AUDIT.md           source 11: repository pin, MathOverflow question, novelty
code/
  03-cardinality-normalization-verify_identities.py   source 03 checks (2,362; stdout)
  04-universal-residue-verify_identities.py           source 04 checks (writes verification.json, see below)
  04-universal-residue-Makefile                       source 04's Makefile (original file names)
  06-universal-quotient-verify.py                     source 06 checks (17,586)
  06-universal-quotient-Makefile                      source 06's Makefile (original file names)
  07-quotient-rigidity-verify_finite.py               source 07 checks (621; needs SymPy)
  08-small-rings-finite_checks.py                     source 08 checks (1,277; stdout)
  09-set-shadows-verify.py                            source 09 checks (597)
  09-set-shadows-build.sh                             source 09's build script (original file names)
  10-omnific-arithmetic-checks.py                     source 10 checks (171,395; needs SymPy; stdout)
  10-omnific-arithmetic-Makefile                      source 10's Makefile (original file names)
  11-set-sized-algebra-check_finite_identities.py     source 11 checks (1,858)
  11-set-sized-algebra-build.sh                       source 11's build script (original file names)
data/
  03-cardinality-normalization-verification_results.txt   recorded run of the source 03 checks
  04-universal-residue-verification.json                  recorded run of the source 04 checks
  04-universal-residue-build_report.json                  source 04's build report and file hashes
  06-universal-quotient-verification.json                 recorded run of the source 06 checks
  06-universal-quotient-build_audit.json                  source 06's build, rendering and integrity record
  07-quotient-rigidity-verification_results.json          recorded run of the source 07 checks
  07-quotient-rigidity-requirements.txt                   sympy==1.14.0
  08-small-rings-finite_checks.txt                        recorded run of the source 08 checks
  09-set-shadows-verification.json                        recorded run of the source 09 checks
  10-omnific-arithmetic-check_results.txt                 recorded run of the source 10 checks
  10-omnific-arithmetic-requirements.txt                  sympy==1.14.0
  11-set-sized-algebra-finite_checks.json                 recorded run of the source 11 checks
```

The directory also holds files of five later manuscripts, placed in `cf350b1`
after this report was written and **not yet integrated**: they are listed
under "Staged for the next merge" below, and nothing in `article.tex` or this
guide describes their content.

Every label in `article.tex` carries the prefix `osq:`. The large-quotient part
(Section 13) uses the sub-prefix `osq:if:`, the integral-closure part
(Section 14) `osq:nm:`, and the polynomial-map part (Section 15) `osq:pm:`.
The report has 334 labels. The audit files and programs keep the source
numbers `03` to `11` of the batch, and the audit files keep their sources' own
notation and theorem numbering. No source manuscript is shipped.

The text placed in `be06fc8` was source 06 with bare labels, which
`docs/FORMALIZATION.md` indexed as **Pending** placement entries. The written
report replaces them as follows (a label of 06 that became part of a larger
statement points to that statement):

| 06 (placed) | here | 06 (placed) | here |
|---|---|---|---|
| `main:class` | `osq:main:universal`, `osq:thm:universal` | `thm:polynomialtests` | `osq:thm:presentations` |
| `main:cardinal` | `osq:thm:model06` | `prop:derivations` | `osq:thm:derivations` |
| `main:homological` | `osq:thm:homological`, `osq:thm:extthreshold` | `prop:euler` | `osq:prop:classder` |
| `lem:c0` | `osq:lem:ct` | `lem:kappagap` | `osq:lem:kappagap` |
| `lem:gap` | `osq:lem:gap` | `prop:fieldclosure` | `osq:prop:fieldclosure` |
| `prop:common` | `osq:prop:common` | `thm:kappasmall` | `osq:thm:model06` |
| `lem:collision`, `cor:collisioncard` | `osq:lem:collision` | `prop:kappachain` | `osq:prop:kappachain` |
| `lem:Ha` | `osq:lem:Ha` | `prop:sharp` | `osq:lem:card06`, `osq:thm:model06` |
| `thm:universal` | `osq:thm:universal` | `lem:projectiveideal` | `osq:lem:projideal` |
| `cor:nofaithful` | `osq:cor:faithful` | `prop:flatideal`, `lem:tensorzero` | `osq:thm:homological` (i), (ii) |
| `prop:localization` | `osq:prop:fractions`, `osq:cor:nofield` | `thm:extreflection` | `osq:thm:homological` (iv) |
| `thm:quotients` | `osq:thm:reflection`, `osq:thm:quotients` | `cor:smallext` | `osq:thm:extthreshold` |
| `cor:smallquot`, unlabeled Gaussian corollary | `osq:thm:quotients`, `osq:cor:smallprimes` | `prop:dimensions` | `osq:thm:homological` (iii), (v) |
| `cor:profinite` | `osq:thm:completions` | `prop:extone` | `osq:thm:homological` (vi) |
| `cor:primeexample` | `osq:cor:primeexample` | `prop:exttwo` | `osq:thm:homological` (vii) |
| `prop:unitconstant` | `osq:prop:unitconstant` | `thm:extthreshold` | `osq:thm:extthreshold` |
| `prop:primereservoir` | `osq:if:prop:reservoir` | `prop:matrices` | `osq:prop:matrices` |

## Eight sources, one report

All eight manuscripts answer the same question, *what can a set-sized ring or
module see of an omnific integer?*, with the same answer: exactly the ordinary
integer constant term. They then diverge. The report prints the common spine
once (Sections 2–7) and keeps every result of every source.

| | Manuscript (pages) | Pin | Contributes |
|---|---|---|---|
| **06** | *The Universal Set-Sized Quotient of the Omnific Integers* (25) | `a5c2a97` | **The base.** The coefficient-ring theorem over any set field with the scaled-field collision lemma (Lemma 4.1) and the direct module argument; the model `A^06_κ` (Section 11.2); the homological package (Section 12); matrix representations (Proposition 5.6); polynomial tests (Theorem 6.14); the prime-reservoir proposition (Proposition 13.12). Files `06-universal-quotient-*`. |
| **03** | *Cardinal Visibility and Normalization of Omnific Integers* (25) | `cd80e5e` | The smaller-scale field bound (in Proposition 10.3); the model `A^03_κ` with threshold `κ^ℵ0` (Section 11.1); integral and complete integral closure, set-generated algebras, surcomplex analogues, set-valued valuations (Section 14). Files `03-cardinality-normalization-*`. |
| **04** | *What Set-Sized Algebra Can See of Surreal Arithmetic* (24) | `cd80e5e` | The theorem for `D + Π_k` by separation and the explicit telescope; standard part on the finite side (Section 8); the support threshold with its negative side (Theorem 9.1); fixed-group bounds; localizations, algebras, derivations. Files `04-universal-residue-*`. |
| **07** | *Small Quotients and Large Internal Fields of the Omnific Integers* (27) | `37eefca` | The theorem over any set field by weighted certificates; completions; the embedding `No ↪ F_a`, field transfer, the exact binomial kernel and the Cantor algebra in `Oz/(1+ω^a)` (Section 13). Files `07-quotient-rigidity-*`. |
| **08** | *What Small Rings Can See of Omnific Integers* (26) | `37eefca` | The choice-free Hartogs formulation and nonunital maps; the finite-congruence closure; the invisible equation `X^m = ω^γ + 1`; class-indexed derivations; the quantitative criterion; the model `A^08_κ` for every infinite `κ` (Section 11.3). Files `08-small-rings-*`. |
| **09** | *Set-Sized Shadows of Omnific Integers* (20) | `37eefca` | Direct division of arbitrary elements; the model `A^09_λ` with residue fields, `≥ λ` non-arithmetic maximal ideals and `ℵ1` generators (Section 11.4); Gaussian ramification. Files `09-set-shadows-*`. |
| **10** | *Set-Sized Shadows of Omnific Arithmetic* (26) | `a5c2a97` | The theorem over any set field including maps on `Π_K`; the quantitative bound; endomorphisms; numerical polynomials, all-modulus congruences, `p`-adic completion and characters, lattice rigidity (Section 15). Files `10-omnific-arithmetic-*`. |
| **11** | *What Set-Sized Algebra Can See of the Omnific Integers* (20) | `37eefca` | Pairwise-difference families; the localization and presentation calculus; the extension criterion (Theorem 9.1(iii)); the coinitiality theorem; residual targets; the ordinal ring and MathOverflow 188430 (Section 16). Files `11-set-sized-algebra-*`. |

- **Base and routes.** 06's coefficient-ring theorem over any set field `K`
  (also proved by 07 and 10) is the most general statement; its scaled-field
  collision lemma, of which 03's field bound is a special case, gives the sharp
  cardinal bounds where counting monomials does not. The proof of Theorem 5.1
  is written in 08's choice-free Hartogs form, with 08's and 10's nonunital
  forms and 06's direct module argument. 04's and 05's explicit telescope,
  09's and 10's direct division, 11's pairwise-difference families and 07's
  weighted certificates are kept as second routes.
- **Printed once:** support gaps, common monomial divisors, clearing, fraction
  fields (Section 3); the telescope and its finite truncation (Lemma 4.3); set-sized
  quotients (Theorem 6.2), completions (Theorem 6.10), modules (Theorem 7.1),
  derivations (Theorem 7.3), the invisible prime `ω^√2 + ω + 1` (Corollary 6.8,
  primality imported from L'Innocente–Mantova, Theorem B); the support threshold
  (Theorem 9.1: 11's formulation with 04's negative side); the finite-support
  augmentation (03, 04, 09, 11).
- **Renamed symbols** (Section 2.4): the purely infinite ideal is the
  repository's `Π` (was `I`, `𝒥_k`, `𝔍`, `𝔓`); the constant term is `ct` (was
  `c_0`, `π`, `ε_D`); 10's shadow map `Π` is `ct_*`; 06's `L_a` and 07's `𝓕_a`
  are `𝓕_a`; 07's localization `L_a` is `Oz[ω^{-a}]`, its `B_a` is `𝒬_a` and
  its compression `E_a` is `Ψ_a`; 03's normalizations `B, C` are `𝒩, 𝒩_C` and its
  `Int_F(A)` is `IC_F(A)` (`Int` is 10's integer-valued polynomials); 09's `Og`
  and `No(i)` are `Oz[i]` and `No[i]`; the set-sized constructions carry their
  source number (`A^03_κ`, `A^06_κ`, `A^08_κ`, `A^09_λ`, `R^11_{Γ,<κ}`).
- **Sign convention** (Section 2.2): large monomials, `ω^γ` infinite for
  `γ > 0`. The foundations report defines `Oz = Π ⊕ Z` (`found:eq:omnific`);
  the trigonometry report (`trigonometry:eq:split`) describes the same `Π` by
  negative `t`-exponents because it writes `t = ω^{-1}`.
- **Foundations.** NBG with choice for sets. 04, 06 and 09 (and 05) state
  global choice; no source uses it.

## Results added in the merge

Each is marked `[merge]` in the text and has a complete proof from the
sources' lemmas.

- **The field bound** for an arbitrary subfield of a fixed-group Hahn field
  (Proposition 10.3), generalizing 03's theorem through 06's collision lemma.
- **Exact fixed-group thresholds** (Examples 10.4, 10.5): in 04's example
  `Q ⊕_lex Q` the least detecting target has exactly `2^ℵ0` elements (04's
  question on optimal small targets, answered for its own example), and with
  rational coefficients the exact threshold `2^ℵ0` exceeds all the monomial and
  weighted counts of 04, 07 and 10, which shows in ZFC that 10's bound need
  not be attained (10 asks when it is).
- **`κ^{<κ}` in ZFC** (Lemma 11.10, Theorem 11.11, Proposition 11.23): the
  rings of 06 and of 11's lexicographic example (coefficient field of size at
  most `max(κ, 2^ℵ0)`, which contains 11's hypothesis `|K| ≤ κ`) have size
  `κ^{<κ}`, and that is their exact detection threshold; 06 and 11 prove
  exactness only under `κ^{<κ} = κ`. This answers the first half of 06's question on cardinal
  arithmetic; 08 answers the second half (a ring of size exactly `κ`).
- **The organizing theorem** (Theorem 10.10): for all five constructions the
  exact threshold equals the size of the ring, with the reconciliation of the
  realized cardinals in Remark 10.11 (`A^06_{ℵ1} ≅ A^03_{ℵ1}`; 03 and 09
  realize exactly the `θ` with `θ^ℵ0 = θ`).
- **The homological package for all five constructions** (Theorems 12.2,
  12.3), with `Ext¹` and `Ext²` thresholds equal to the size of the ring; for
  06's ring this corrects "exact `κ` under `κ^{<κ} = κ`" to "exact `κ^{<κ}` in
  ZFC".
- 08's criterion with the field-bound hypothesis (Theorem 10.7), the
  finite-side extension criterion (Theorem 9.1(iv)), `No ↪ Frac(Oz/P)` for
  primes `P ⊉ Π` (Remark 13.13), and explicit elements of `𝒩 \ Oz` from 08's
  equation (Remark 14.27).

## What the report claims

Let `K` be a set field, `D ⊆ K` a unital subring and `Π_K` the normal forms with
strictly positive set support and coefficients in `K`.

- **Theorem A (Theorem 5.1).** Every additive multiplicative map from
  `D + Π_K` to a set-sized ring (noncommutative, nonreduced, nonunital allowed)
  kills `Π_K` and factors uniquely through `ct`; every set-sized module is
  annihilated by `Π_K`. For `Oz` the only unital map is `x ↦ ct(x)1`;
  nonunital maps correspond to idempotents; unital maps from `Oz[i]` correspond
  to square roots of `−1` (Corollaries 5.2, 5.3). Set-sized quotients are
  exactly `ct⁻¹(𝔞)`, for `Oz` the ideals `Π` and `nOz` (Theorem 6.2); every class
  quotient has small reflection `D/ct(J)` (Theorem 6.1).
- **Theorem B (Theorems 8.2, 9.1).** Standard part is universal on `D + 𝔪_k`
  and on the finite surreal and surcomplex rings (04). Supports of size at most
  any infinite cardinal suffice for Theorem A; finite supports admit the
  augmentation `Σ c_g ω^g ↦ Σ c_g`, and a map on the finite-support ring extends
  to countable supports iff it factors through `ct` (the criterion is 11's; that
  the augmentation does not extend is 04's and 11's).
- **Theorem C (Theorem 10.10).** For the five set-sized rings of Section 11,
  four integer parts inside `Oz` of sizes `κ^ℵ0` (03), `κ^{<κ}` (06), `κ` (08,
  every infinite `κ`) and `λ` with `λ^ℵ0 = λ` (09), and 11's lexicographic Hahn
  ring of size `κ^{<κ}`, the least ring or module detecting any nonzero purely
  infinite element has exactly the size of the ring, in ZFC. Generator counts:
  `cf κ` (03, 08), `κ` (06 and 11's ring), `ℵ1` (09); no general law is
  stated. 09 adds residue fields of size `λ`, at least `λ` non-arithmetic maximal
  ideals and `Jac = 0` (Theorem 11.20).
- **Theorem D (Proposition 10.3, Examples 10.4–10.5).** The field bound and the
  exact fixed-group thresholds above.
- **Theorem E (Section 13, from 07 and one proposition of 06).** Inverting a
  nonzero purely infinite element forces an explicit copy of `No`
  (Theorems 13.4, 13.7); `Oz/(1+ω^a)` has no nonzero set-sized image yet
  contains an algebraically closed field containing `No[i]`, exact cyclotomic
  algebras (Theorem 13.15) and the Cantor algebra `LC(Z_2, E_a)`
  (Theorem 13.19), so it is not a domain, not local and not Noetherian.
- **Theorem F (Section 14, from 03 and 08).** `Oz* = No`; the integral closure
  `𝒩` is proper, fine-dense, of zero conductor and not set-generated
  (Theorems 14.5, 14.12); constant slices, the complexification defect killed by
  `2` (Proposition 14.18), no finite quotients (Theorem 14.20), no nontrivial
  set-valued valuation of `No` containing `Oz` (Theorem 14.22); for `γ > 0` and
  `m ≥ 2`, `X^m = ω^γ + 1` has no root in `Oz[i]` but the root `1` in every
  set-sized image (Theorem 14.25).
- **Theorem G (Section 15, from 10).** `Num_r(Oz) = Π[X] ⊕ Int(Z^r)` with
  universal set-sized image `Int(Z^r)` (Theorem 15.7); the Newton
  least-common-multiple criterion for congruences modulo every omnific integer
  (Theorem 15.14); the `p`-adic completion `C(Z_p^r, Z_p)` and its characters,
  most not evaluations (Corollary 15.20, Theorem 15.22); rational self-maps of
  `Oz`, `Oz[i]` are polynomial, nonlinear images have holes of every surreal
  radius, and rational bijections are affine (Theorems 15.27, 15.28,
  Corollary 15.29).
- **Theorem H (Theorem 16.1, from 11).** The Grothendieck ring of the ordinals
  under natural operations is not a quotient of `Oz` (every unital ring map
  from `Oz` to it has image `Z`), answering the quotient
  addendum of MathOverflow question 188430 (Jesse Elliott, 2014) negatively; the
  question's only answer (Eric Wofsey) concerns transcendence degree.

## What the report does not claim

- All eight sources are AI-assisted, unrefereed drafts that call their main
  results candidate original; priority is not certified, no named conjecture
  (Conway's refinement problem, factorization, GCD) is claimed solved, and
  nothing is formalized: the repository has no omnific Lean module and
  `docs/FORMALIZATION.md` maps none of these labels. The merge results are no
  more refereed than the sources.
- The universal theorem is not an isomorphism `Oz ≅ Z`, does not classify class
  ideals, class modules, automorphisms or factorizations, concerns only
  multiplicative maps (additive coefficient extraction detects `ω^γ`), and fails
  verbatim over every fixed set-sized exponent group. Size alone and
  divisibility alone do not prove it.
- The exact thresholds are proved for the five constructions and the two
  fixed-group examples only; the general fixed-group question (Question 17.1)
  stays open, and no classification of exponent groups or support restrictions
  is claimed.
- `pd_A Z` is known only to be at least `2` (Question 17.3); nonarithmetic class
  primes are treated conditionally and their existence is not claimed
  (Question 17.4); the idempotents and primes of `Oz/(1+ω^a)` are not classified.
- The support-threshold theorem is stated for `k ∈ {R, C}` as in 04 and 11,
  and no Gaussian analogue of 10's congruence criterion is given.
- Section 17.2 keeps every limitation stated by a source, numbered per source:
  03 (19 items), 04 (14), 06 (14), 07 (13), 08 (13), 09 (12), 10 (12), 11 (12),
  and 5 for the merge (114 in all). Section 17.3 lists eleven questions,
  merging duplicates across sources, with their status: one answered
  (Question 17.2), one answered only for specific examples (Question 17.1),
  one settled for cardinal support bounds only (Question 17.8), eight open.
- The finite checks validate finite identities only; they verify no infinite
  support, class-size, cardinal, maximal-ideal, `Ext` or priority statement.

## Corrections and stale statements

- **Repository searches.** The audits of 06 (`06-universal-quotient-source_audit.md`,
  §1), 08 and 11 report a repository code search for "omnific" with no hits,
  and 09 an incomplete result. *Correction (23 September 2026):* at their pins
  the repository already defined `Oz = Π ⊕ Z` at `found:eq:omnific` in the
  foundations report and used omnific integers in the trigonometry,
  gamma–zeta, analysis and euclidean-three-space reports; what it lacked was a
  report on omnific arithmetic. It now has two (this one and the sibling).
- **Prior manuscripts.** 03's `SOURCE_NOTES` calls its companion draft
  (`omnific_integers(1).tex`) not redistributed, and 04's audit calls its prior
  manuscript (`omnific_integers_diophantine.tex`) absent from the pinned tree.
  They are manuscripts 05 and 02 of the sibling report.
- **Literature.** 09 (text and audit) credits "Proposition 8.2.1 on
  separated-scale division" of L'Innocente–Mantova; the separated-scale
  factorization is their Fact 8.0.1 (Gonshor's Theorem 8.6) with the example on
  p. 46, as 11 cites, and Proposition 8.2.1 is the truncation criterion for
  divisibility that 08 cites (Section 4.2).
- **Sources.** 03's source prints "C e B[i]" for `C ≠ B[i]` (Proposition 14.18);
  09's hypothesis `λ ≥ 2^ℵ0` follows from `λ^ℵ0 = λ` (Section 11.4); 04's remark
  that its `Q ⊕_lex Q` example involves "only a countable family" is true but
  misleading (Remark 10.6); 06's remark on `|R_κ/xR_κ|` needs no cardinal
  hypothesis (Section 12). No source contains a false theorem.
- 07's audit describes the staging directory at its pin (Gamma–zeta archives);
  it is a snapshot statement.
- The shipped audit files keep these statements verbatim. Several delivered
  files name files that are not shipped: the source `.tex` and `.pdf` files
  (`article.tex`, `omnific_small_quotients.tex`, `omnific_set_shadows.tex`,
  and others), the hash blocks of `04-universal-residue-build_report.json` and
  `06-universal-quotient-build_audit.json`, and the original script names used
  by the Makefiles and `build.sh` files.

## Relation to the neighbouring reports

- [`omnific-diophantine-geometry`](../omnific-diophantine-geometry/) (sources
  01, 02, 05) is the sibling report, written concurrently. It quotes 05's
  universal set-sized quotient theorem and refers here for the proof, which is
  the explicit-telescope route of Theorem 5.1. 05's "exact size boundary"
  question, kept there, is answered here by the constructions of Section 11 and
  Theorem 10.10 for specific integer parts; the general version is Question
  17.1. The preliminaries (normal form, `ct`, support gaps, `Frac Oz = No`)
  overlap Sections 2–3.
- [`foundations`](../../foundations-and-computation/foundations/) defines
  `Oz = Π ⊕ Z` (`found:eq:omnific`), whose notation is used here.
- [`euclidean-three-space`](../euclidean-three-space/), Part III: every class
  homomorphism from `SO(3, No)` to a set-sized group factors through standard
  part (`e3:cut:thm:smallquotient`, `e3:cut:cor:onlyimage`). Theorem 8.2 here is
  the ring analogue on the finite side; neither implies the other.
- [`first-kappa-coefficients`](../../surcomplex/first-kappa-coefficients/)
  proves closedness of `<κ`-support Hahn fields for every uncountable `κ`
  (`fkc:thm:main`), which contains the closure step of Proposition 11.8; the
  thresholds here are not about its omitted types.
- [`trigonometry`](../../surcomplex/trigonometry/) uses `2πOz = Π + 2πZ` as a
  period kernel and the same `Π` with the opposite `t`-exponent sign.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 90 pages with no errors, warnings, undefined references or
overfull boxes. Build in a copy of the directory and do not commit the
auxiliary files.

The eight check programs were rerun for this merge on copies (Python 3.14.4,
SymPy 1.14.0); all pass and reproduce the recorded outputs up to line endings
and the recorded Python version. **Several write files by default**: 04 always
writes `verification.json` next to the script, 06 and 09 do so unless given
`--output`, and 07 writes `verification_results.json` in the working directory
unless given `--output`. Run them with an explicit output in a scratch
directory, and run 04 on a copy:

```sh
cd docs/surreal/set-sized-quotients-of-omnific-integers
T=$(mktemp -d)
python code/03-cardinality-normalization-verify_identities.py > "$T/03.txt"   # 2,362 checks; = data/03-...
cp code/04-universal-residue-verify_identities.py "$T/" && python "$T/04-universal-residue-verify_identities.py" > /dev/null   # writes $T/verification.json
python code/06-universal-quotient-verify.py --output "$T/06.json"             # 17,586 assertions
pip install -r data/07-quotient-rigidity-requirements.txt                      # sympy==1.14.0, for 07 and 10
python code/07-quotient-rigidity-verify_finite.py --output "$T/07.json"       # 621 checks
python code/08-small-rings-finite_checks.py > "$T/08.txt"                     # 1,277 cases
python code/09-set-shadows-verify.py --output "$T/09.json"                    # 597 assertions
python code/10-omnific-arithmetic-checks.py > "$T/10.txt"                     # 171,395 checks, about 15 s
python code/11-set-sized-algebra-check_finite_identities.py --output "$T/11.json"   # 1,858 checks
```

The shipped `04-…-Makefile`, `06-…-Makefile`, `10-…-Makefile`,
`09-set-shadows-build.sh` and `11-set-sized-algebra-build.sh` use the original
package file names (`verify.py`, `article.tex`, `omnific_set_shadows.tex`,
`code/check_finite_identities.py`, …) and do not run as shipped; they are kept
as provenance.

## Staged for the next merge

Placed in `cf350b1` (the batch following this report), pinned at `71e9606`,
and not described by `article.tex`:

```
15-set-sized-representations-SOURCE_AUDIT.md
code/12-homological-dimension-build.sh, 12-homological-dimension-check_boolean_tor.py
code/13-small-target-rigidity-verify.py
code/14-arithmetic-tensors-build.py, 14-arithmetic-tensors-verify.py
code/15-set-sized-representations-verify_identities.py
code/16-fresh-scale-verify_finite.py
data/12-homological-dimension-audit_results.json
data/13-small-target-rigidity-source_manifest.json, 13-small-target-rigidity-verification.txt
data/14-arithmetic-tensors-provenance.json, 14-arithmetic-tensors-requirements.txt,
     14-arithmetic-tensors-verification.json
data/15-set-sized-representations-finite_checks.json
data/16-fresh-scale-requirements.txt, 16-fresh-scale-verification_results.txt
```
