# Omnific Integers and Omnific–Diophantine Geometry

**Retractions, rigidity, definability, and infinite families**
Merged research report, from seven manuscripts written independently: three
dated 22 September 2026 (batch items 01, 02 and 05 of the batch placed in
`be06fc8`), two dated 23 September 2026 (batch items 01 and 07 of the batch
placed in `cf350b1`, numbered 06 and 07 here), and two more dated 23 September
2026 (batch items 01 and 02 of the batch placed in `a4dcb91`, numbered 08 and
09 here). Prepared for Vladimir Reshetnikov.

```
article.tex                        the report, standalone LaTeX with an internal bibliography
article.pdf                        the compiled report, 122 pages
README.md                          this guide
RECONCILIATION.md                  the source comparisons and precise proof-review scope
02-diophantine-PROVENANCE.md       source 02's provenance and verification-boundary note, as delivered
05-diophantine-rigidity-BUILD.md   source 05's build and check instructions, as delivered
06-definability-reconstruction-SOURCE_AUDIT.md   source 06's source and novelty audit, as delivered
08-fractions-SOURCE_AUDIT.md       source 08's source and novelty audit, as delivered
code/
  01-diophantine-geometry-verification.py   source 01 checks (writes a JSON report; see below)
  01-diophantine-geometry-build.sh, .ps1    source 01's build scripts (they compile source 01's
                                            own file name and do not build this report)
  02-diophantine-verify_examples.py         source 02 checks
  05-diophantine-rigidity-verify_examples.py  source 05 checks
  06-definability-reconstruction-verify.py  source 06 checks (writes JSON only to --output)
  06-definability-reconstruction-Makefile   source 06's build and check targets (delivered
                                            paths; they do not build this report)
  07-defining-arithmetic-verify.py          source 07 checks (standard library only; prints)
  07-defining-arithmetic-build.sh           source 07's build script (compiles its own
                                            article.tex in its own directory; not this report)
  08-fractions-verify.py                    source 08 checks (writes JSON; see below)
  08-fractions-Makefile                     source 08's build and check targets (delivered
                                            file names; they do not build this report)
  09-fraction-fibres-verify_examples.py     source 09 checks (always writes JSON; see below)
  09-fraction-fibres-build.sh, .ps1         source 09's build scripts (they compile source 09's
                                            own file name and do not build this report)
data/
  01-diophantine-geometry-verification_report.json   source 01's recorded run
  02-diophantine-verification.txt                    source 02's recorded run
  05-diophantine-rigidity-verification.txt           source 05's recorded run
  06-definability-reconstruction-verification.json   source 06's recorded run
  06-definability-reconstruction-build_report.json   source 06's build summary for its own article
  07-defining-arithmetic-verification.txt            source 07's recorded run
  08-fractions-verification.json                     source 08's recorded run
  08-fractions-build_audit.json                      source 08's build record for its own article
  09-fraction-fibres-verification_report.json        source 09's recorded run
  01-, 02-, 05-, 06-, 08-, 09-...-requirements.txt   each pins sympy==1.14.0
```

Every label in `article.tex` carries the prefix `odg:` (310 labels, counting
both `\label{…}` and `\label[type]{…}`): the 150 labels of the three-source
assembly `bbdd536`, none renamed or removed; nine aliases kept by the
elementary review merged from upstream; 69 labels added by the batch-25
integration; and 82 labels added by the batch-27 integration. The material of
sources 06 and 07 carries the sub-prefix `odg:def:` (63 labels), the fiber and
norm results printed from the sibling report's manuscript 13 carry `odg:dec:`
(6 labels), and the material of sources 08 and 09 carries `odg:frac:` (82
labels). Two older labels, `odg:def:rings` and `odg:def:primitive`, name
Definitions 2.1 and 7.7 and predate the sub-prefix.

The elementary review (`7784f7f`, `8f1527c`), written in parallel with the
assembly and merged into it in `1186c11`, added four results, which the
assembly also contains (common multiples combined with projective clearing),
and support and size clarifications, which are retained. The assembly renamed
or combined nine locations cited by that review; their old labels (`odg:cor:Jglobal`, `odg:cor:commonmultiples`,
`odg:prop:nogcd`, `odg:cor:powers`, `odg:cor:Jdefinable`, `odg:eq:nA`,
`odg:eq:pellmod8`, `odg:app:dependencies`, `odg:app:audit`) are kept as
aliases on the new locations, so all 81 labels of the review resolve. A later
proof review of Sections 5–7 (`f0bdcf3`) extended one-variable and
separated-power rigidity to complex coefficients and corrected Remark 7.5; a
further review of Sections 8–10 (`40c09a3`, `58cd8e1`) expanded their proofs
without adding or renumbering statements. The later reviews `25e372c` and `3dd4e2c` cover the former Sections 11–12,
now Sections 14 and 16, including real-coefficient specialization and the finite
factorization proof of the two-term root obstruction. These reviews exclude the batch-25
material (Sections 11–13, the Section 6 results of sources 07 and 13, and
Remark 10.5). A subsequent pass reviews Section 11: leading degrees, the
quadratic ideal predicate, Pell divisibility, intersectivity and the
order-free integer-defining system. It adds boundary examples for intermediate
rings and expands the finite congruence arguments. A further pass reviews
Section 12: the detector, ideal test, constant-term graph, homomorphisms and
number-field extension. Its root hypothesis already gives an existential
ideal and graph. Section 13 now also has a proof review of reconstruction,
automorphisms and logical consequences. It extends coefficient reconstruction
to the number-field ideal predicates and the c.e.-set classification to
all characteristic-zero coefficient fields using finite equation systems.
The new material in Sections 6 and 10 still needs review.
A further pass reviews Sections 15.1–15.4: denominator ideals, least
denominators, the multiplier theorem and the affine denominator dichotomy.
The rest of the batch-27 material remains unreviewed: Sections 15.5–15.12,
the additions to Section 17, Section 18.3 and Questions 18.12–18.16. Inserting
Section 15 moved the former Sections 15–17 to 16–18; statement numbers in
Sections 1–14 are unchanged. See [RECONCILIATION.md](RECONCILIATION.md) for the
elementary claim correspondence, these proof reviews and the remaining review
boundary.

The article has 143 standard results (51 theorems, 31 propositions, 25 lemmas,
36 corollaries), of which 39 are in Section 15. The
[ledger](../../FORMALIZATION.md) indexes all 143 standard results of the
seven-source assembly by `odg:` label, all **Pending**; no implementation
mapping cites an `odg:` label, and no Lean code about omnific integers exists
in the repository.

## Seven sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **01** | *Omnific Integers and Omnific–Diophantine Geometry* | `2cb9c02` | The base text and structure; the exhaustive quadratic-level dichotomy including degenerate forms (Theorem 8.1); the five-auxiliary three-square guard (Theorem 10.3); rational directions (Theorem 14.5); no real point at infinity (Theorem 9.6); symmetric matrices (Corollary 9.5); the elementary uniqueness of `ct` (Proposition 3.5). Files prefixed `01-diophantine-geometry-`. |
| **02** | *Omnific Integers and Diophantine Geometry* | `2cb9c02` | Exact decomposable fibers (Theorem 6.2(a)); bounded semialgebraic rigidity (Theorem 9.2); decidable homogeneous existence with sign conditions (Theorem 14.2(b)); the square-discriminant criterion (Theorem 15.1); the general pair without a gcd (Theorem 4.10); the explicit Lorentz matrix and the unipotent subgroup (Corollary 8.4); nilpotent tests and mixed gcds. Files prefixed `02-diophantine-`. |
| **05** | *Omnific Integers and Diophantine Rigidity* | `2cb9c02` | Binary rigidity over `C` (Theorem 6.7); Euler derivations (Section 7); separated powers (Theorem 7.4) and unimodular Fermat (Theorem 7.9); the four-square definition of `Z` (Theorem 10.4); a failed existential induction (Theorem 10.10); failed lifting (Proposition 15.4, Example 15.5); finite-support specialization (Theorem 14.7). Also the universal set-sized quotient theorem, which is **printed in the sibling report** and only quoted here (Cited theorem 3.6). Files prefixed `05-diophantine-rigidity-`. |
| **06** | *Definable Arithmetic and Coefficient Reconstruction in Omnific Integer Rings* | `71e9606` | Base of Sections 11–13: the one-witness Diophantine definition of `Π` (Theorem 11.2), the Diophantine graph of `ct` (Theorem 12.8), all homomorphisms preserve `ct` (Theorem 12.12), the multiplier identity (Theorem 13.2), reconstruction of `R`, `No`, order and standard part from the pure ring `Oz` (Theorem 13.4), automorphisms fix `R` (Theorem 13.6), the phase twist and the real–Gaussian asymmetry (Theorem 13.10), c.e. sets (Theorem 13.11); its quintic is Remark 11.10. Files prefixed `06-definability-reconstruction-`. |
| **07** | *Defining Arithmetic Inside Omnific Integers* | `71e9606` | The order-free system in intermediate rings (Theorem 11.9, with 06); the augmentation root detector (Theorem 12.1) and the constant-term detector (Theorem 12.2); support bounds (Proposition 12.3); the ideal test (Theorem 12.6); number-field coefficient rings (Theorem 12.14); norm rigidity over any base field (in Theorem 6.15); recursive saturation (Theorem 13.15); its quartic is Remark 10.5. Files prefixed `07-defining-arithmetic-`. |
| **08** | *Fractions of Omnific Integers: Rational Specialization, Lowest Terms, Denominator Ideals, and Scale Extensions* | `9a385d3` | Base of Section 15: real constants (Theorem 15.7); the multiplier theorem for any retraction and any number of coordinates (Theorem 15.11); the classification of all representations of rational-function tuples at any `0 ≠ t ∈ Π` (Theorem 15.18, Corollaries 15.19–15.21); no lcm (Example 15.27); rational curves (Corollary 15.28); the localization at `Π` and independent residues (Proposition 15.40, Theorem 15.42); polynomial models, the enlargement and scale defects, nonflatness and `Tor_1` (Theorems 15.45–15.47, Proposition 15.48); monomial denominators (Proposition 15.50); the Gaussian dichotomy (Theorem 15.54). Files prefixed `08-fractions-`. |
| **09** | *Omnific Fractions: Rationality, Denominator Ideals, and Dense Arithmetic Fibres* | `9a385d3` | The calculus of denominator ideals and least denominators (Propositions 15.2, 15.3); the unimodular region `𝒱` and its dichotomy (Theorem 15.15); nearly equal values of opposite type (Example 15.24); local density (Proposition 15.26); fibers as congruence orbits (Theorem 15.32, Corollary 15.33); set-wise focusing (Theorem 15.35), dense fibers (Corollaries 15.36, 15.37) and nowhere continuity (Corollary 15.38). Its pair multiplier theorem and its one-scale classification are special cases of 08's Theorems 15.11 and 15.18 and are credited there. Files prefixed `09-fraction-fibres-`. |

Batch-25 item 03 is manuscript 13 of the sibling report
[`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/),
where its files are shipped with the prefix `13-small-target-rigidity-`. Its
fiber and norm results (its Sections 8–9) are printed here once, tagged `[13]`:
the Gaussian fiber theorem (Theorem 6.3), the converse of the kernel criterion
(Corollary 6.4), the real-kernel remark (Remark 6.5), a rank-deficient level
(Example 6.6) and étale norms (in Theorem 6.15). Its real fiber theorem is
Theorem 6.2(a), printed once. It is not counted among this report's seven
sources. Batch-25 item 04 is the sibling report's manuscript 14 (files
`14-arithmetic-tensors-` there). Its criterion for unimodular constant
directions over `Z` and `Z[i]` is printed here once, tagged `[14]`, as
Corollary 15.55, which is also the constant case of source 08's Gaussian
dichotomy. The sibling report says that this criterion is printed here with
Theorem 14.5; before this integration it was not.

The source manuscripts are not shipped; their code, data, source 02's
provenance note, source 05's build note and the source audits of sources 06
and 08 are. The delivered READMEs of sources 06–09 are not shipped. The pin
`2cb9c02` is 107 commits before `be06fc8`; the pin `71e9606` also precedes
`be06fc8`, so sources 06 and 07 did not see this report or its sibling. The pin
`9a385d3` of sources 08 and 09 is 35 commits before `a4dcb91`; at that pin this
report had only sources 01, 02 and 05. The checksum manifests of sources 01 and
09 are not shipped because they list the delivered file names.

**Why one report.** Sources 01, 02 and 05 prove the same spine: normal forms,
the rings `B_R ⊃ Oz = Z ⊕ Π`, degree and units, the floor, the retraction `ct`
and its congruences, the full-class common divisor and clearing,
non-atomicity, transfer and Hilbert's tenth problem, the Smith criterion, the
unit lemma with binary and Pell rigidity, homogeneous scaling, polynomial
arcs, and the unimodular Pythagorean family. It is printed once (Sections
2–6), naming the sources of each statement. Source 01 is the base because it
has the weakest hypotheses on most shared statements. Where another source is
more general, its statement is printed and the others are recorded as special
cases: 02's exact fibers (01's rank-`n` theorem is case (b) of Theorem 6.2),
and 05's complex binary theorem. Sources 06 and 07 are twins: they share the
same order-free system (three equations, five witnesses, degrees 3, 3, 7), the
same intersective polynomial and the same Pell divisibility argument, and each
has decisive results the other lacks. They answer this report's question on an
existential definition of `Π` and extend its definability section, so they are
added as Sections 11–13 after Section 10, with source 06 as base. Sources 08
and 09 prove the same core theorem: for a tuple unimodular over `B_R`, the
constant vector decides whether the admissible multipliers form `Oz` or `Π`.
Source 08 is the base because it has the weaker hypotheses (any retraction, any
number of coordinates, any `0 ≠ t ∈ Π`, against 09's pairs and monomials
`t = ω^α`). The core generalizes Theorems 4.10 and 14.5 and fills the gap
stated after Theorem 14.5. So the two are added as one new Section 15,
directly after Section 14, with the label sub-prefix `odg:frac:`. None of the
seven sources, nor source 13 or 14, contradicts another.

**Printed once from sources 06, 07 and 13.** The units lemma, Pell rigidity
(with the Gaussian solution `(i, i)`), Pell divisibility, the intersective
polynomial and its proof, the order-free system, transfer and Hilbert's tenth
problem, the collapse obstruction, `Frac(Oz) = No`, the zero Pell fiber, the
cubic norm, the negative-exponent Pell solutions and the omitted types. Source
07's quartic is source 05's up to a substitution and is printed once as Remark
10.5.

**Printed once from sources 08 and 09.** Their re-proofs of the rings and
units, the common divisor, `Π² = Π` and its non-generation, `Frac(Oz) = No`,
the floor and ordered division stay in Sections 2–4. Within Section 15, the
unimodular-fraction lemma (Lemma 15.4), real constants (Theorem 15.7), ordinary
denominators (Proposition 15.5), the one-function criterion (Corollary 15.21),
the monomial criterion (Proposition 15.50) and the Gaussian fraction field are
printed once, naming both. 09's pair multiplier theorem and one-scale
classification are credited as special cases of Theorems 15.11 and 15.18, and
09's region `𝒱` is kept as the formulation of Theorem 15.15. The two example
tables are merged into Example 15.23. Source 08's conic example is Proposition
14.4 with source 01's witness and is not reprinted.

**Kept twice, as different proofs.** Uniqueness of `ct`: 01's divisibility
proof (Proposition 3.5) and 05's route through the set-sized quotient theorem.
Homogeneous systems: 01's leading-coefficient proof, which needs no quantifier
elimination, and 02's Tarski proof, which handles sign conditions and
decidability (Theorem 14.2). The pair `(√2ω, ω)` without a gcd: 02's general
proof (Theorem 4.10) and 01's degree proof, which works in any divisible
workspace (Remark 4.11). Quartic definitions of `Z`: 01's (five auxiliary
variables, three squares) and 05's (six auxiliary variables, four squares).
Pell divisibility: 07's permutation argument and 06's finite-ring argument
(Lemma 11.6). The universal definition of `Π` and the `∃⁵∀²`/`∀²∃⁵`
definitions of the graph of `ct` of source 07 (Corollary 12.7, Remark 12.11),
next to source 06's existential ones. The Bézout lift in Theorem 15.11: 08's
one-line formula and 09's adjustment of constants (Remark 15.12). The absence
of a gcd: the halving argument of 08 and 09 (Remark 15.8), next to the two
routes for Theorem 4.10. Two elements outside the fraction field of one
workspace: 08's exponential series and 09's factorial-gap series (Example
15.52).

**Added in the merge**, each tagged `[merge]` with a complete proof: an
explicit identity giving the divisibility step of the separated-power proof
without the quotient ring (Remark 7.5, for derivations killing `a`, `b` and
`c`, as corrected by the later review; checked symbolically for general
`a, b` and `2 ≤ m, n ≤ 7`); the failure of existential induction in the pure
ring language, via `Std` (Remark 10.11); a quartic with six witnesses for the
graph of `ct` in `Oz` (Corollary 12.9, replacing source 06's degree-ten,
eight-witness polynomial); Diophantine definitions of the ideal and of the
graph of `ct` over number-field coefficient rings through another radicand
(Remark 12.15, strengthened by the later review: the detector
hypothesis already supplies the required square root); the combined étale norm theorem in intermediate rings (Theorem
6.15); the collapse of source 06's quintic over `Oz[i]` at `x = ω` (Remark
11.10); and the Gaussian point `(1 + ω, iω)` of `X + iY = 1` (Remark 6.5). The
degrees, witness identities and collapses were checked with SymPy when the
merge was made. The batch-27 merge adds three items, also tagged `[merge]`
with complete proofs. Remark 15.8: the conclusion of Theorem 4.10 holds in
every fixed workspace `Oz_Γ`, by the halving route. Corollary 15.30: source
08's curve criterion stated for homogeneous systems, the partial answer to
Question 18.3. Remark 15.39: comparison with the omnific groups report. The
focusing matrices `F_{x,b}` are transposes of that report's non-elementary
unipotents; they lie outside `E_2(Oz)` at centres with irrational standard
part; and `E_2(Oz)·∞` is not dense although `K·∞` is, so the density of
Corollary 15.36 needs non-elementary matrices. Its certificates, the table of
Example 15.23 and the second Bézout lift were checked with SymPy.

**Notation.** The purely infinite ideal is `Π`, the letter used by the
foundations report (`found:eq:omnific`); the sources wrote `𝒥` (01), `𝓘`
(02, 05, 06), `I_k^+(Γ)` (07) and `J` (13). Exponents follow the Conway
normal-form convention: `ω^γ` is infinite for `γ > 0`, so `Π` consists of the
normal forms supported on **positive** exponents. The trigonometry report
writes the same class with **negative** `t`-exponents (`t = ω^(-1)`, at
`trigonometry:eq:split`); Section 1.4 prints the translation. Other renamings
resolve collisions: the Lorentz Gram matrix is `G` (02's `J`, which also named
an index set and an ideal), the guard polynomial is `Ψ_n` (01's `G_n`), the
Euler derivation is `∂_λ` (05's `D_λ`, which clashed with the Pell `D`), the
Fermat exponent is `n` (05's `p`), and a set-sized target ring is `S` (05's
`A`, which was also 01's name for `Oz`). In Sections 11–13 the coefficient
field is `𝕜` (the sources' `k`; `k` is an index here), the exponent group is
`Γ` (06's `G`, the Gram matrix here), the coefficient ring is `𝔬` (the
sources' `D`, the Pell parameter here), the rings are `𝒜_𝕜(Γ)`, `Π_𝕜(Γ)` and
`ℛ_𝔬(𝕜, Γ) = 𝔬 + Π_𝕜(Γ)`, the Gaussian omnific integers are `Oz[i]`, and
the intersective polynomial `(T²−13)(T²−17)(T²−221)` is `Λ` (06's `H`, 07's
`P`). Source 07's constant definition `Φ` is `Ξ` here, because `Φ` is the
induction formula of Theorem 10.10. In Section 15 (conventions in Section
15.1) the purely infinite parameter is `t` (08's `τ` is the phase twist here),
projective coordinates put the denominator last (08 put it first), a point
other than `∞` is *affine* (09 says "finite", reserved here for bounded
surreals), the denominator ideal is `𝔇` (09's `D` is the Pell parameter), the
specialization is `sp` (09's `σ`), the congruence kernel of
`SL_2(Oz) → SL_2(Z)` is `K` (09's `Γ`, the exponent group here), the rational
residue is `res` on the localization `Oz_Π` (08's `ρ` on `𝒜`; `ρ = √2 − 1` and
`𝒜_𝕜(Γ)` here), the abstract pullback is `R_Z = c⁻¹(Z)` for a retraction
`c : R → R` (08's `A`, `B`; `A` is an intermediate ring and `B` a bilinear form
here), the polynomial models are `𝒫[X] = Z + X R[X]` (08's `A_τ`, `A_0`,
`A_m`), the focusing matrices are `F_{x,b} = I + b N_x` (09's `G_{x,b}`; `G` is
the Gram matrix), and 09's lemma "transvection" is Lemma 15.34, not Lemma 8.2.
The full per-source table is Table 1 in Appendix A.

## What the report claims

Numbers refer to the built `article.pdf`.

1. **Rings and integer part (Section 2).** `Oz`, `B_R = R ⊕ Π` and
   `B_C = B_R[i]` are domains; `ct` is a ring retraction onto `Z`, `R`, `C`
   (Proposition 2.2); units are `±1`, `R^×`, `C^×`, and bounded omnific
   integers are integers (Proposition 2.5); the exact floor, with the
   correction at a negative infinitesimal displacement (Theorem 2.7).
2. **Residues (Section 3).** `nOz = Π + nZ`, `n | x ⇔ n | ct(x)`,
   `∩ nOz = ∩ p^k Oz = Π` (Theorem 3.1); finite quotients are `Z/n`
   (Corollary 3.4); `ct` is the unique homomorphism to `Z` and endomorphisms
   preserve it (Proposition 3.5). The universal set-sized quotient theorem of
   source 05 is quoted as Cited theorem 3.6; Remark 3.7 notes that the Hartogs
   ordinal replaces 05's use of global choice.
3. **Full-class support (Section 4).** One monomial divides a whole set of
   purely infinite elements (Theorem 4.2); `Π² = Π`, `Π` is not generated by
   any set, `Oz` is not atomic (Corollary 4.3); `Frac(Oz) = No` (Theorem 4.6);
   `(t, rt)` has no gcd for `0 ≠ t ∈ Π`, irrational `r` (Theorem 4.10); the ring
   is not integrally closed (Proposition 4.12). These are full-class results.
4. **Transfer (Section 5).** An integer system has an omnific solution iff it
   has an integer one (Theorem 5.1); Hilbert's tenth problem over `Oz` is the
   ordinary one (Corollary 5.2); nonzero, positive and nonnegative are not
   positive-existentially definable (Proposition 5.3); linear systems are
   solved completely (Theorem 5.4, Theorem 5.5).
5. **Constant products (Section 6).** Exact fibers of decomposable equations
   at a nonzero level (Theorem 6.2), and over the Gaussian omnific integers
   `Oz[i]` (Theorem 6.3); the kernel criterion is exact when an ordinary point
   exists (Corollary 6.4); binary forms with two distinct projective factors
   over `C` at a level in `C^×` have only constant points in `B_C` (Theorem
   6.7); Pell rigidity for every `D ≠ 0` (Corollary 6.9), the full class for
   `x² − 2y² = 1` (Example 6.10), central conics (Corollary 6.12), norm forms
   for any `Q`-basis (Theorem 6.14), and nonzero norm equations of finite
   étale algebras over any subfield of the coefficient field in every
   intermediate ring, in particular over `Oz` and `Oz[i]` (Theorem 6.15).
6. **Separated powers and Fermat (Section 7).** For complex `a, b, c ≠ 0` and
   `m, n ≥ 2`, every `B_C`-solution of `ax^m + by^n = c` is constant (Theorem
   7.4; extending source 05's real case), so `y² = x³ + k` (`k ≠ 0`) and
   `x^m − y^n = c ≠ 0` have only ordinary omnific solutions (Corollary 7.6).
   For `n ≥ 3` a Fermat triple in `B_C`, with all three coordinates nonzero
   and generating the unit ideal, is constant (Theorem 7.9); with Wiles and
   Taylor–Wiles there is no unimodular omnific Fermat triple with all
   coordinates nonzero (Corollary 7.10), although `(1, 0, 1)` is unimodular.
   The threshold is sharp at `n = 2`.
7. **Quadratic levels (Section 8).** For integral `q` and `c ≠ 0`: ordinary
   points only in the nondegenerate definite case and in dimension at most
   two; injective linear families for degenerate `q`; injective quadratic
   families through every integer point for nondegenerate indefinite `q` in
   at least three variables (Theorem 8.1). The quadratic matrix orbits preserve
   the coordinate ideal, hence carry primitive integer points to unimodular
   omnific points. `(Π, +)` embeds in
   `ker(SO(q, Oz) → SO(q, Z))` (Corollary 8.4).
8. **Bounded geometry (Section 9).** Bounded semialgebraic sets (Theorem 9.2),
   definite levels (Corollary 9.3), `O_n(Oz)` = signed permutations
   (Corollary 9.4), symmetric matrices with constant `tr(M²)` (Corollary 9.5),
   no real point at infinity (Theorem 9.6). The set-sized transfer argument
   includes quantified ordered-ring formulas. Any definite real form has a
   finite integer isometry group, while the signed-permutation description
   is specific to standard Euclidean coordinates.
9. **Defining `Z` (Section 10).** Theorem 10.3 (five auxiliaries, defines
   `Z^n`) and Theorem 10.4 (six auxiliaries, defines `Z`; source 07's variant
   is Remark 10.5); `ct` and `Π` are first-order definable (Corollary 10.7);
   an explicit `Σ₁` induction instance fails (Theorem 10.10) while open
   induction holds.
   The workspace argument and the nonnegative domain of induction are explicit;
   an order-free semiring formula also defines exactly the ordinary naturals
   inside the nonnegative cone (Remark 10.11).
10. **Diophantine arithmetic (Section 11).** For a domain `𝔬 ⊆ 𝕜` with
    `√2 ∈ 𝕜 \ Frac(𝔬)`, `∃y (x² = 2y²)` defines `Π_𝕜(Γ)` in `ℛ_𝔬(𝕜, Γ)`, in
    particular `Π` in `Oz` and `Π_C` in `Oz[i]` (Theorem 11.2); homomorphisms
    preserve the ideal (Corollary 11.3); Pell rigidity in intermediate rings
    (Corollary 11.5); `Λ` is intersective and root-free in `Q(i)`
    (Proposition 11.8); one system of three equations with five witnesses
    defines `Z` in `Oz` and `Z[i]` in `Oz[i]`, and `𝔬` in every intermediate
    ring (Theorem 11.9); the natural numbers are Diophantine (Corollary 11.11).
11. **The constant term (Section 12).** An augmentation root detector
    (Theorem 12.1); `as = Λ(t)` is solvable exactly when `ct(a) ≠ 0` (Theorem
    12.2), with explicit support-controlled witnesses (Proposition 12.3,
    Example 12.4) and a counterexample without a root in the coefficient field
    (Remark 12.5); `Π` is the largest ideal whose quotient has no root of `Λ`
    (Theorem 12.6); the graph of `ct` is Diophantine (Theorem 12.8), in `Oz`
    by one quartic with six witnesses (Corollary 12.9); every unital
    homomorphism between such rings preserves `ct`, up to conjugation in the
    Gaussian case, without any size condition (Theorem 12.12); for subrings of
    a number field `K`, a tailored polynomial `Λ_K` gives the same constant
    definition and, with a root of `Λ_K` in `𝕜`, the detector (Lemma 12.13,
    Theorem 12.14). The same root hypothesis also gives a one-witness
    existential ideal and a six-witness existential graph (Remark 12.15):
    the square of that root supplies a suitable radicand.
12. **Reconstruction and logic (Section 13).** For `Γ ≠ 0` the multiplier ring
    of the ideal is `𝒜_𝕜(Γ)` and its units with `0` are `𝕜` (Theorem 13.2);
    from the pure ring `Oz` one interprets `No` and defines `R`, the order,
    the finite ring, the infinitesimals and standard part (Theorem 13.4); the
    value group is interpretable (Corollary 13.5); automorphisms of `Oz` fix
    `R` pointwise (Theorem 13.6) although `Aut(Oz)` is nontrivial (Example
    13.7); every automorphism of `C` extends to `Oz[i]` (Proposition 13.8), a
    phase twist preserving `Oz[i]` (Lemma 13.9) shows that `No`, conjugation
    and `Oz` are not definable from `Oz[i]` (Theorem 13.10); Diophantine
    subsets of `Z^n` in `Oz` are exactly the c.e. ones (Theorem 13.11); `Z` and
    `N` are definable and `Th(A)` is undecidable and not recursively
    axiomatizable for set-sized intermediate rings (Corollary 13.12); no
    positive-existential set contains a nonzero element of `Π` and excludes
    `0` (Theorem 13.13); no quantifier elimination (Proposition 13.14); an
    omitted computable type (Theorem 13.15).
13. **Families and primitivity (Section 14).** Polynomial lifting (Proposition
    14.1); homogeneous cone criterion and its decidability (Theorem 14.2);
    unimodular Pythagorean triples (Proposition 14.4); a real direction has a
    primitive omnific representative iff it is rational (Theorem 14.5);
    every primitive representative of a real direction is an ordinary coprime
    integer tuple. Finite-support solutions specialize to polynomial arcs
    over real coefficients (Theorem 14.7, extending source 05’s integer
    case); supplied finite-support Bézout witnesses specialize with them.
14. **Fractions and denominator ideals (Section 15).** `𝔇(x)` is a nonzero
    ideal with the covariance `𝔇((ax+b)/(cx+d)) = (cx+d)𝔇(x)` under `GL_2(Oz)`
    (Proposition 15.2), principal exactly when it has a least positive member
    (Proposition 15.3). `Oz[(Z∖0)⁻¹] = Q ⊕ Π`, with `𝔇(y + m/n) = nOz`
    (Proposition 15.5); no set of denominators serves all surreals
    (Proposition 15.6). For real `r`, `𝔇(r)` is `qOz` or `Π`, and five
    properties characterize `r ∈ Q` (Theorem 15.7); the pair `(t, rt)` has no
    gcd in every fixed workspace `Oz_Γ` (Remark 15.8). *Multiplier theorem*:
    for a tuple unimodular over a domain `R` with a retraction `c : R → R`,
    every ambient scalar making it `c⁻¹(Z)`-valued lies in `R`; the scalars form
    `c⁻¹(Z)` (rational constant direction, after normalization, and the tuple
    is then unimodular over `c⁻¹(Z)`) or `ker c` (irrational)
    (Theorem 15.11). On the region `𝒱 ⊆ P¹(No)` of points with a
    `B_R`-unimodular presentation, `𝔇(x)` is `λQ·Oz` with a unique primitive,
    unimodular presentation, or `QΠ` with no gcd, no set of generators and no
    least denominator, according as `sp(x) ∈ P¹(Q)`, and `𝒰 = sp⁻¹(P¹(Q))`
    (Theorem 15.15). For coprime real polynomials and `0 ≠ t ∈ Π`, all
    representations of `(p_j(t)/q(t))_j` are `h(p(t), q(t))` with `h ∈ Oz` or
    `h ∈ Π` according to `[p(0):q(0)]`, for arbitrary supports
    (Theorem 15.18); lowest terms are all or nothing (Corollary 15.19); the
    leading-exponent spectrum (Corollary 15.20); `f(t)` has lowest terms iff
    `f(0) ∈ Q ∪ {∞}` (Corollary 15.21); a table of eleven examples
    (Example 15.23); `r + 1/t` and `r + 1/(t+1)` have opposite types
    (Example 15.24); local density at infinity (Proposition 15.26). Two reduced
    fractions without an lcm (Example 15.27); primitive coordinates on rational
    curves iff `φ(0) ∈ Pⁿ(Q)` (Corollary 15.28) and unimodular solutions of
    homogeneous systems along such curves (Corollary 15.30). The fibers of `sp`
    are the orbits of `K = ker(SL_2(Oz) → SL_2(Z))` (Theorem 15.32);
    `𝒰 = SL_2(Oz)·∞` (Corollary 15.33); one matrix of `K` sends any set of
    points into any interval (Theorem 15.35), so every `K`-orbit is dense
    (Corollary 15.36), both denominator types occur in every interval
    (Corollary 15.37) and `sp` is continuous nowhere (Corollary 15.38); the
    density needs matrices outside `E_2(Oz)` (Remark 15.39). `Oz_Π` is local
    with residue field `Q` (Proposition 15.40), its rational-function part is
    described (Proposition 15.41), and on finite elements `(st, res)` maps onto
    `R × Q` (Theorem 15.42). `Oz ∩ R(t) = Z + tR[t]` (Proposition 15.43), whose
    ideal `tR[t]` needs `𝔠` generators (Proposition 15.44); extension to `Oz`
    loses denominators (Theorem 15.45); under `T = U^m` the irrational defect is
    `UR[U]/U^mR[U]`, of real dimension `m − 1` (Theorem 15.46), the extension is
    integral but neither finite nor flat (Theorem 15.47), and `Tor_1` realizes
    the same defect (Proposition 15.48). Monomial denominators (Proposition
    15.50, Examples 15.51, 15.52). The Gaussian dichotomy (Theorem 15.54) and
    the constant-direction criterion over `Z` and `Z[i]` (Corollary 15.55,
    sources 08 and 14).
15. **Omnific coefficients (Section 16).** The square-discriminant criterion
    (Theorem 16.1), initial forms (Proposition 16.3), two-term roots
    (Proposition 16.4, also proved by finite factorization) and simple residue
    roots that do not lift (Example 16.5). Nonmonic quadratics need an extra
    divisibility condition; the omnific lifting failure concerns a different
    ring from finite-surreal standard-part lifting. The sibling report's fresh-scale image-gap theorem contains
    `x² = ω² + 1` (Example 16.2) and the two-term equations as special cases.

**Questions (Section 18).** Two source questions are recorded as settled by
source 05 (Section 18.1): source 01's `Y² = X³ + 1` and coprime exponents, and
the unimodular half of the Fermat questions of sources 01 and 02. Section 18.2
records that source 06 answers the first part of Question 18.4 (an
existential definition of `Π`) and source 07's closing question on
positive-existential definitions of `Π` and of the graph of `ct`, and that the
report's quartics answer source 06's degree question in part. Section 18.3
records that source 08's rational-curve criterion answers Question 18.3 in part
(Corollary 15.30); points off rational curves and the dependence on the
integral model remain open. Still open: affine varieties and curves, including
`Y² = X³ + aX + b` with `a ≠ 0` (Question 18.1; the omnific groups report
answers it for closed subgroup schemes of `GL_N`); primitive, non-unimodular
Fermat triples (Question 18.2); primitive homogeneous solutions, re-scoped
(Question 18.3); which fibers or subideals of `Π` are Diophantine (the second
part of Question 18.4); the guard's complexity, the least degree of a
definition of `Z`, a single Gaussian polynomial and better quantifier bounds
(Question 18.5); roots with omnific coefficients (Question 18.6); the size
boundary (Question 18.7); finite-support search (Question 18.8); coefficient
recovery of lower quantifier complexity (Question 18.9); structure that
determines the real form of `Oz[i]` (Question 18.10); infinite algebraic
extensions (Question 18.11); and, from sources 08 and 09, denominator ideals
beyond one parameter (Question 18.12), the extent of `𝒱` (Question 18.13),
orbits outside `𝒱` (Question 18.14), several parameters (Question 18.15) and
other scale extensions (Question 18.16). No source claims that these are open
in the literature.

## Corrections made in the merge

- Source 02 stated Pell rigidity for `D > 0`, and source 13 for positive
  nonsquare `d`; their proofs need only `D ≠ 0`.
- Source 01's abstract said "nondegenerate binary forms"; its theorem needs
  only two distinct projective linear factors (weaker in degree ≥ 3, e.g.
  `X²Y`).
- Matiyasevich, *Soviet Math. Dokl.* 11 (1970): sources 02 and 06 gave pages
  354–358, source 05 354–357. The report uses 354–357, the range given with
  MR 258744 in Bhatt and Poonen's notes *Diophantine sets* and in the title of
  the *Journal of Symbolic Logic* review.
- Source 05's set-sized quotient proof uses global choice where the Hartogs
  ordinal suffices (Remark 3.7).
- Source 01's isotropic-vector lemma assumed `q(a) ≠ 0` where `a ≠ 0` suffices
  (Lemma 8.3).
- Source 02 credits MathOverflow comments by Jeřábek (2018) and Chow (2021)
  for the observation that nonzero Fermat solutions exist in `Oz`. The site
  could not be reached; the attribution is printed as source 02's and marked
  unverified (after Example 14.3).
- Source 06's principal real formula, a quintic with seven witnesses, is
  dominated by the report's quartics (five and six witnesses); it is printed
  as Remark 11.10 with that comparison. Its degree-ten polynomial for the
  graph of `ct` is improved to degree four (Corollary 12.9).
- Source 07's universal definition of `Π` and its prenex definitions of the
  graph of `ct` are superseded as definitions by source 06's existential ones
  and kept as second routes.
- Sources 06 and 07 credit the intersective polynomial to Lê–Spencer (07 also
  to Berend–Bilu); Lê and Spencer attribute it to Borevich–Shafarevich, *Number
  Theory*, p. 3, which is added.
- Source 06's `∃y (x² = 2y²)` fails for number-field coefficient rings with
  `√2` in their fraction field; Remark 12.15 uses another radicand.
  Under the detector hypotheses one can use `p`, `q` or `pq`, according
  to which factor vanishes at the chosen root.
- The initial assembly reported no mathematical error in the main proofs
  of the five sources; the proof review and source reconciliation remain
  incomplete, as recorded above.
- The later Sections 5–7 review corrected the merge's own divisibility
  identity (Remark 7.5): it requires the derivation to kill `a` and `b`, and
  its use at level `c` also requires `∂c = 0`. The Euler derivations satisfy
  these hypotheses. The review also extends one-variable and separated-power
  rigidity to complex coefficients (Proposition 2.8, Theorem 7.4), explains
  the support-ring witnesses in Fermat rigidity, and distinguishes these local
  Euler derivations from the normalized surreal derivation.
- The Sections 8–9 review makes polarization and the isotropic complement
  explicit, proves preservation of coordinate ideals along the quadratic
  orbits, and fills in transfer of quantified formulas from `No` to a
  set-sized real closed field. It includes empty definite levels and shows
  why symmetry and the chosen polynomial generators matter in the two
  matrix/leading-form criteria. The exact review boundary is in the
  reconciliation record.
- The Section 10 review expands the finite bounds and divisibility test,
  specifies the induction domain, and gives nonnegative witnesses for the
  order-free arithmetic formula. The open-induction argument explicitly
  transfers quantifier-free truth to a set-sized Hahn workspace.
- The Section 11 review (now Section 14) strengthens the description of
  primitive real directions, expands the finite ordered specialization
  argument, and extends the arc theorem to real coefficients. Finite-support
  Bézout witnesses and the positive-parameter sign condition are explicit.
- No mathematical error was found in sources 08 and 09. Source 09 says "finite
  x" for `x ≠ ∞`; these points are called affine here. Its local density
  proposition ends "unless `g = f` exactly", which is unnecessary (Proposition
  15.26). Its introduction's "unique positive least denominator" is simply the
  least positive denominator. Source 08's `A = c⁻¹(Z)` and `𝒜 = Oz_Π` share a
  letter, and the two sources order projective coordinates oppositely; both are
  fixed (Section 15.1). Source 09's `lem:transvection` would collide with this
  report's Lemma 8.2 and is Lemma 15.34.
- Credits added: source 08's conic is Proposition 14.4 with source 01's
  witness; its no-lcm example is, for monomial `t`, the sibling report's
  `osq:tn:thm:syzygy`(iii); its real-constant ideal is, for irrational `r`,
  `osq:tn:thm:duals`; source 09's `M⁻¹Oz = No` is `osq:prop:fractions`(iii);
  and source 08's Gaussian theorem contains manuscript 14's direction
  criterion. The sibling report's results postdate the pin of sources 08
  and 09.
- The review of the omnific-coefficients section (numbered 15 in that pass,
  now Section 16) gives a finite-algebra proof of the two-term root
  obstruction, expands the support justification of its binomial series,
  and distinguishes the omnific constant-term map from finite-surreal
  residue lifting. The monic hypothesis and leading-term cancellation
  requirement have explicit counterexamples.

- The new Section 11 review expands leading-degree and Pell-divisibility
  proofs, separates arbitrary intermediate rings from full support rings,
  and makes the witness and congruence steps in the integer definitions
  explicit. The shared notation guide now records the different meanings
  of the two reports' `𝒜` notation.
- The new Section 12 review checks witness membership even with zero
  divisors, distinguishes coefficient parameters from integer numerals,
  adds a detector counterexample in `Z[ω]`, proves the additive splitting
  explicitly, and derives the existential number-field ideal and graph
  from the existing detector hypothesis. Standard statements are unchanged.
- The Section 13 review expands fraction interpretation, coefficient
  reconstruction, value-group ordering, automorphism invariance and the
  computable omitted type. It makes the nontrivial-exponent hypothesis
  explicit, specifies strict positivity in the collapse obstruction, and
  derives the c.e.-set classification without ordering or a square root
  of two, using the order-free integer guard.

**Stale repository statements.** Source 01 said the repository's
trigonometry material used the omnific integer part; at the pin the
foundations report already defined `Oz = Π ⊕ Z` (`found:eq:omnific`).
Sources 01, 02 and 05 correctly found no omnific report and no omnific Lean
at their pin. Sources 06 and 07 say that the explicit Diophantine definitions
of `Z` they give were not found in the repository, and source 13 says the same
of its exact fiber formulation; at their pin `71e9606` this was true, but the
collection has contained the quartic guards (Theorems 10.3, 10.4) and the exact
fiber theorem (Theorem 6.2) since `be06fc8`. The collection now has this
report and its sibling, and still no Lean. Descriptions of
`docs/NORMAL_FORM_BRIDGE.md`, the `Surreal/Foundations/` workspace modules,
the surcomplex automorphism report's phase twists, the catalogue entry on
coefficient recovery by a dilation, and the formalization ledger remain
accurate. Sources 08 and 09 cite the rational-direction criterion as
"Theorem 11.5", its number at their pin `9a385d3`; it is now Theorem 14.5 (and
09's "§§4, 11" are now Sections 4 and 14). Source 09 describes this report as
built from manuscripts of 22 September, true at its pin; it now has seven
sources of 22 and 23 September. Source 08 gives the sibling report its old
title, *The Universal Set-Sized Quotient of the Omnific Integers*; it is now
*Set-Sized Quotients of the Omnific Integers*. Their other citations of this
report (Theorems 4.2, 4.6, 4.10, Corollary 4.3, the floor of Section 2) are
accurate, and 09's statement that its omnific results are pending in Lean
still holds. The sibling report's statement that manuscript 14's Gaussian
direction criterion is printed here was not true before this integration; it
is now (Corollary 15.55).

## What the report does not claim

No non-claim of any source was dropped. Appendix B lists them per source (01:
24 items, 02: 22, 05: 26, 06: 25, 07: 19, 08: 25, 09: 20, 7 for the results
printed from source 13 and 2 for the criterion printed from source 14, plus
the caveats common to 01, 02 and 05, to 06 and 07, and to 08 and 09). The
main ones:

- **Status.** AI-assisted; not refereed; nothing formalized in Lean; the finite
  scripts check identities and examples, not theorems. The repository was
  inspected through the GitHub connector at the pins, not checked out or built.
- **Priority.** None is claimed. Source 01 names the quadratic classification
  and the guard, source 02 the exact decomposable fibers and uniform quadratic
  lifting, source 05 the separated-power, unimodular Fermat and set-sized
  quotient proofs, source 06 the explicit Diophantine formulas and the
  reconstruction package, source 07 the formula package and the
  constant-term detector, source 08 the rational-function classification and
  the denominator-defect package, and source 09 the multiplier and dichotomy
  theorems, the one-scale classification and the orbit and focusing theorems
  as their most distinctive contributions. None is certified new. First-order definability of `Z` in `Oz` and its nonsaturation
  go back to a 2018 MathOverflow comment by *nombre*, which source 06 credits;
  the ideal equation belongs to the same obstruction.
- **Rigidity is not finiteness.** No Thue or Baker finiteness, no bounds and no
  algorithm for the ordinary integer solutions; a finite search does not
  certify a complete solution list.
- **Transfer is about existence.** It says nothing about fiber sizes;
  nonvanishing and order do not transfer; omnific coefficients are not
  covered by the Hilbert's-tenth-problem statement.
- **Quadratic levels.** Only the presence of infinite points on represented
  nonzero levels is classified; not every point lies on the constructed
  orbits; source 02's version excludes degenerate forms and the zero level.
- **Definability.** No degree or witness count is claimed optimal (the
  quantifier-free obstruction is only a first lower bound); no single
  polynomial defines `Z[i]` in `Oz[i]` here; the certificate `vs = Λ(t)` is not
  a definition of nonzeroness; the detector needs a root of `Λ` in the
  coefficient field and is not asserted for all intermediate rings; the
  number-field theorem is not uniform in the field and not for infinite
  algebraic extensions; the first-order definitions of Corollary 10.7 are
  kept, and the multiplier and coefficient-field formulas are first order, not
  positive existential.
- **Reconstruction.** The value group is an interpreted quotient, not a
  monomial section; no definability of the `ω`-map, birthdays or the
  exponential; pointwise fixation of `R` is for automorphisms only; `Γ ≠ 0` is
  needed and the fraction field of a fixed Hahn ring need not be the whole
  Hahn field; recovering `C` from `Oz[i]` does not recover the real form.
- **Logic.** Undecidability and non-axiomatizability are consequences of
  established results (MRDP, Jeřábek 2011), not new theorems about `Q` or
  number fields; class statements are read formula by formula.
- **Fermat.** Scaling solutions are not primitive; Theorem 7.9 says nothing
  about triples that merely lack a common nonunit divisor.
- **Elliptic curves.** `y² = x³ + ax + b` with `a ≠ 0` is outside the method.
- **Full class versus workspace.** Common divisors, clearing, `Frac(Oz) = No`,
  the reconstruction of `No`, non-generation of `Π`, the general no-gcd pair
  and the set-sized quotient theorem are not asserted for fixed Hahn
  workspaces; the quotient theorem does not apply to class-sized targets.
- **Refinement.** The 18 September 2026 announcement of a Lean proof of
  Conway's refinement conjecture is recorded, not audited and not used; no
  result assumes refinement, GCD or UFD properties.
- **Fractions.** `Frac(Oz) = No` is classical (Conway; L'Innocente–Mantova,
  Proposition 2.4.5), and Hamkins's observations on lowest terms are not new;
  the pullback and matrix-completion methods are ordinary algebra (LM Lemma
  9.2.1 and Klawa as precedents); integrality and nonflatness of such
  extensions are classical (Stacks 00HK). Sources 08 and 09 name their
  candidate contributions without certifying priority; their searches were
  targeted or keyword-based. The classification covers tuples in `R(t)` and
  `C(t)`, and the region `𝒱`; it does not classify `𝔇(x)` for all `x`, and
  neither source claims `𝒱 = P¹(No)`. `t` must be purely infinite and
  nonzero; one parameter only (a multivariate gcd of one gives no Bézout
  identity). Primitive and unimodular coincide only for the classified
  representations. `sp` is not a field homomorphism, and `f(0)` is a formal
  substitution: no homomorphism `No → R` sets `ω = 0`. `res` and `st` have
  different domains; neither is a retraction of `No`. The dense fibers are
  not open and not separated, and focusing fails for proper classes. The
  scale defect is a real dimension, not a length, and there is no general
  flatness or normalization theorem for Hahn integer parts. The certificate
  procedure needs exact coefficients. The primitive-fraction class is not a
  subring. Manuscript 14's criterion concerns coordinate representatives, not
  all points of a projective scheme over a ring.
- **Formalization.** The proposed Lean modules (Section 17.2) are proposals.
  At the repository's Mathlib pin (`81a5d257`) `Nat.sum_four_squares` exists and
  no three-square theorem does, so only the four-square definitions of `Z`
  rest on a theorem in Mathlib.

## Relation to neighbouring reports

- [`foundations`](../../foundations-and-computation/foundations/) defines
  `Oz = Π ⊕ Z` (`found:eq:omnific`, subsection `found:sub:omnific`); this report
  develops its arithmetic with the same letter `Π`.
- [`trigonometry`](../../surcomplex/trigonometry/) uses the opposite
  (`t`-exponent) sign for `Π` (`trigonometry:eq:split`); its integer-part
  construction agrees with Theorem 2.7, and `2πOz = Π + 2πZ`
  (`trigonometry:eq:periodclass`) rests on the same fact as Theorem 3.1.
- [`gamma-and-zeta-functions`](../../surcomplex/gamma-and-zeta-functions/):
  the parity statements of `gz:cor:canonical-zeros` are instances of Theorem
  3.1.
- [`transcendence-over-bounded-support`](../transcendence-over-bounded-support/):
  its GCD hypothesis (`bst:hyp:gcd`) is about a different ring, whose units are
  the monomials; Theorem 4.10 concerns `Oz`, whose units are `±1`. No conflict.
- [`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/)
  prints source 05's universal set-sized quotient theorem with its proof; its
  preliminaries overlap Sections 2–4 here. Its manuscript 13 supplies the
  Gaussian fiber and étale norm results printed here once (Section 6), and
  its manuscript 16 (files `16-fresh-scale-`) proves the fresh-scale image-gap
  theorem generalizing Example 16.2 and Proposition 16.4. Its manuscript 14
  (files `14-arithmetic-tensors-`) proves the direction criterion printed here
  as Corollary 15.55; its `osq:tn:thm:duals`, `osq:tn:thm:syzygy`(iii) and
  `osq:tn:thm:hom` contain the rank-two case of Theorem 15.7, the intersection
  of Example 15.27 for monomial `t`, and the scalar step of Theorem 15.11;
  `osq:prop:fractions`(iii) gives `M⁻¹Oz = No`, and `osq:cor:smallprimes` agrees
  with the residue field `Q` of `Oz_Π` (Proposition 15.40).
- [`omnific-groups-and-lattices`](../omnific-groups-and-lattices/): its
  cusp-residue obstruction and non-elementary unipotents
  (`ogl:el:prop:cuspresidue`, `ogl:el:thm:nonel`) show that the focusing
  matrices of Lemma 15.34 lie outside `E_2(Oz)` at irrational centres and that
  the density of Corollary 15.36 needs such matrices (Remark 15.39). It also
  answers Question 18.1 for closed subgroup schemes of `GL_N`.
- [`surcomplex-field-automorphisms`](../../surcomplex/surcomplex-field-automorphisms/)
  constructs the phase twists and the dilations `S_a`; source 06 credits it and
  proves that the twist of Lemma 13.9 preserves `Oz[i]`.
- [`single-dilation-hahn-support`](../../surcomplex/single-dilation-hahn-support/)
  defines the coefficient field and constant coefficient of a Hahn field from
  one dilation; Theorems 13.2 and 13.4 recover them from the pure ring `Oz`.
- [`euclidean-three-space`](../euclidean-three-space/):
  `e3:cut:thm:smallquotient` is the analogous size phenomenon for `SO(3, No)`;
  by Corollary 9.4, `SO(3, Oz)` is finite.

## Build and reproduce

The report uses standard TeX Live or MiKTeX packages (`lmodern`, AMS
packages, `mathtools`, `aliascnt`, `booktabs`, `longtable`, `enumitem`,
`xcolor`, `fancyhdr`, `xurl`, `hyperref`, `cleveref`). No bibliography
processor is needed:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 118 pages with no errors, warnings, undefined references,
multiply defined labels or overfull boxes. (The text at `a4dcb91`, before
Section 15, built to 87 pages with the same MiKTeX installation; the PDF
committed then had 86 pages.) Source 08's `code/08-fractions-Makefile` and
source 09's `code/09-fraction-fibres-build.sh` and `.ps1` compile the delivered
`omnific_fractions.tex`, which is not shipped; they do not build this report.
Source 08's shipped source audit describes its own article and files
(`verify.py`, `verification.json`), which are shipped here as
`code/08-fractions-verify.py` and `data/08-fractions-verification.json`. Source 01's `code/01-diophantine-geometry-build.sh` and `.ps1`
compile source 01's delivered file name (`omnific_integers.tex`), which is not
shipped; they do not build this report. Source 06's
`code/06-definability-reconstruction-Makefile` and source 07's
`code/07-defining-arithmetic-build.sh` refer to their delivered layouts
(`article.tex`, `code/verify.py` beside the Makefile, and the script's own
directory); they do not build this report either. Source 05's build note names
its delivered file names (`article.tex`, `verify_examples.py`,
`requirements.txt`); here they are this report's `article.tex`,
`code/05-diophantine-rigidity-verify_examples.py` and
`data/05-diophantine-rigidity-requirements.txt`. Source 06's shipped source
audit likewise describes source 06's own article.

The checks of sources 01, 02, 05, 06, 08 and 09 need Python 3.9 or later
(3.10 for sources 06 and 08) and SymPy (tested with 1.14.0); source 07's needs
Python 3.10 or later and the standard library only. From this directory:

```text
python -m pip install -r data/01-diophantine-geometry-requirements.txt
python code/01-diophantine-geometry-verification.py --output <scratch>/verification_report.json
python code/02-diophantine-verify_examples.py
python code/05-diophantine-rigidity-verify_examples.py
python code/05-diophantine-rigidity-verify_examples.py --standard-radius 200
python code/06-definability-reconstruction-verify.py --output <scratch>/verification-rerun.json
python code/07-defining-arithmetic-verify.py
python code/08-fractions-verify.py --output <scratch>/08-verification.json
cp code/09-fraction-fibres-verify_examples.py <scratch>/verify_examples.py
python <scratch>/verify_examples.py
```

Source 01's script **writes** a JSON report, by default
`verification_report.json` in the working directory; pass `--output` with a
path outside this directory (as above) or run it on a copy, so that the shipped
`data/01-diophantine-geometry-verification_report.json` stays the delivered
record. Source 06's script writes only to the path given with `--output`
(without it, it prints the report), so it never overwrites
`data/06-definability-reconstruction-verification.json`. The scripts of
sources 02, 05 and 07 print to the terminal only. Source 07's script uses
assertions: do not run it with `python -O`. Source 08's script **writes**
`verification.json` next to itself (that is, into `code/`) unless `--output`
is given; pass a path outside this directory, as above. Source 09's script
**always** writes `verification_report.json` next to itself, so run a copy, as
above, to keep `code/` unchanged; the shipped record is
`data/09-fraction-fibres-verification_report.json`.

When this report was assembled all five passed with Python 3.14.4 and SymPy
1.14.0: source 01's checks cover scalar identities, 20 quadratic-isometry cases
(dimensions 3–7), 31 Pell pairs and 256 guard witnesses; source 02's 13
identity checks and 49 finite-support products; source 05's nine groups,
including quartic certificates for `|t| ≤ 40` (and `≤ 200` with the option);
source 06's degrees, witnesses, six Gaussian examples, Pell orders for moduli
up to 500 and roots of `Λ` modulo every integer up to 2000; source 07's 13
groups, including roots of `Λ` modulo every integer up to 4096 and quartic
witnesses for `|x| ≤ 100`. The outputs of sources 01, 02 and 06 differ from the
shipped records only in the recorded Python version (3.13.5 there); the
outputs of sources 05 and 07 are identical to their records. When Section 15
was written, the scripts of sources 08 and 09 passed on copies with the same
versions. Source 08's 833 assertions in 13 categories (40 random polynomial
vectors, Bézout identities and lifted certificates, the classification over
`Q(√2)`, scalar memberships, the examples, the substitution `T = U^m` and its
defect layers, the nonflat relation, integrality equations, residue identities
and falling-factorial independence) gave a report with the same content as
the shipped record, which has no timestamp. Source 09's 92 assertions (the
matrices `F_{x,b}`, the covariance, Bézout certificates, nine one-scale
examples, local density and five focusing samples) gave a report that differs
from its record only in the generation time and Python version. The
certificates and table of the merge's Section 15 additions were checked
separately with SymPy.
