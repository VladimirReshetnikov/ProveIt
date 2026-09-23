# Set-Sized Quotients of the Omnific Integers

**The universal constant-term quotient, exact cardinal thresholds, support
thresholds, and what survives in large quotients**
Merged research report, 23 September 2026, from thirteen manuscripts: eight of
22 September 2026 (batch 24, placed in `be06fc8`): 06 (the base), 03, 04, 07,
08, 09, 10 and 11; and five of 23 September 2026 (batch 25, placed in
`cf350b1`), numbered here 12 to 16 by their file prefixes. Manuscript 05 of
batch 24 proves the unital universal theorem too; it is merged into the sibling
report [`omnific-diophantine-geometry`](../omnific-diophantine-geometry/) and
credited here.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 117 pages
README.md     this guide
03-cardinality-normalization-SOURCE_NOTES.md   source 03: repository pin, companion draft, literature
04-universal-residue-SOURCE_AUDIT.md           source 04: repository pin, prior manuscript, novelty, checks
06-universal-quotient-source_audit.md          source 06: repository scope, inputs, proof checkpoints
07-quotient-rigidity-SOURCE_AUDIT.md           source 07: repository inspection, precedents, novelty
08-small-rings-BUILD_REPORT.md                 source 08: build and finite-check record
08-small-rings-SOURCE_AUDIT.md                 source 08: repository pin, literature, novelty
09-set-shadows-SOURCE_AUDIT.md                 source 09: repository pin, literature, novelty
11-set-sized-algebra-SOURCE_AUDIT.md           source 11: repository pin, MathOverflow question, novelty
15-set-sized-representations-SOURCE_AUDIT.md   source 15: repository pin, literature, novelty, checks
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
  12-homological-dimension-check_boolean_tor.py       source 12 checks (780 multidegrees; needs SymPy; always writes, see below)
  12-homological-dimension-build.sh                   source 12's build script (original file names)
  13-small-target-rigidity-verify.py                  source 13 checks (6 groups; stdout)
  14-arithmetic-tensors-verify.py                     source 14 checks (2,189; needs SymPy; writes by default)
  14-arithmetic-tensors-build.py                      source 14's build script (original file names)
  15-set-sized-representations-verify_identities.py   source 15 checks (820; writes, see below)
  16-fresh-scale-verify_finite.py                     source 16 checks (1,354; needs SymPy; writes by default)
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
  12-homological-dimension-audit_results.json             recorded run of the source 12 checks
  13-small-target-rigidity-verification.txt               recorded run of the source 13 checks
  13-small-target-rigidity-source_manifest.json           source 13's record of inspected repository paths and sources
  14-arithmetic-tensors-verification.json                 recorded run of the source 14 checks
  14-arithmetic-tensors-requirements.txt                  sympy==1.14.0
  14-arithmetic-tensors-provenance.json                   source 14's provenance and verification-scope record
  15-set-sized-representations-finite_checks.json         recorded run of the source 15 checks
  16-fresh-scale-verification_results.txt                 recorded run of the source 16 checks
  16-fresh-scale-requirements.txt                         sympy==1.14.0
```

Every label in `article.tex` carries the prefix `osq:`. The large-quotient part
(Section 14) uses the sub-prefix `osq:if:`, the integral-closure part
(Section 15) `osq:nm:`, and the polynomial-map part (Section 16) `osq:pm:`.
The five later manuscripts use `osq:hd:` (12) and `osq:tn:` (14) in the new
Section 13, `osq:fs:` (16) in Sections 16.6 and 16.7, `osq:rep:` (15) for its
two printed additions and `osq:str:` (13) for the remark crediting its answer to
Elliott's question. The report has 409 labels (334 before the second merge;
none was renamed or removed). The audit files and programs keep the source
numbers `03` to `16`, and the audit files keep their sources' own notation and
theorem numbering. No source manuscript is shipped.

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

## Thirteen sources, one report

The eight manuscripts of batch 24 answer the same question, *what can a
set-sized ring or module see of an omnific integer?*, with the same answer:
exactly the ordinary integer constant term. They then diverge. The report
prints the common spine once (Sections 2–7) and keeps every result of every
source. Two batch-25 manuscripts (13, 15) reprove that answer independently;
two (12, 14) add the ordinary homological and tensor algebra of subrings of
`Oz`; one (16) adds fresh-scale arguments for polynomial and rational maps.

| | Manuscript (pages) | Pin | Contributes |
|---|---|---|---|
| **06** | *The Universal Set-Sized Quotient of the Omnific Integers* (25) | `a5c2a97` | **The base.** The coefficient-ring theorem over any set field with the scaled-field collision lemma (Lemma 4.1) and the direct module argument; the model `A^06_κ` (Section 11.2); the homological package (Section 12); matrix representations (Proposition 5.7); polynomial tests (Theorem 6.14); the prime-reservoir proposition (Proposition 14.12). Files `06-universal-quotient-*`. |
| **03** | *Cardinal Visibility and Normalization of Omnific Integers* (25) | `cd80e5e` | The smaller-scale field bound (in Proposition 10.3); the model `A^03_κ` with threshold `κ^ℵ0` (Section 11.1); integral and complete integral closure, set-generated algebras, surcomplex analogues, set-valued valuations (Section 15). Files `03-cardinality-normalization-*`. |
| **04** | *What Set-Sized Algebra Can See of Surreal Arithmetic* (24) | `cd80e5e` | The theorem for `D + Π_k` by separation and the explicit telescope; standard part on the finite side (Section 8); the support threshold with its negative side (Theorem 9.1); fixed-group bounds; localizations, algebras, derivations. Files `04-universal-residue-*`. |
| **07** | *Small Quotients and Large Internal Fields of the Omnific Integers* (27) | `37eefca` | The theorem over any set field by weighted certificates; completions; the embedding `No ↪ F_a`, field transfer, the exact binomial kernel and the Cantor algebra in `Oz/(1+ω^a)` (Section 14). Files `07-quotient-rigidity-*`. |
| **08** | *What Small Rings Can See of Omnific Integers* (26) | `37eefca` | The choice-free Hartogs formulation and nonunital maps; the finite-congruence closure; the invisible equation `X^m = ω^γ + 1`; class-indexed derivations; the quantitative criterion; the model `A^08_κ` for every infinite `κ` (Section 11.3). Files `08-small-rings-*`. |
| **09** | *Set-Sized Shadows of Omnific Integers* (20) | `37eefca` | Direct division of arbitrary elements; the model `A^09_λ` with residue fields, `≥ λ` non-arithmetic maximal ideals and `ℵ1` generators (Section 11.4); Gaussian ramification. Files `09-set-shadows-*`. |
| **10** | *Set-Sized Shadows of Omnific Arithmetic* (26) | `a5c2a97` | The theorem over any set field including maps on `Π_K`; the quantitative bound; endomorphisms; numerical polynomials, all-modulus congruences, `p`-adic completion and characters, lattice rigidity (Sections 16.1–16.5). Files `10-omnific-arithmetic-*`. |
| **11** | *What Set-Sized Algebra Can See of the Omnific Integers* (20) | `37eefca` | Pairwise-difference families; the localization and presentation calculus; the extension criterion (Theorem 9.1(iii)); the coinitiality theorem; residual targets; the ordinal ring and MathOverflow 188430 (Section 17). Files `11-set-sized-algebra-*`. |
| **12** | *Arithmetic Invisibility and Homological Dimension in Omnific Integer Cores* (21) | none stated | Coordinate-cone cores `A_d ⊂ Oz`: the Boolean flat resolution (Theorem 13.4), the multigraded `Tor` (Theorem 13.7), `fd D = d` (Corollary 13.8); the noncoherence certificate (Theorem 13.9(iii)); the ordered-cone collapse (Theorems 13.13, 13.14); projective bounds and the telescope (Proposition 13.12). Files `12-homological-dimension-*`. |
| **13** | *Small-Target Rigidity and Arithmetic Specialization* (21) | `71e9606` | An independent proof of the universal theorem (credited at Theorem 5.1) and of the answer to Elliott's addendum (Remark 17.2). Its fiber and norm theorems are printed in the sibling report. Files `13-small-target-rigidity-*`. |
| **14** | *Arithmetic Tensors in the Omnific Integers* (19) | `71e9606` | Coefficient-lattice modules `L(M) = M + Π`: syzygy (Theorem 13.9), nonflatness (Proposition 13.10), tensor normal form (Theorem 13.18), exterior and symmetric powers (Theorem 13.20), Rees equations (Theorems 13.21, 13.22, Corollary 13.23), Hom and isomorphism types (Theorem 13.24), ideal classes (Theorem 13.25), duals (Theorem 13.27), matrix kernels (Theorem 13.28), `fd` over `A_0` (Theorem 13.11). Files `14-arithmetic-tensors-*`. |
| **15** | *Omnific Integers Have Only Ordinary Set-Sized Representations* (21) | `71e9606` | An independent proof of the universal theorem and its consequences (credited throughout Sections 3–9); two one-line additions (Corollary 5.5, Proposition 7.3). Files `15-set-sized-representations-*`. |
| **16** | *Fresh-Scale Image Gaps and Rational Rigidity for Omnific Integers* (23) | `71e9606` | The image gap with forbidden layers (Theorems 16.35, 16.36), fresh fibers (Theorem 16.40), rational collapse and surjective self-maps over any constant ring (Theorems 16.42, 16.43), optimal and Gaussian finite tests (Theorem 16.46, Proposition 16.47), rational probes and certificates (Theorem 16.49, Corollary 16.50), no set-sized sample (Theorem 16.51), co-small rigidity and hulls. Files `16-fresh-scale-*`. |

- **Base and routes.** 06's coefficient-ring theorem over any set field `K`
  (also proved by 07 and 10) is the most general statement; its scaled-field
  collision lemma, of which 03's field bound is a special case, gives the sharp
  cardinal bounds where counting monomials does not. The proof of Theorem 5.1
  is written in 08's choice-free Hartogs form, with 08's and 10's nonunital
  forms and 06's direct module argument. 04's and 05's explicit telescope,
  09's and 10's direct division, 11's pairwise-difference families and 07's
  weighted certificates are kept as second routes. 13 (any set field, direct
  division with the family `ε/(α+2)`) and 15 (`k ∈ {R, C}`, separating families
  with a Hartogs ordinal, which is 08's route) are credited as further proving
  sources; neither adds generality.
- **Printed once:** support gaps, common monomial divisors, clearing, fraction
  fields (Section 3); the telescope and its finite truncation (Lemma 4.3); set-sized
  quotients (Theorem 6.2), completions (Theorem 6.10), modules (Theorem 7.1),
  derivations (Theorem 7.4), the invisible prime `ω^√2 + ω + 1` (Corollary 6.8,
  primality imported from L'Innocente–Mantova, Theorem B); the support threshold
  (Theorem 9.1: 11's formulation with 04's negative side); the finite-support
  augmentation (03, 04, 09, 11, 15); the answer to Elliott's addendum (Theorem 17.1:
  11's two proofs, which are also 13's). From the second merge: 14's `A_0` is 12's
  `A_1` (Lemma 13.1(iii)); 12's two-generator syzygy is the case `r = 2` of 14's
  (Theorem 13.9, in the common generality of both); 10's and 16's rational collapse,
  affine self-maps, transfer and grids are printed once each, the general-`D`
  statement with 16's fresh-scale proof and 10's statements with their
  finite-difference and lattice proofs as a second route (Theorems 16.25, 16.42,
  Corollary 16.29, Theorem 16.43, Proposition 16.45, Theorem 16.46).
- **Printed in the sibling report, not here:** 13's exact fibers of products of
  linear forms and its étale norm and Pell theorems; 14's criterion for unimodular
  projective directions, which is the Gaussian and principal-ideal extension of
  that report's rationality theorem for primitive constant directions.
- **Renamed symbols** (Sections 2.4, 13, 16.6): the purely infinite ideal is the
  repository's `Π` (was `I`, `𝒥_k`, `𝔍`, `𝔓`, `J_k`, `𝓘_K`, `𝒫_k`); the constant
  term is `ct` (was `c_0`, `π`, `ε_D`, `ε`); 10's shadow map `Π` is `ct_*`; 06's
  `L_a` and 07's `𝓕_a` are `𝓕_a`; 07's localization `L_a` is `Oz[ω^{-a}]`, its
  `B_a` is `𝒬_a` and its compression `E_a` is `Ψ_a`; 03's normalizations `B, C` are
  `𝒩, 𝒩_C` and its `Int_F(A)` is `IC_F(A)` (`Int` is 10's integer-valued
  polynomials); 09's `Og` and `No(i)` are `Oz[i]` and `No[i]`; the set-sized
  constructions carry their source number (`A^03_κ`, `A^06_κ`, `A^08_κ`,
  `A^09_λ`, `R^11_{Γ,<κ}`). In Section 13: 12's tail `M` is `Π_Λ`, its ordered-cone
  ring `T` with monomials `t^γ` is `T_Γ` with monomials `X^γ` (here `t^g` means
  `X^{-g}`), its test modules `N_F` are `V_F`, its cyclic module `Q` is `A/H`; 14's
  `𝓘, B, A, F` are `Π_k, 𝒜_{k,k}, 𝒜_{D,k}, k((X^No))`, its `P, A_0, B_0` are
  `Π^fin_Q, T_Q, k + Π^fin_Q`, its `μ_{M,N}, K(M,N), E(M,N)` are
  `m_{M,N}, 𝒯(M,N), E(M,N)`, its multiplier ring `𝒪(M)` and orders `𝒪 ⊂ K` are
  `𝔬(M)` and `𝔬 ⊂ K_0` (`𝒪` is the finite surreal ring). In Section 16.6: 16's
  `ℐ_k, 𝒜_D` are `𝒜_{k,k}, 𝒜_{D,k}`, its defect `D_{ζ,c}` is `d_{ζ,c}` (`D` is the
  constant ring), its centre `μ` is `s`, its `L_ζ, A_ζ` are `a_ζ, c_ζ`.
- **Sign convention** (Section 2.2): large monomials, `ω^γ` infinite for
  `γ > 0`. The foundations report defines `Oz = Π ⊕ Z` (`found:eq:omnific`);
  the trigonometry report (`trigonometry:eq:split`) describes the same `Π` by
  negative `t`-exponents because it writes `t = ω^{-1}`.
- **Foundations.** NBG with choice for sets. 04, 06 and 09 (and 05) state
  global choice; no source uses it. 13 and 15 add a two-universe reading.

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
  primes `P ⊉ Π` (Remark 14.13), and explicit elements of `𝒩 \ Oz` from 08's
  equation (Remark 15.27).
- **From the second merge.** The syzygy, noncoherence and nonflatness theorems
  in the common generality of 12's rings and 14's (any unital `D ⊆ K`, any rank)
  (Theorem 13.9, Proposition 13.10); the flat dimensions `d` and `d+1` of lattice
  modules and cyclic quotients over every coordinate-cone core and `1`, `2` over
  every ordered-cone core (Theorem 13.11); the exact projective dimensions
  `pd D = 2` over `A_1` and every `T_Γ`, `pd L(M) = 2` and `pd A_0/J = 3`, and
  `pd D = 2` for every ring satisfying the hypotheses (H1)–(H3) of Section 12 whose
  tail is countably generated, which among the five constructions is exactly
  `A^08_κ` with `cf κ = ℵ0` (Proposition 13.12); and the comparison of the two
  kinds of flat-dimension statement (Remark 13.16).

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
  quotient has small reflection `D/ct(J)` (Theorem 6.1). A set of maps with
  specified nonzero kernel elements has a common nonzero monomial in all kernels,
  and `Hom(M, Oz) = 0` for every set-sized `Oz`-module `M` (15; Corollary 5.5,
  Proposition 7.3).
- **Theorem B (Theorems 8.2, 9.1).** Standard part is universal on `D + 𝔪_k`
  and on the finite surreal and surcomplex rings (04). Supports of size at most
  any infinite cardinal suffice for Theorem A; finite supports admit the
  augmentation `Σ c_g ω^g ↦ Σ c_g`, and a map on the finite-support ring extends
  to countable supports iff it factors through `ct` (the criterion is 11's; that
  the augmentation does not extend is 04's, 11's and 15's).
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
- **Theorem E (Section 14, from 07 and one proposition of 06).** Inverting a
  nonzero purely infinite element forces an explicit copy of `No`
  (Theorems 14.4, 14.7); `Oz/(1+ω^a)` has no nonzero set-sized image yet
  contains an algebraically closed field containing `No[i]`, exact cyclotomic
  algebras (Theorem 14.15) and the Cantor algebra `LC(Z_2, E_a)`
  (Theorem 14.19), so it is not a domain, not local and not Noetherian.
- **Theorem F (Section 15, from 03 and 08).** `Oz* = No`; the integral closure
  `𝒩` is proper, fine-dense, of zero conductor and not set-generated
  (Theorems 15.5, 15.12); constant slices, the complexification defect killed by
  `2` (Proposition 15.18), no finite quotients (Theorem 15.20), no nontrivial
  set-valued valuation of `No` containing `Oz` (Theorem 15.22); for `γ > 0` and
  `m ≥ 2`, `X^m = ω^γ + 1` has no root in `Oz[i]` but the root `1` in every
  set-sized image (Theorem 15.25).
- **Theorem G (Section 16, from 10 and 16).** `Num_r(Oz) = Π[X] ⊕ Int(Z^r)` with
  universal set-sized image `Int(Z^r)` (Theorem 16.7); the Newton
  least-common-multiple criterion for congruences modulo every omnific integer
  (Theorem 16.14); the `p`-adic completion `C(Z_p^r, Z_p)` and its characters,
  most not evaluations (Corollary 16.20, Theorem 16.22); rational self-maps of
  `Oz`, `Oz[i]` are polynomial, nonlinear images have holes of every surreal
  radius, and rational bijections are affine (Theorems 16.25, 16.28,
  Corollary 16.29). For every unital `D ⊆ k ∈ {R, C}` (16): a polynomial `f` of
  degree `d ≥ 2` over a set-sized Hahn field `K_G` and a fresh `t = ω^b`, `b > G`,
  satisfy `f(D + Π_k) ∩ (f(t) + K_G) = {f(t)}`, every root of `f(Y) = f(t) + c`
  (`c ≠ 0`) having a forbidden block of negative exponents in one of the first
  `d − 1` layers with an explicit coefficient (Theorems 16.35, 16.36); the fresh
  fiber is given by the rotational symmetries of the centered polynomial
  (Theorem 16.40); rational self-maps of `D + Π_k` are polynomials and the
  surjective ones are `uX + a`, `u ∈ D^×` (Theorems 16.42, 16.43); `Num_r` of
  `D + Π_k` is `Int(D^r) ⊕ Π_k[X]` (Proposition 16.45); lower-set grids are optimal
  tests (Theorem 16.46); fresh probes certify rational maps (Theorem 16.49); no
  set-sized sample tests all rational self-maps (Theorem 16.51). The image gap
  contains `x² = ω² + 1` and `X^n = aω^γ + β` (in the sibling report) and 08's
  `X^m = ω^γ + 1` as special cases (Remark 16.37).
- **Theorem H (Theorem 17.1, from 11 and 13).** The Grothendieck ring of the
  ordinals under natural operations is not a quotient of `Oz` (every unital ring
  map from `Oz` to it has image `Z`), answering the quotient addendum of
  MathOverflow question 188430 (Jesse Elliott, 2014) negatively; the question's
  only answer (Eric Wofsey) concerns transcendence degree. 13 gives the same
  answer with the same two proofs (Remark 17.2).
- **Theorem I (Section 13, from 12 and 14).** For the set-sized core
  `A_d = D + ⊕_{0≠α∈Q_{≥0}^d} K X^α ⊂ Oz` (coordinatewise exponent cone),
  `Tor_{>0}(D, D) = 0` but `fd D = d`, with the full multigraded
  `Tor(D, A_d/(X_i : i ∈ F))` (Theorems 13.4, 13.7, Corollary 13.8); enlarging to
  the totally ordered cone of the same exponent group gives the nonflat
  extension `A_d → T_Γ` with `fd D = 1`, `pd D = 2` (Theorems 13.13, 13.14). For a
  coefficient lattice `M` of rank `r ≥ 2`, `L(M) = M + Π` has first syzygy
  `Π^{r−1}` and is not finitely presented or flat; over `A_d` and `T_Γ`,
  `fd L(M) = d`, resp. `1`, and cyclic quotients `A/J` have `fd = d + 1`, resp. `2`
  (Theorem 13.11); `L(M) ⊗ L(N) ≅ Π ⊕ (M ⊗ N)` with torsion
  `ker(M ⊗ N → MN)` annihilated exactly by `Π` (Theorem 13.18); the nonlinear Rees
  equations are exactly the ordinary homogeneous relations among the generators,
  the first one for `(ω, 2^{1/d} ω)` in degree `d` (Theorems 13.21, 13.22,
  Corollary 13.23); `L(M) ≅ L(N)` iff `N = cM` (Theorem 13.24); invertible ideals of
  a real order realize its Picard group under torsion-free tensor product
  (Theorem 13.25, with `Z[√10]`); `L(M)* = Π` and `L(M)** = 𝒜_{k,k}`
  (Theorem 13.27).

## What the report does not claim

- All thirteen sources are AI-assisted, unrefereed drafts that call their main
  results candidate original or proposed contributions; priority is not
  certified, no named conjecture (Conway's refinement problem, factorization,
  GCD) is claimed solved, and nothing is formalized: the repository has no
  omnific Lean module and `docs/FORMALIZATION.md` maps none of these labels. The
  merge results are no more refereed than the sources.
- The universal theorem is not an isomorphism `Oz ≅ Z`, does not classify class
  ideals, class modules, automorphisms or factorizations, concerns only
  multiplicative maps (additive coefficient extraction detects `ω^γ`), and fails
  verbatim over every fixed set-sized exponent group. Size alone and
  divisibility alone do not prove it.
- The exact thresholds are proved for the five constructions and the two
  fixed-group examples only; the general fixed-group question (Question 18.1)
  stays open, and no classification of exponent groups or support restrictions
  is claimed.
- `pd_A Z` for the five constructions is known only to be at least `2`, except
  that it is exactly `2` when the tail is countably generated (Question 18.3,
  partly answered); nonarithmetic class primes are treated conditionally and
  their existence is not claimed (Question 18.4); the idempotents and primes of
  `Oz/(1+ω^a)` are not classified.
- "Flat dimension one" is a property of rings whose exponents form a totally
  ordered cone (the five constructions, `T_Γ`, 14's `A_0`, the class ring in the
  two-universe reading); it is not asserted for arbitrary subrings of `Oz`, whose
  flat dimensions are unbounded (Remark 13.16). Nothing is claimed about the
  homological dimensions of the class ring `Oz`; `pd_{A_d} D` for `d ≥ 2` and the
  weak global dimensions of the cores are open (Question 18.12). The
  finite-support cores are outside Theorem A: the augmentation detects their
  tails (Proposition 13.2).
- The support-threshold theorem is stated for `k ∈ {R, C}` as in 04 and 11,
  and no Gaussian analogue of 10's congruence criterion is given. 16's
  surjectivity rigidity is one-variable and for rational functions only.
- Section 18.2 keeps every limitation stated by a source, numbered per source:
  03 (19 items), 04 (14), 06 (14), 07 (13), 08 (13), 09 (12), 10 (12), 11 (12),
  12 (12), 13 (10), 14 (12), 15 (11), 16 (8), and 8 for the merge (170 in all).
  Section 18.3 lists fourteen questions, merging duplicates across sources, with
  their status: one answered (Question 18.2), one answered only for specific
  examples and constructions (Question 18.1, which also absorbs 13's and 15's
  cardinal-bound questions), one partly answered (Question 18.3), one settled for
  cardinal support bounds only (Question 18.8), ten open.
- The finite checks validate finite identities only; they verify no infinite
  support, class-size, cardinal, maximal-ideal, `Ext`, flatness or priority
  statement.

## Corrections and stale statements

- **Repository searches.** The audits of 06 (`06-universal-quotient-source_audit.md`,
  §1), 08 and 11 report a repository code search for "omnific" with no hits,
  and 09 an incomplete result; so do 13 (its §11.2) and 15 (its §13.2 and
  `15-set-sized-representations-SOURCE_AUDIT.md`). *Correction (23 September
  2026):* at their pins (including `71e9606` for 13–16) the repository already
  defined `Oz = Π ⊕ Z` at `found:eq:omnific` in the foundations report and used
  omnific integers in the trigonometry, gamma–zeta, analysis and
  euclidean-three-space reports; what it lacked was a report on omnific
  arithmetic. It now has two (this one and the sibling).
- **Novelty of 13 and 15.** 13 calls the universal theorem and its answer to
  Elliott's addendum proposed contributions, and 15 calls the universal theorem
  candidate-original. Both results are in the eight batch-24 manuscripts, dated a
  day earlier, which 13 and 15 could not see (their pin precedes `be06fc8`); they
  are credited as independent re-derivations (Theorem 5.1, Remark 17.2). 13's and
  15's questions on optimal cardinal bounds are answered by the threshold theorem
  for the five constructions (Theorem 10.10) and are part of Question 18.1.
- **16's repository search** for integer-valued polynomials was accurate at its
  pin; the collection now has 10's treatment (Section 16).
- **Prior manuscripts.** 03's `SOURCE_NOTES` calls its companion draft
  (`omnific_integers(1).tex`) not redistributed, and 04's audit calls its prior
  manuscript (`omnific_integers_diophantine.tex`) absent from the pinned tree.
  They are manuscripts 05 and 02 of the sibling report; 14's "companion
  manuscripts" (the same files and *Cardinal Visibility and Normalization*) are
  manuscripts 02 and 05 of the sibling report and 03 of this one.
- **Literature.** 09 (text and audit) credits "Proposition 8.2.1 on
  separated-scale division" of L'Innocente–Mantova; the separated-scale
  factorization is their Fact 8.0.1 (Gonshor's Theorem 8.6) with the example on
  p. 46, as 11 cites, and Proposition 8.2.1 is the truncation criterion for
  divisibility that 08 cites (Section 4.2).
- **Sources.** 03's source prints "C e B[i]" for `C ≠ B[i]` (Proposition 15.18);
  09's hypothesis `λ ≥ 2^ℵ0` follows from `λ^ℵ0 = λ` (Section 11.4); 04's remark
  that its `Q ⊕_lex Q` example involves "only a countable family" is true but
  misleading (Remark 10.6); 06's remark on `|R_κ/xR_κ|` needs no cardinal
  hypothesis (Section 12). 12 assumes `c² ∈ D` for the flat dimensions `d + 1` and
  `2` of its cyclic modules but needs it only for its `Tor_2` formula
  (Theorem 13.11), and gives only bounds for projective dimensions that are exact
  in rank one (Proposition 13.12). 14 credits the sibling report's example
  `[1:√2]` but not its rationality theorem for primitive directions, of which 14's
  unimodular-direction criterion is the Gaussian and principal-ideal extension.
  No source contains a false theorem.
- 07's audit describes the staging directory at its pin (Gamma–zeta archives),
  and 15's audit says `docs/new` held only its README at its pin; both are
  snapshot statements.
- The shipped audit files keep these statements verbatim. Several delivered
  files name files that are not shipped: the source `.tex` and `.pdf` files
  (`article.tex`, `omnific_small_quotients.tex`, `omnific_set_shadows.tex`,
  `omnific_homological_dimension.tex`, and others), the hash blocks of
  `04-universal-residue-build_report.json` and
  `06-universal-quotient-build_audit.json`, the source packages' `SHA256SUMS.txt`
  files, and the original script names used by the Makefiles and build scripts.

## Relation to the neighbouring reports

- [`omnific-diophantine-geometry`](../omnific-diophantine-geometry/) (sources
  01, 02, 05 and later additions) is the sibling report, written concurrently. It
  quotes 05's universal set-sized quotient theorem and refers here for the proof,
  which is the explicit-telescope route of Theorem 5.1. 05's "exact size
  boundary" question, kept there, is answered here by the constructions of
  Section 11 and Theorem 10.10 for specific integer parts; the general version is
  Question 18.1. The preliminaries (normal form, `ct`, support gaps,
  `Frac Oz = No`) overlap Sections 2–3. It prints 13's exact decomposable fibers
  and norm theorems and 14's unimodular-direction criterion (with its own
  rationality theorem for primitive directions), and it cites 16's image gap
  (Theorem 16.36) as the general form of its equations `x² = ω² + 1` and
  `X^n = aω^γ + β`.
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
- [`hahn-evaluation-at-omega`](../hahn-evaluation-at-omega/) separates finite
  polynomial evaluation at `ω` from evaluation of unrestricted series; 12's
  embeddings of its cores use finite normal forms only.
- [`trigonometry`](../../surcomplex/trigonometry/) uses `2πOz = Π + 2πZ` as a
  period kernel and the same `Π` with the opposite `t`-exponent sign.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 117 pages with no errors, warnings, undefined references or
overfull boxes. Build in a copy of the directory and do not commit the
auxiliary files.

The thirteen check programs were rerun for the two merges on copies (Python
3.14.4, SymPy 1.14.0); all pass and reproduce the recorded outputs up to line
endings and the recorded Python version. **Several write files by default**:
04 always writes `verification.json` next to the script; 06, 09 and 14 do so
unless given `--output` (14 writes `verification.json`); 07 writes
`verification_results.json` and 15 writes `finite_checks.json` in the working
directory unless given `--output` (15's own README runs it with
`--output finite_checks.json`, which overwrites its recorded result); 12 always
writes `audit_results.json` next to the script; 16 writes
`verification_results.txt` next to the script unless given `--output`. Run them
with an explicit output in a scratch directory, and run 04 and 12 on a copy:

```sh
cd docs/surreal/set-sized-quotients-of-omnific-integers
T=$(mktemp -d)
python code/03-cardinality-normalization-verify_identities.py > "$T/03.txt"   # 2,362 checks; = data/03-...
cp code/04-universal-residue-verify_identities.py "$T/" && python "$T/04-universal-residue-verify_identities.py" > /dev/null   # writes $T/verification.json
python code/06-universal-quotient-verify.py --output "$T/06.json"             # 17,586 assertions
pip install -r data/07-quotient-rigidity-requirements.txt                      # sympy==1.14.0, for 07, 10, 12, 14, 16
python code/07-quotient-rigidity-verify_finite.py --output "$T/07.json"       # 621 checks
python code/08-small-rings-finite_checks.py > "$T/08.txt"                     # 1,277 cases
python code/09-set-shadows-verify.py --output "$T/09.json"                    # 597 assertions
python code/10-omnific-arithmetic-checks.py > "$T/10.txt"                     # 171,395 checks, about 15 s
python code/11-set-sized-algebra-check_finite_identities.py --output "$T/11.json"   # 1,858 checks
cp code/12-homological-dimension-check_boolean_tor.py "$T/" && python "$T/12-homological-dimension-check_boolean_tor.py"   # 780 multidegrees; writes $T/audit_results.json
python code/13-small-target-rigidity-verify.py > "$T/13.txt"                  # 6 groups; = data/13-...
python code/14-arithmetic-tensors-verify.py --output "$T/14.json"             # 2,189 assertions
python code/15-set-sized-representations-verify_identities.py --output "$T/15.json"   # 820 cases
python code/16-fresh-scale-verify_finite.py --output "$T/16.txt"              # 1,354 assertions, about 12 s
```

12 requires SymPy but ships no requirements file; 14 and 16 ship
`sympy==1.14.0`. Run 12 without Python's `-O` option (its checks are
assertions). The shipped `04-…-Makefile`, `06-…-Makefile`, `10-…-Makefile`,
`09-set-shadows-build.sh`, `11-set-sized-algebra-build.sh`,
`12-homological-dimension-build.sh` and `14-arithmetic-tensors-build.py` use the
original package file names (`verify.py`, `article.tex`,
`omnific_set_shadows.tex`, `omnific_homological_dimension.tex`,
`code/check_finite_identities.py`, …) and do not run as shipped; they are kept
as provenance. For the second merge an independent exact computation, not
shipped, rechecked Theorem 13.7 in 1,626 cases (every proper subset `F`
included) and Corollary 13.23 for `d ≤ 8`, `n ≤ 12`.
