# Set-Sized Quotients of the Omnific Integers

**The universal constant-term quotient, exact cardinal thresholds, support
thresholds, and what survives in large quotients**
Merged research report, 23 September 2026, from nineteen manuscripts: eight of
22 September 2026 (batch 24, placed in `be06fc8`): 06 (the base), 03, 04, 07,
08, 09, 10 and 11; five of 23 September 2026 (batch 25, placed in `cf350b1`),
numbered here 12 to 16 by their file prefixes; three of 23 September 2026
(items 01, 03 and 05 of batch 26, placed in `f4c9504`), numbered here 17 to 19
by their file prefixes; one of 23 September 2026 (item 01 of batch 28,
placed in `c6359e4`), numbered here 20 by its file prefix
`20-boolean-branching-`; one of 23 September 2026 (item 01 of batch 29,
placed in `66d7e55`), numbered here 21 by its file prefix
`21-derived-arithmetic-`; and one of 23 September 2026 (item 09 of batch 31,
placed in `9d28e28`), numbered here 22 by its file prefix `22-finite-tests-`.
Manuscript 05 of batch 24 proves the unital universal
theorem too; it is merged into the sibling report
[`omnific-diophantine-geometry`](../omnific-diophantine-geometry/) and credited
here.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 177 pages
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
20-boolean-branching-PROOF_AUDIT.md            source 20: proof obligations, independent checks, limitations
20-boolean-branching-SOURCE_AUDIT.md           source 20: repository pin, antecedents, novelty boundary
22-finite-tests-SOURCE_AUDIT.md                source 22: repository inspection, literature, novelty, verification boundary
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
  17-relations-arithmetic-verify.py                   source 17 checks (347; needs SymPy; writes by default, see below)
  18-polynomial-rigidity-verify.py                    source 18 checks (499; needs SymPy; always writes, see below)
  18-polynomial-rigidity-build.sh                     source 18's build script (original file names)
  19-normalization-fibres-checks.py                   source 19 checks (253; needs SymPy; stdout)
  19-normalization-fibres-build.sh                    source 19's build script (original file names; overwrites checks.txt)
  20-boolean-branching-verify.py                      source 20 checks (6,674; needs SymPy; always writes, see below)
  20-boolean-branching-Makefile                       source 20's Makefile (original file names)
  21-derived-arithmetic-verify.py                     source 21 checks (1,608; stdlib; writes by default, see below)
  21-derived-arithmetic-build.sh                      source 21's build script (original file names)
  21-derived-arithmetic-build.ps1                     source 21's PowerShell build script (original file names)
  22-finite-tests-verify.py                           source 22 checks (1,776; needs SymPy; always writes, see below)
  22-finite-tests-build.sh                            source 22's build script (original file names)
  22-finite-tests-build.ps1                           source 22's PowerShell build script (original file names)
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
  17-relations-arithmetic-verification.json               recorded run of the source 17 checks
  17-relations-arithmetic-build_report.json               source 17's build and document-validation record
  17-relations-arithmetic-requirements.txt                sympy==1.14.0
  18-polynomial-rigidity-verification_results.json        recorded run of the source 18 checks
  18-polynomial-rigidity-build_report.json                source 18's build, rendering and verification-scope record
  18-polynomial-rigidity-requirements.txt                 sympy==1.14.0
  19-normalization-fibres-checks.txt                      recorded run of the source 19 checks
  20-boolean-branching-verification_results.json          recorded run of the source 20 checks
  20-boolean-branching-BUILD_REPORT.json                  source 20's build, rendering and diagnostics record
  20-boolean-branching-requirements.txt                   sympy==1.14.0
  21-derived-arithmetic-verification_results.json         recorded run of the source 21 checks
  21-derived-arithmetic-provenance.json                   source 21's pin, scope and verification metadata (no hashes)
  22-finite-tests-verification_report.json                recorded run of the source 22 checks
  22-finite-tests-verification_report.txt                 the same run as text
  22-finite-tests-requirements.txt                        sympy==1.14.0
```

Every label in `article.tex` carries the prefix `osq:`. The large-quotient part
(Section 14) uses the sub-prefix `osq:if:`, the integral-closure part
(Section 15) `osq:nm:`, and the polynomial-map part (Section 16) `osq:pm:`.
The five later manuscripts use `osq:hd:` (12) and `osq:tn:` (14) in the new
Section 13, `osq:fs:` (16) in Sections 16.6 and 16.7, `osq:rep:` (15) for its
two printed additions and `osq:str:` (13) for the remark crediting its answer to
Elliott's question. The three batch-26 manuscripts use `osq:rel:` (17) in
Section 13.9, `osq:nf:` (19) in Section 15.8 and `osq:or:` (18) in Section 16.8.
The batch-28 manuscript uses `osq:bb:` (20) in Section 15.9 and for Question 18.18.
The batch-29 manuscript uses `osq:da:` (21) in Section 13.10.
The batch-31 manuscript uses `osq:ft:` (22) in Section 16.10 and for
Questions 18.19 and 18.20 (30 labels).
The report has 551 labels (521 before the sixth merge, 505 before the fifth,
469 before the fourth, 409 before the third and 334 before the second; none was
renamed or removed, and no earlier statement was renumbered). The audit files and
programs keep the source numbers `03` to `22`, and the audit files keep their
sources' own notation and theorem numbering. No source manuscript is shipped.

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

## Nineteen sources, one report

The eight manuscripts of batch 24 answer the same question, *what can a
set-sized ring or module see of an omnific integer?*, with the same answer:
exactly the ordinary integer constant term. They then diverge. The report
prints the common spine once (Sections 2–7) and keeps every result of every
source. Two batch-25 manuscripts (13, 15) reprove that answer independently;
two (12, 14) add the ordinary homological and tensor algebra of subrings of
`Oz`; one (16) adds fresh-scale arguments for polynomial and rational maps.
The three batch-26 manuscripts extend three sections: relation modules and
`Tor` of coefficient-lattice ideals (17), ordinary-output rigidity of
integer-valued polynomials (18), and the arithmetic fibre of the integral
closure (19). The other seven batch-26 items are in
[`omnific-preserving-automorphisms`](../omnific-preserving-automorphisms/) and
[`omnific-groups-and-lattices`](../omnific-groups-and-lattices/). The batch-28
manuscript (20) answers 19's question on the Boolean algebra of that fibre
(Section 15.9); the other eight batch-28 items were placed in other reports.
The batch-29 manuscript (21) answers the first clause of 12's and 14's
Question 18.12: `pd_{A_d} D = d + 1` (Section 13.10); the other eight batch-29
items were placed in other reports. The batch-31 manuscript (22) certifies
rational functions of several variables by finitely many values at one fresh
scale and joins the polynomial-map section (Section 16.10); about half of it
re-derives 16's and 10's results, which it did not see; the other eight
batch-31 items were placed in other reports.

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
| **12** | *Arithmetic Invisibility and Homological Dimension in Omnific Integer Cores* (21) | none stated | Coordinate-cone cores `A_d ⊂ Oz`: the Boolean flat resolution (Theorem 13.4), the multigraded `Tor` (Theorem 13.7), `fd D = d` (Corollary 13.8); the noncoherence certificate (Theorem 13.9(iii)); the ordered-cone collapse (Theorems 13.13, 13.14); projective bounds and the telescope (Proposition 13.12; the bounds for `A_d` are attained, by 21's Corollary 13.47 and Theorem 13.48). Files `12-homological-dimension-*`. |
| **13** | *Small-Target Rigidity and Arithmetic Specialization* (21) | `71e9606` | An independent proof of the universal theorem (credited at Theorem 5.1) and of the answer to Elliott's addendum (Remark 17.2). Its fiber and norm theorems are printed in the sibling report. Files `13-small-target-rigidity-*`. |
| **14** | *Arithmetic Tensors in the Omnific Integers* (19) | `71e9606` | Coefficient-lattice modules `L(M) = M + Π`: syzygy (Theorem 13.9), nonflatness (Proposition 13.10), tensor normal form (Theorem 13.18), exterior and symmetric powers (Theorem 13.20), Rees equations (Theorems 13.21, 13.22, Corollary 13.23), Hom and isomorphism types (Theorem 13.24), ideal classes (Theorem 13.25), duals (Theorem 13.27), matrix kernels (Theorem 13.28), `fd` over `A_0` (Theorem 13.11). Files `14-arithmetic-tensors-*`. |
| **15** | *Omnific Integers Have Only Ordinary Set-Sized Representations* (21) | `71e9606` | An independent proof of the universal theorem and its consequences (credited throughout Sections 3–9); two one-line additions (Corollary 5.5, Proposition 7.3). Files `15-set-sized-representations-*`. |
| **16** | *Fresh-Scale Image Gaps and Rational Rigidity for Omnific Integers* (23) | `71e9606` | The image gap with forbidden layers (Theorems 16.35, 16.36), fresh fibers (Theorem 16.40), rational collapse and surjective self-maps over any constant ring (Theorems 16.42, 16.43), optimal and Gaussian finite tests (Theorem 16.46, Proposition 16.47), rational probes and certificates (Theorem 16.49, Corollary 16.50), no set-sized sample (Theorem 16.51), co-small rigidity and hulls. Files `16-fresh-scale-*`. |
| **17** | *Proper-Class Relations and Arithmetic Endomorphisms of Omnific Ideals* (19) | `71e9606` | Independent proofs of 14's matrix, syzygy, Hom, tensor and power-growth theorems and 12's intersection (credited at Theorems 13.9, 13.18, 13.23, 13.24, 13.28). New (Section 13.9): no set-presentation and failure of the equational flatness criterion (Theorem 13.29); the embedding of the lexicographic models `R^11_{Γ,<κ}` in `Oz` (Lemma 13.30); exactly `κ` relations in every finite presentation (Theorem 13.31); `Tor_1 ≅ Tor_2 ≅ ker(M ⊗ N → K)` (Theorem 13.34), the self-`Tor` range and field test (Corollary 13.36, Proposition 13.37); `GL_2(D)` moduli with `2^ℵ0` classes (Theorem 13.38); orders and their realization (Theorem 13.39, Corollary 13.40, Example 13.41); modules killed by the tail (Theorem 13.42). Files `17-relations-arithmetic-*`. |
| **18** | *Polynomial Rigidity of Omnific Integer Lattices* (21) | `befe739` | Independent proofs of 10's and 16's classification of `Num_r`, finite tests, rational collapse and surjections (credited at Theorems 16.7, 16.9, 16.25, 16.46, Corollary 16.29). New (Section 16.8): the ordinary-output dichotomy over any discretely ordered ring (Theorem 16.56), the canonical translation and its coefficient test (Theorems 16.59, 16.60), the unique rich target (Theorem 16.61), composition alignment (Theorem 16.63), a Gaussian simplex test (Proposition 16.64), matrix and jet reductions (Theorem 16.65), rational functions on discretely ordered rings (Theorem 16.66), fixed Hahn workspaces (Corollary 16.67). Files `18-polynomial-rigidity-*`. |
| **19** | *Normalization and Arithmetic Fibres of the Omnific Integers* (23) | `befe739` | Independent proofs of four results of 03 and of the universal theorem (credited). New (Section 15.8): contraction, radicality, saturation (Lemma 15.28, Theorems 15.29, 15.30); real-rooted lifting (Theorem 15.32); the residue with `v² = −1` (Proposition 15.34); `𝒩/Π𝒩 ≅ Z̄[Idem]` (Theorem 15.38); finitely generated ideals (Theorem 15.39); integral doubling (Theorem 15.42); domain images (Theorem 15.46); detection by maps to `Z̄` and field targets (Theorem 15.49, Corollary 15.50); a finite-axiom form (Theorem 15.51). Files `19-normalization-fibres-*`. |
| **20** | *Proper-Class Boolean Branching in the Normalization of the Omnific Integers* (24) | `4cdeaec` | Independent proofs of 19's contraction, radicality and saturation (Lemma 15.28, Theorems 15.29, 15.30), coefficient copy, spectral idempotents and Boolean power (Lemmas 15.35, 15.36, Definition 15.37, Theorem 15.38), rational comparison and doubling (Lemma 15.41, Theorem 15.42), factorization of set-sized images, class ultrafilters and detection (Corollary 15.45, Lemma 15.48, Theorem 15.49), of most of Propositions 15.34, 15.43 and Theorem 15.46, and of the universal theorem for `Oz` (credited at Theorem 5.1). New (Section 15.9): monic radical certificates (Lemma 15.53, Corollary 15.54); support projection and exact descent (Lemma 15.55, Theorem 15.57, Corollary 15.58); one-scale rational functions (Theorem 15.60); independent quadratic branches (Lemma 15.63); uniform splitting (Theorems 15.65, 15.66); rank extension of set-sized Hahn fibres (Theorem 15.70); relative Boolean freeness, an explicit ordinal family, atomless proper-class `Idem` (Theorems 15.71–15.73); split idempotent matrices (Corollary 15.74); reduced fibres of fixed Hahn fields (Proposition 15.76); the surcomplex fibre (Corollary 15.77); no jointly faithful set of small targets (Theorem 15.79); `2^κ` branches through prescribed data (Theorem 15.80, Corollary 15.81). Files `20-boolean-branching-*`. |
| **21** | *Exact Homological Dimensions and Arithmetic Intersections in Omnific Integer Rings* (25) | `9693b28` | Independent proofs of 17's second-`Tor` identification with its rank, the self-`Tor` rank and the `Tor` groups against modules killed by the tail (credited at Theorem 13.34, Corollary 13.36, Theorem 13.42); its flat face resolution, `fd D = d` and lattice syzygy are 12's and 14's (Theorems 13.4, 13.9, 13.11, Corollary 13.8). New (Section 13.10): flat resolutions and flat dimensions of the face quotients (Proposition 13.43); a countably generated free Koszul telescope (Theorem 13.44); the top `Ext` as a `lim¹` cokernel (Theorem 13.45) containing `D^N/D^(N)` (Theorem 13.46); `pd_{A_d} D = d + 1` and `pd` of every face quotient (Corollary 13.47); `pd L(M) = d + 1`, `pd A_d/J = d + 2` (Theorem 13.48); a flat DGA resolution (Theorem 13.50); the first-`Tor` window (Theorem 13.51); the linear-disjointness test (Lemma 13.52, Theorem 13.53); the self-`Tor` product and its alternating and symmetric parts (Theorem 13.54, Corollary 13.55); framed reconstruction of orders (Theorem 13.56); the square-zero constant-term shadow (Theorem 13.57). Files `21-derived-arithmetic-*`. |
| **22** | *Finite Tests at New Surreal Scales* (24) | `bcac55a` | Independent proofs of 16's fresh exponent, Laurent blocks and detector, of 10's binomial closure, grid test and decomposition, of 16's optimal tests, multivariate collapse, one-variable certificate (`d + 2` values), no-set-test theorem and one-variable removal of exceptions (credited at Lemma 16.5, Theorems 16.6, 16.7, 16.9, Lemma 16.30, Theorem 16.31, Corollary 16.32, Theorem 16.33, Proposition 16.45, Theorems 16.46, 16.49, Corollary 16.50, Theorems 16.51, 16.52); all were in this report at its pin. New (Section 16.10): rectangular grids and good specializations with the resultant degree bound (Lemmas 16.68, 16.69); the single-scale certificate with at most `(d+1)^m + m(2d²+2d+1)^{m−1}` values (Theorem 16.70); common tests for a set of functions (Corollary 16.72); a second pole-free witness for Theorem 16.51, in every number of variables (Remark 16.73, Example 16.74); removal of set-sized exceptions in `m` variables (Theorem 16.75); composition of the specialization (Remark 16.76); the leading-exponent example (Example 16.77); the coordinate-degree Gaussian grid and Gaussian certificate (Theorems 16.78, 16.79); tensor base change `Λ ⊗_D Int(D^m) ≅ Num_m(Λ)` (Theorem 16.80); exact lifting of constant test sets (Definition 16.81, Theorem 16.82); finite image-ideal generators (Theorem 16.83); birational rigidity (Corollary 16.84, Example 16.85); fresh scales in a fixed Hahn workspace (Proposition 16.86); a resultant example (Example 16.87). Files `22-finite-tests-*`. |

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
  sources; neither adds generality. So are 17 (`k ∈ {R, C}`, any set-sized
  `D_0 ⊆ k`, by 06's scaled-field collision), 19 (`Oz`, by the explicit
  telescope) and 20 (`Oz`, by the telescope with exponents `a/ω^{α+1}`), which
  also add no generality.
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
  Corollary 16.29, Theorem 16.43, Proposition 16.45, Theorem 16.46). From the
  third merge: 17's matrix kernels, lattice syzygy, Hom and isomorphism types,
  tensor torsion and power growth under 14's labels, and its intersection
  `(ω^γ) ∩ (αω^γ) = ω^γ Π` under 12's (Theorems 13.9, 13.18, 13.23, 13.24,
  13.28); 18's description of `Num_r`, total-degree tests, binomial basis,
  rational collapse and surjections under 10's and 16's (Theorems 16.7, 16.9,
  16.25, 16.46, Corollary 16.29; 18's canonical-form proof of the surjections is
  kept as a third route); 19's constant slices, absence of finite images and
  complexification defect under 03's (Theorems 15.14, 15.19, 15.20,
  Proposition 15.18; 19's witness `w_±` and its proof of the finite-image
  statement are kept as second routes), and 17's and 19's proofs of the
  universal theorem as further proving sources of Theorem 5.1. From the
  fourth merge: 20's reproofs of 19's fibre theory under 19's labels (tagged
  `[19, 20]` where 20 proves the whole statement), its proof of the universal
  theorem at Theorem 5.1, and its dominant-scale lemma as 16's Laurent blocks
  (Lemma 15.62 cites Theorem 16.31 and Corollary 16.32, adding 20's surjectivity
  step); 20's class-ultrafilter lemma from a set with the finite intersection
  property is printed beside 19's (Lemma 15.78). From the fifth merge: 21's
  second-`Tor` identification with its rank, its self-`Tor` rank, the pair
  `Z[√2]`, `Z[√3]` and its `Tor` groups against modules killed by the tail under
  17's labels (tagged `[17; 21]`: Theorem 13.34, Corollary 13.36, Theorem 13.42),
  and its flat face resolution, `fd D = d` and lattice syzygy cited as 12's and
  14's (Theorems 13.4, 13.9, 13.11, Corollary 13.8); 21's extension of 17's
  `Tor` formulas to the class ring in a two-universe reading is stated in
  Theorems 13.51 and 13.57. From the sixth merge: 22's fresh exponent, Laurent
  blocks, binomial closure, grid test, decomposition of `Num_m`, optimal
  polynomial tests and no-set-test theorem under 10's and 16's labels (tagged
  with 22: Lemma 16.5, Theorems 16.6, 16.7, 16.9, Lemma 16.30, Theorems 16.31,
  16.46, 16.51), and its detector, multivariate collapse, one-variable
  certificate and one-variable removal of exceptions credited at Corollary
  16.32, Theorems 16.33, 16.49, Corollary 16.50 and Theorem 16.52; 22's own
  witness `2ω^{ωb}/(2X + 2t + 1)` for Theorem 16.51 is kept as a second witness
  (Remark 16.73), and its multivariate certificate is kept beside 16's smaller
  probe certificate (Remark 16.71). 22's Gaussian grid is the coordinate-degree
  twin of 18's simplex test (Theorem 16.78, Proposition 16.64).
- **Printed in the sibling report, not here:** 13's exact fibers of products of
  linear forms and its étale norm and Pell theorems; 14's criterion for unimodular
  projective directions, which is the Gaussian and principal-ideal extension of
  that report's rationality theorem for primitive constant directions.
- **Renamed symbols** (Sections 2.4, 13, 13.9, 15.8, 15.9, 16.6, 16.8, 16.10): the purely infinite ideal is the
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
  constant ring), its centre `μ` is `s`, its `L_ζ, A_ζ` are `a_ζ, c_ζ`. In
  Section 13.9: 17's positive-support ideal `𝔪` (not the infinitesimal ideal,
  which is `𝔪_k` here) is `Π`, its lattices `L, M` are `M, N`, its ideals
  `J_L^γ` are `J_γ(M) = X^γ L(M)`, its `E(L)`, `(M:L)`, `μ_{L,M}`, `T(L,M)` are
  `𝔬(M)`, `(N:M)`, `m_{M,N}`, `𝒯(M,N)`, its kernel dimensions `d, r` are
  `q, ℓ`, and its models `A_κ, 𝔪_κ` are `R^11_{Γ_κ,<κ}, Π^11_κ`. In Section 16.8:
  18's `𝒥, A, K, k_0, Int(A)` are `Π_Λ, Λ, E, F_0, Num_1(Λ)`, its `f̄` is
  `ct_*(f)`, its `pi(a)` is `å`, its loci `E_f, E_b(f)` are `ℒ_f, ℒ_{f,b}`. In
  Section 15.8: 19's `𝒥, N_R, N_C, K_ε, B_ε, E_ε` are `Π, 𝒩, 𝒩_C, Π𝒩_•,
  𝖡_•, 𝖡^Q_•`, its Boolean algebra `ℰ` is `Idem(𝖡_•)` (`ℰ` would clash with
  07's field), its unit `u` is `υ_T` with residue `𝗏`. In Section 15.9: 20's
  `N_R, N_C, 𝒥, K_R, B_R, E, ℰ` are as for 19; its local rings
  `F_G, A_G, J_G, N_G, C_G` are `K_G` (16's Hahn field), `𝒜(G)`, `Π(G)`,
  `𝒩(G)`, `𝖢(G)` (parentheses to keep them apart from 03's `𝒩_κ`; `C` is
  03's letter); its projection `π_G` is `pr_G` (`π_b` is a detecting map in
  Theorem 5.12); its dominant exponent `a`, group `H = G ⊕ Za` and monomial
  `T = ω^a` are 16's fresh `b`, `G̃ = G ⊕ Zb` and `t = ω^b` (`H_a` is the scale
  subgroup, `H` is 03's parameter in `u_H`); its branches `s_0, s_1, s_r` are
  `ϱ_0, ϱ_1, ϱ_r`, its specializations `θ_±` are `σ_±` (`θ = κ^ℵ0` in 03's
  construction), and its splitting element `w(T)` is `𝗐_t` (`w_±` are 19's
  idempotents). In Section 13.10: 21's `k, 𝓘_d, L, M, M_L` are
  `K, Π_d, M, N, L(M)`; its `t_a = ω^a` is `X^a` (here `t^g` means `X^{-g}`) and
  its `J_{a,L}` is `J_a(M)`; its face quotient `B_U` is `𝖥_U`, its `c = |U|` is
  `|U|`, its ideals `Q_n` are `J^{(n)}_U`, its `K_n, F, σ, 𝒯, δ_N` are
  `Kos_n, Kos, sh, Tel, Δ^∨_P`; its `R_0, R, 𝓘` are `T_Q, 𝒜_{D,k}, Π`, its
  `𝒦(L, M)` is `𝒯(M, N)`, its `W_L, S, T, H_j, λ, Q_2` are
  `Syz_M, A/I, A/J, 𝖳_j, 𝖻, Ind_2`, its `C_{a,b}, 𝓗_k(0, c)` are
  `𝖫_{g,h}, Π_{(0,e)}`, and its fields `E, F` over `F_0`, orders `O` and kernels
  `𝒦_O` are `K_1, K_2` over `Frac D`, `𝔬` and `𝒯(𝔬, 𝔬)`. In Section 16.10:
  22's `𝒥_R, 𝒥_C, 𝒜_k, Og` are `Π, Π_C, 𝒜_{k,k}, Oz[i]`; its `B ∈ {Oz, Oz[i]}`
  is `Λ` (`B` is 18's discretely ordered ring, `ℬ` the ring `D + 𝔪_k`); its
  `Int(B^m)` and `Int^R(B^m)` (surreal polynomials and rational functions
  preserving `B`) are `Num_m(Λ)` and `Num^rat_m(Λ)`, `Int` being kept for the
  ordinary `Int(D^m)`; its `E = Frac D` is `F_0` (`E` is the ambient field);
  its `B_ν` are the binomial products; its coefficient group `Γ`, field
  `K_k(Γ)`, exponent `β` with `Γ ≪ β`, monomial `T = ω^β` and embedding `ℰ_T`
  are 16's `G`, `K_G`, fresh `b > G`, `t = ω^b` and `ι_b` (22's `Γ ≪ β` means
  `|γ| < β` for all `γ`, not the scale relation `h ≪ a` of (2.4)); its field
  `L` is `K` (`L` is a lower set), its `H_j` is `𝗁_j` (`H` is a group), its
  bound `D = 2d² + 2d` is `𝖭_d` (`D` is the constant ring); its box, remote
  grid and test set `ℬ_{m,d}, ℋ_{m,D}(T), 𝒯_{m,d}(T)` are
  `□_{m,d}, 𝖱_{m,d}(t), 𝖳𝖾𝗌𝗍_{m,d}(t)`; its Gaussian grid `G_d` is `C_{d+1}`
  (16's notation, an interpolation grid here, not the residue system
  `C_{d!}`); its exceptional set `E` is `S`; its deceiver's `τ, η, A, λ, F_S`
  are `t, ωb, ω^{ωb}, a, R̃_S` (`η` is 18's translation, `R_S` 16's witness);
  and in its Section 9 its value group `Λ`, subgroup `Γ`, ring `B_Λ` and
  convex subgroup `C(Γ)` are `Γ`, `G`, `𝒜_{D,k}(Γ)` and `cvx_Γ(G)`.
- **Sign convention** (Section 2.2): large monomials, `ω^γ` infinite for
  `γ > 0`. The foundations report defines `Oz = Π ⊕ Z` (`found:eq:omnific`);
  the trigonometry report (`trigonometry:eq:split`) describes the same `Π` by
  negative `t`-exponents because it writes `t = ω^{-1}`.
- **Foundations.** NBG with choice for sets. 04, 06 and 09 (and 05) state
  global choice; none of them uses it. 13 and 15 add a two-universe reading.
  17 and 19 state class theory with global choice; 17's uses of it are avoided
  (Theorem 13.29 gives a choice-free Schanuel splitting), and 19's class
  ultrafilter (Lemma 15.48) is the only place where it is used, for the
  detection results (Theorem 15.49, Corollary 15.50), which say so. 20 states
  the same foundation; its splitting results need only choice for sets
  (Remark 15.75, a merge observation), and only its extension of branch maps
  (Theorem 15.80, with Lemma 15.78) uses class ultrafilters. 21 reads the
  class ring in two Grothendieck universes, as 13 does; its core theorems are
  ordinary set-sized mathematics. 22 reads its class statements in a class
  theory carrying `No` or with a lower and an upper universe, and chooses a
  fresh exponent only after a set of supports has been assembled.

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
- **From the third merge.** 17's relation counts, embedding and flat
  dimensions for `κ = ℵ0` as well (17 assumes `κ` uncountable but uses only
  regularity), with `pd Π = 1`, `pd D = 2` and `pd L(M) = 2` there
  (Lemma 13.30, Theorem 13.31, Remark 13.32); 17's `Tor` identification over
  12's cores and 14's `A_0` (Theorem 13.34), which gives
  `rank Tor_2(A/H, A/H) = 4 − rank(M²)` for 12's cyclic modules without 12's
  hypothesis `c² ∈ D` (Corollary 13.35); the comparison of 18's and 16's
  Gaussian tests (18's is smaller for `d ≥ 3`, Proposition 16.64); the images of
  08's invisible roots in domain images (Remark 15.47); and the explicit
  candidates reducing the question on `Idem(𝒩/Π𝒩)` to membership in `𝒩`
  (Remark 15.52; that reduction is now superseded by 20).
- **From the fourth merge.** 03's descent question answered from 20's support
  projection: `𝒩 ∩ F^03_κ = 𝒩_κ`, `Π𝒩 ∩ F^03_κ = √(Π^03_κ 𝒩_κ)` and the
  Gaussian forms (Corollary 15.59); 03's unit `u_H` is a one-radical uniform
  splitter, which decides both candidates of Remark 15.52 (nontrivial; the
  first is the second for `H = ω^{1/2}`), for every positive `H ∈ Π` supported
  in one cyclic group `Za` (Proposition 15.68); 20's splitting results need no
  global choice (Remark 15.75); and `𝖡_R` is residually set-sized although no
  set-indexed family of small targets is jointly faithful (remark after
  Theorem 15.79).
- **From the fifth merge.** 21's projective dimensions of lattice modules over
  `A_d` for every unital `D ⊆ K` (21 assumes a principal ideal domain only to
  have a basis; Theorem 13.48); and the observation that the cores `A_d`, with
  countably generated tails and (H1), (H3) but not (H2), have `pd D = d + 1`, so
  (H2) cannot be dropped from Proposition 13.12(v) (Remark 13.49).
- **From the sixth merge.** The comparison of 22's single-scale certificate
  with 16's probe certificate: for `m ≥ 2` the probes with the rectangular box
  need `(d+1)^m + m` values, fewer than 22's, but use `m + 1` fresh exponents
  where 22 uses one, in one coordinate (Remark 16.71); the conclusion of 16's
  no-set-test theorem for `𝒜_{D,k}` with every unital `D ≠ k`, by replacing
  `1/2` with any `c ∈ k \ D` (Remark 16.88); and the observation that where
  22's criterion gives no fresh exponent, 18's discrete-gap collapse still
  holds, so what is lost there is only the finite rational certificate
  (after Proposition 16.86).

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
  Proposition 7.3). A group-level strengthening (for `n ≥ 3` every
  homomorphism from the purely infinite congruence kernel of `E_n(Oz)` to a
  set-sized group is trivial) is in
  [`omnific-groups-and-lattices`](../omnific-groups-and-lattices/).
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
- **Theorem F (Section 15, from 03, 08, 19 and 20).** `Oz* = No`; the integral closure
  `𝒩` is proper, fine-dense, of zero conductor and not set-generated
  (Theorems 15.5, 15.12); constant slices, the complexification defect killed by
  `2` (Proposition 15.18), no finite quotients (Theorem 15.20), no nontrivial
  set-valued valuation of `No` containing `Oz` (Theorem 15.22); for `γ > 0` and
  `m ≥ 2`, `X^m = ω^γ + 1` has no root in `Oz[i]` but the root `1` in every
  set-sized image (Theorem 15.25). From 19 (Section 15.8): the extended ideal
  `Π𝒩` is radical and `𝒩/Π𝒩` is the integral closure of `Z` in its
  rationalization (Theorems 15.29, 15.30); every monic polynomial over `𝒩` can
  be changed by coefficients in `Π` into one with `d` distinct positive
  infinite roots (Theorem 15.32); `υ_T = (T − √(T² − 4))/2` is an infinitesimal
  integral unit whose residue squares to `−1` (Proposition 15.34);
  `𝒩/Π𝒩 ≅ Z̄[Idem]`, a finite-partition Boolean power of the ring of all
  complex algebraic integers, semihereditary with nilpotents of every index
  mod `p` (Theorems 15.38, 15.39, Proposition 15.40); integrally
  `𝒩_C/Π𝒩_C ≅ (𝒩/Π𝒩)²`, also mod 2 (Theorem 15.42); every set-sized domain
  image of `𝒩` or `𝒩_C` is `Z̄` or `F̄_p` (Theorem 15.46), and, with global
  choice, `Π𝒩` is the common kernel of the maps to `Z̄` (Theorem 15.49).
  From 20 (Section 15.9): for every set-sized subgroup `G ⊆ No`,
  `𝒩 ∩ K_G = 𝒩(G)` and `Π𝒩 ∩ K_G = √(Π(G)𝒩(G))`, so integrality witnesses at
  larger scales never help (Theorem 15.57); `𝒩 ∩ R(ω^a) = Z̄_R + ω^a R[ω^a]`
  (Theorem 15.60); every set-sized subring of `𝒩/Π𝒩` is split by one
  idempotent, e.g. the residue of `(1 − √(t²−1)√(t²/4−1))/2` for a fresh
  monomial `t` (Theorems 15.65, 15.66); relative free Boolean extensions of
  every set size, an explicit independent family `t_α = ω^{ω^α}` indexed by
  all ordinals, and `Idem(𝒩/Π𝒩)` atomless, a proper class, with no set-sized
  order-dense subset (Theorems 15.71–15.73), also for `𝒩_C` (Corollary 15.77);
  one dominant coordinate adds a free Boolean family of size `|K_G|` to the
  reduced fibre of any set-sized Hahn field (Theorem 15.70), and that reduced
  fibre is `Z̄[Idem]` for every nonzero `G` (Proposition 15.76); no
  set-indexed family of maps to set-sized rings is jointly faithful on
  `𝒩/Π𝒩` (Theorem 15.79), and, with global choice, every branch map extends
  in at least `2^κ` ways from any set of data (Theorem 15.80). With the merge:
  `𝒩 ∩ F^03_κ = 𝒩_κ` (Corollary 15.59).
- **Theorem G (Section 16, from 10, 16, 18 and 22).** `Num_r(Oz) = Π[X] ⊕ Int(Z^r)` with
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
  `X^m = ω^γ + 1` as special cases (Remark 16.37). From 18 (Section 16.8): a
  polynomial of degree `d` preserving a discretely ordered ring `B` (or `B[i]`)
  sends at most `d` inputs to `Z` (or `Z[i]`) unless it is an ordinary
  integer-valued polynomial after a translation, sharp in every degree
  (Theorem 16.56, Proposition 16.58); on `Oz`, `Oz[i]` the translation is a
  unique purely infinite `η = −å_{d−1}/(d a_d)` (Theorems 16.59, 16.60); in
  degree `≥ 2` at most one coset `b + D` has more than `d` preimages
  (Theorem 16.61), and composites of two such polynomials keep one exactly when
  they align (Theorem 16.63); a Gaussian test with `C(2n+d, 2n)` points
  (Proposition 16.64); matrix and jet reductions (Theorem 16.65); rational
  collapse for every discretely ordered ring with finitely many exceptions
  (Theorem 16.66); all of this also in fixed Hahn workspaces (Corollary 16.67).
  From 22 (Section 16.10): a rational function `P/Q` over `No` in `m`
  variables with coordinate degrees at most `d`, coefficients supported in a
  set-sized group `G` and `b > G`, preserves `Oz` iff it is defined and
  `Oz`-valued on the box `{0,…,d}^m` and on the `m` grids
  `{0,…,2d²+2d}^{j−1} × {ω^b} × {0,…,2d²+2d}^{m−j}`, at most
  `(d+1)^m + m(2d²+2d+1)^{m−1}` values (14 for `m = 2`, `d = 1`), uniformly
  over `K_G` (Theorem 16.70), with the Gaussian version on `C_{d+1}^m` plus the
  same grids (Theorems 16.78, 16.79); every set of functions has common tests
  (Corollary 16.72); a rational function defined and `Λ`-valued outside a set
  of points of `Λ^m` preserves `Λ` (Theorem 16.75); `Num_m(Λ) ≅ Λ ⊗_D Int(D^m)`
  (Theorem 16.80); a finite `S ⊆ D^m` tests `Λ` iff it tests `Int(D^m)`
  (Theorem 16.82); the image ideal of a preserving polynomial is generated by
  its Newton coefficients, or by its values on the box (Theorem 16.83);
  mutually inverse rational maps preserving `Λ^m` are polynomial automorphisms
  (Corollary 16.84); and a fixed Hahn workspace with value group `Γ` has a
  fresh exponent over `G` iff the convex subgroup generated by `G` is proper,
  in which case the certificates hold there (Proposition 16.86).
- **Theorem H (Theorem 17.1, from 11 and 13).** The Grothendieck ring of the
  ordinals under natural operations is not a quotient of `Oz` (every unital ring
  map from `Oz` to it has image `Z`), answering the quotient addendum of
  MathOverflow question 188430 (Jesse Elliott, 2014) negatively; the question's
  only answer (Eric Wofsey) concerns transcendence degree. 13 gives the same
  answer with the same two proofs (Remark 17.2).
- **Theorem I (Section 13, from 12, 14, 17 and 21).** For the set-sized core
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
  (Theorem 13.27). From 17 (Section 13.9): over `Oz`, `L(M)` with `rank M ≥ 2`
  (for example `(ω, √2 ω)`) has no presentation by sets, so `Oz` and `Oz[i]`
  are neither coherent nor finite-conductor even for intersections of two
  principal ideals (Theorem 13.29); `e_α ↦ ω^{−α}` embeds 11's lexicographic
  rings `R^11_{Γ,<κ}` in `Oz` (Lemma 13.30), over which every finite
  presentation of `L(M)` needs exactly `κ` relations (Theorem 13.31);
  `Tor_1(J, A/J') ≅ Tor_2(A/J, A/J') ≅ ker(M ⊗ N → K)`, of rank
  `rs − rank(MN)` (Theorem 13.34), the self-`Tor` rank lies between
  `r(r−1)/2` and `r(r−1)`, the top value detecting a field (Corollary 13.36,
  Proposition 13.37); the ideals `(ω, αω)` form `2^ℵ0` isomorphism classes,
  the `GL_2(D)` orbits of `α` (Theorem 13.38); `End(J)/Π` is an order in a
  field whose degree divides `rank M`, and every order occurs (Theorem 13.39,
  Corollary 13.40). From 21 (Section 13.10): `pd_{A_d} D = d + 1` for every
  `d ≥ 1`, one more than `fd D = d`, and `pd_{A_d} Π_d = d`; more generally the
  quotient by the open coordinate faces in a nonempty `U ⊆ [d]` has flat
  dimension `|U|` and projective dimension `|U| + 1`, with a countably generated
  free Koszul telescope resolution and `D^N/D^(N) ↪ Ext^{|U|+1}` (Theorems
  13.44–13.46, Corollary 13.47); over `A_d`, `pd L(M) = d + 1` and
  `pd A_d/J_g(M) = d + 2` for `rank M ≥ 2`, so `gl.dim A_d ≥ d + 2` when
  `K ≠ Frac D` (Theorem 13.48). Over `T_Q`, and over `Oz`, `Oz[i]` read in two
  universes: the lattice quotient has a flat DGA resolution of length two
  (Theorem 13.50); `Tor_1(A/J_g(M), A/J_h(N))` is `(𝖫 + Π)/X^e(MN + Π)`, where
  `𝖫` is `N`, `M` or `M ∩ N` as `g < h`, `g > h` or `g = h`: a window of scales
  below `e = min(g, h)` with boundary `k/MN`, while `Tor_2` is 17's scale-free
  kernel and `Tor_{≥3} = 0` (Theorem 13.51); for orders `𝔬_1, 𝔬_2` with fields
  `K_1, K_2` over `F = Frac D`, `rank Tor_2 = [K_1:F][K_2:F] − [K_1K_2:F]`, zero
  exactly under linear disjointness (Theorem 13.53); the self-`Tor` product is
  `xy = b(x) ⊗ b(y) − b(y) ⊗ b(x)`, and `Tor_2` is an extension of the symmetric
  relations `ker(Sym² M → M²)` by `Λ² M` (Theorem 13.54, Corollary 13.55); the
  data `(𝔬, 1, 𝒯(𝔬, 𝔬))` recover the multiplication of an order (discriminants
  8, 12, 5, −108 in the examples), while derived constant-term reduction gives
  only the square-zero `D ⊕ M[1]` (Theorems 13.56, 13.57).

## What the report does not claim

- All nineteen sources are AI-assisted, unrefereed drafts that call their main
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
  partly answered; the same holds for 17's countable model, while for its
  uncountable models the projective dimensions of `Π^11_κ` and `L(M)` and an
  upper bound on the weak global dimension stay open, Question 18.15);
  nonarithmetic class primes are treated conditionally and
  their existence is not claimed (Question 18.4); the idempotents and primes of
  `Oz/(1+ω^a)` are not classified.
- "Flat dimension one" is a property of rings whose exponents form a totally
  ordered cone (the five constructions, `T_Γ`, 14's `A_0`, the class ring in the
  two-universe reading); it is not asserted for arbitrary subrings of `Oz`, whose
  flat dimensions are unbounded (Remark 13.16). Nothing is claimed about the
  homological dimensions of the class ring `Oz`; the global and weak global
  dimensions of the cores are open (Question 18.12, partly answered: before
  21, `pd_{A_d} D` for `d ≥ 2` was known only to be `d` or `d + 1`). The
  finite-support cores are outside Theorem A: the augmentation detects their
  tails (Proposition 13.2).
- The support-threshold theorem is stated for `k ∈ {R, C}` as in 04 and 11,
  and no Gaussian analogue of 10's congruence criterion is given. 16's
  surjectivity rigidity is one-variable and for rational functions only.
- 17's relation counts and `Tor` groups concern the lattice ideals `J_g(M)` and
  constant matrices at one common scale, not arbitrary finitely generated
  ideals or several support levels; over the class ring `Hom` means scalar
  codes, and `Tor` and flat dimensions are taken over set-sized models only.
  The `D + M` mechanism and the relation module `M^{n−1}` are classical (Dobbs,
  Dobbs–Papick).
- 21's value `d + 1` concerns the set-sized cores `A_d`, not `pd Z` over `Oz`;
  it claims no exact global or weak global dimension, only the lower bounds
  `d + 2` and `d + 1`, and its resolutions control specified modules, not all
  ideals. Its class-ring statements are read under a two-universe convention.
  The vanishing of `Tor_2` is not `Tor`-independence (`Tor_1 ≠ 0`), and the
  decomposition of `Tor_1` is not an `A`-module splitting. Reconstruction needs
  the boundary embedding and the distinguished `1`; an abstract `Tor_2` or an
  abstract derived equivalence is not claimed to recover an order. The DGA is
  not claimed cofibrant or `E_∞`-formal. Modules killed by the tail have
  `Tor_{>0}(D, E) = 0` although `pd D = d + 1`.
- 18's dichotomy is one-variable (`XY` defeats any bound in several
  variables); its coefficient test is relative to exact coefficient operations;
  the Gaussian tests compared are not claimed minimal; nothing is said about
  `No` or the finite surreals.
- 19 does not determine `Idem(𝒩/Π𝒩)` (its size, atoms, triviality or whether
  it is a set) and gives no membership test for `𝒩`; set-sized images with
  zero divisors are classified only up to the factorization through `𝒩/Π𝒩`,
  which 19 does not assert to be a set; the detection theorem uses global
  choice; no Bézout property of `Oz` or `𝒩` is claimed, and the fibres mod `p`
  are neither reduced nor fields.
- 20 determines of `Idem(𝒩/Π𝒩)` that it is nontrivial, atomless and a proper
  class with free families of every set size, not its isomorphism type (it
  need not be free, complete or saturated; no infinite joins; no
  `𝖡_R ≅ 𝖡_R × 𝖡_R`). Its fixed-workspace results concern reduced fibres:
  radicality of `Π(G)𝒩(G)` and atomlessness of `Idem(𝖢(G))` in a fixed
  workspace are not asserted. Its descent is not a decision procedure, and
  its matrix corollary computes no projective or global dimension. Its
  specializations are maps of finite branch algebras, not evaluations of
  Laurent series; its support projection is not a ring map. The merge's
  decision of 03's candidates covers `H` polynomial in a fresh monomial
  (in particular `H` supported in one `Za`), not every `H ∈ Π`.
- 22's certificates are relative to exact field operations and exact
  membership, not algorithms, and choosing the fresh exponent is not an
  effective operation; neither its rational bound nor its Gaussian grid is
  claimed optimal, and the lower bound `(d+1)^m` concerns fixed point-value
  tests only. Its no-set-test theorem needs the full proper class and fails for
  set-sized rings; its workspace criterion says when its method applies, and
  its failure for Archimedean value groups is a failure of the method, not an
  impossibility. It classifies no arbitrary, algebraic or semialgebraic maps;
  its birational corollary assumes a rational inverse and makes no Jacobian
  claim; image ideals are not assumed principal; its tensor isomorphisms are
  read through finite sums or in a containing universe. The D-ring collapse
  and the binomial basis are credited, not claimed, and its novelty list is
  incomplete (see below).
- Section 18.2 keeps every limitation stated by a source, numbered per source:
  03 (19 items), 04 (14), 06 (14), 07 (13), 08 (13), 09 (12), 10 (12), 11 (12),
  12 (12), 13 (10), 14 (12), 15 (11), 16 (8), 17 (12), 18 (10), 19 (12),
  20 (14), 21 (17), 22 (18), and 15 for the merge (260 in all). 12's item (3) carries a
  note that 21 determines the projective dimensions. 03's item (10) carries a note that
  19 classifies the domain images, 03's item (8) a note that the descent now
  holds (Corollary 15.59), and 19's items (1), (2), (7) and (9) notes on what
  20 adds. Section 18.3 lists twenty questions, merging
  duplicates across sources, with their status: one answered (Question 18.2),
  one answered only for specific examples and constructions (Question 18.1,
  which also absorbs 13's and 15's cardinal-bound questions), six partly
  answered (Question 18.3; Question 18.11, whose clause on set-sized images of
  `𝒩` is answered for domain images by 19, whose descent clause is answered by
  Corollary 15.59 and whose fixed-subgroup clause is answered for witnesses at
  larger scales by 20; Question 18.12, whose first clause, `pd_{A_d} D`, is
  answered by 21; Question 18.14, whose part (a) is partly addressed by 18's
  tests and 22's lifting theorem and whose part (c) 22 answers for its
  single-scale rational certificates, Proposition 16.86; Question 18.15,
  answered for `κ = ℵ0`, with part (c) partly
  addressed by 21's framed reconstruction; Question 18.17, whose part (a) 20
  answers and whose part (b) it answers for reduced fibres), one settled for
  cardinal support bounds only (Question 18.8), and eleven open (Question 18.18
  is 20's question on the isomorphism type of the Boolean algebra; Questions
  18.19 and 18.20 are 22's, the second with its part (d) partly addressed by
  16's general-`D` results and Remark 16.88; Question 18.16(c) is not
  addressed by 22, whose lifting theorem concerns ordinary test points only).
  22's question on sharp Gaussian constant tests is merged into Question
  18.14(a). 19's membership
  question is merged into Question 18.11, 20's questions on fixed-workspace
  radicality and effective certificates into Question 18.17(b), (c), and 21's
  three questions (exact global and weak global dimensions of the cores,
  several support levels, how much framing is needed) into Questions 18.12,
  18.13 and 18.15(c).
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
- **Third batch.** 17 (pin `71e9606`) proposes as additions the constant-matrix
  descent criterion, the coefficient-lattice Hom and isomorphism
  classification and the multiplication-kernel computation of `Tor`, with
  consequences for orders and ideal powers. None was in the repository at its
  pin, but the collection now prints the descent criterion, the Hom
  classification, the tensor kernel and the power growth as 14's and the
  intersection `(ω^γ) ∩ (αω^γ) = ω^γ Π` as 12's (Theorems 13.9, 13.18, 13.23,
  13.24, 13.28); 17 is credited there as an independent second source, and its
  "49 main texts" in the catalogue is a snapshot. 18 (pin `befe739`) reports
  that repository searches for integer-valued polynomial and rational
  terminology found nothing; at its pin source 10 was present only as
  `code/10-omnific-arithmetic-checks.py`, and the collection now prints 10's and
  16's polynomial arithmetic (Section 16). 19 (pin `befe739`) reports that the
  catalogue lists nine omnific manuscripts awaiting integration; true at its
  pin, since written. 18 and 19 saw only 06's text of this report, not 03's
  normalization, 10's polynomials or batch 25.
- **Fourth batch.** 20 (pin `4cdeaec`, which also precedes the writing of this
  report) saw only 06's text here and cites this report under 06's title and
  date; it read 19 as a saved draft and does not assert that 19 was in the
  repository (it was placed later, in `f4c9504`, and is now Section 15.8). Its
  appendix and `20-boolean-branching-SOURCE_AUDIT.md` say that the catalogue
  separates the main reports from companions awaiting integration; true at its
  pin. 20 proposes support-local descent and the dominant-scale branch
  construction as new; the identification of a fresh scale with Laurent
  blocks over the old Hahn field is 16's (Theorem 16.31, Corollary 16.32),
  not in the repository at 20's pin, and is credited (Lemma 15.62). 20's
  own statements are otherwise accurate; no error was found.
- **Fifth batch.** 21 (pin `9693b28`, after the writing of the second merge
  and before that of the third, `aae58bb`) quotes Proposition 13.12(iii) as
  `d ≤ pd_{A_d} D ≤ d + 1` with the next paragraph leaving the value
  undetermined, and (iv) as bounds for lattice modules; both were accurate at
  its pin and are now settled by 21 itself (Corollary 13.47, Theorem 13.48),
  with pointers added beside the bounds, and the stale sentences (the
  paragraph after Proposition 13.12, Remark 13.16, Questions 18.3 and 18.12,
  the merge's non-claim (6)) are updated. 21 presents a uniform calculation of
  all `Tor` groups of two lattice quotients, the self-`Tor` ranks, second `Tor`
  as a linear-disjointness test and the `Tor` groups against constant-term
  modules as its contributions, and calls the additive second-`Tor` formula a
  dimension-shift consequence of the report's tensor calculation. At its pin
  the report did not contain 17's Section 13.9 (written in `aae58bb`); the
  second-`Tor` identification with its rank, the self-`Tor` range, the pair
  `Z[√2]`, `Z[√3]` and the `Tor` groups against modules killed by the tail are
  17's (Theorem 13.34, Corollary 13.36, Theorem 13.42), and 21 is credited
  there as a further source. The "quadratic self-`Tor` example" that 21 finds in
  the report is 12's `Tor_2(A/H, A/H) ≅ D ⊕ D` (Theorem 13.11). No error was
  found in 21's proofs.
- **Sixth batch.** 22 (pin `bcac55a`, which contains the writing of the
  third merge, `aae58bb`, but not of the fourth or fifth) read the repository
  and catalogue READMEs, the openings of the Diophantine and holonomic-rigidity
  reports and the Diophantine report's fractions audit, not this report. Its
  introduction (Section 1.4) and `22-finite-tests-SOURCE_AUDIT.md` (§4) say that
  the precise statements of its proposed package were not located in the
  material inspected. *Correction:* at its pin this report already contained
  the Laurent-block detector at one fresh scale (Theorems 16.31, 16.33),
  workspace-uniform rational certificates with `d + 2` values in one variable
  and fresh probes in several (Corollary 16.50), a numerator-degree-0,
  denominator-degree-1 function with no pole on `Oz` or `Oz[i]` deceiving any
  set (Theorem 16.51; 16's `ω^β/(X − 1/2)` is `2ω^β/(2X − 1)`, with
  coefficients in `Oz`), the empty-or-proper-class alternative in one variable
  (Theorem 16.52), and Gaussian tests with a one-variable lifting of ordinary
  test sets (Propositions 16.47, 16.64). So 22's novelty list is incomplete;
  what is new in it is listed in the table above. Its bibliographic statements
  and proofs contain no error found in this merge; it repeats 10's and 16's
  results without credit because it did not read this report, and they are
  credited (Section 16.10).
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
  in rank one (Proposition 13.12; 21 has since determined them for every `d`,
  Corollary 13.47, Theorem 13.48). 21 repeats 17's `Tor` results without credit
  (it could not see them); they are credited (Section 13.10). 14 credits the sibling report's example
  `[1:√2]` but not its rationality theorem for primitive directions, of which 14's
  unimodular-direction criterion is the Gaussian and principal-ideal extension.
  17 assumes `κ` uncountable for its relation counts, but its proofs use only
  regularity, so `κ = ℵ0` is included (Remark 13.32). 19 reproves four results
  of 03 without credit (it could not see them); they are credited
  (Section 15.8). 18's question on minimal tests with omnific nodes is settled
  for `Oz` by 16's optimality theorem and stays open for `Oz[i]`
  (Question 18.16). 17 cites Dobbs (1975) for the relation module `M^{n−1}`;
  that page-level attribution was not verified for this merge.
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
  files, and the original script names used by the Makefiles and build scripts
  (for the third batch: `18-polynomial-rigidity-build.sh` expects `article.tex`,
  and `19-normalization-fibres-build.sh` expects `article.tex`, `checks.py` and
  `checks.txt`; the build records `17-relations-arithmetic-build_report.json`
  and `18-polynomial-rigidity-build_report.json` describe PDFs that are not
  shipped; for the fourth batch: `20-boolean-branching-Makefile` expects
  `article.tex` and `verify.py`, `20-boolean-branching-BUILD_REPORT.json`
  describes 20's own 24-page PDF, and the audit files name
  `verification_results.json` (here
  `data/20-boolean-branching-verification_results.json`) and 20's saved copies
  of 19 (`article(20260923-180548).tex` and its PDF), which are neither shipped
  nor in the repository; for the fifth batch: `21-derived-arithmetic-build.sh`
  and `21-derived-arithmetic-build.ps1` run pdfLaTeX on `article.tex` in their
  own directory, which is not shipped there, and
  `21-derived-arithmetic-provenance.json` describes 21's own 25-page PDF and
  build; 21's delivered `SHA256SUMS.txt` was verified at placement and
  dropped; for the sixth batch: `22-finite-tests-build.sh` and
  `22-finite-tests-build.ps1` run pdfLaTeX three times on `article.tex` in
  their own directory, which is not shipped there;
  `22-finite-tests-SOURCE_AUDIT.md` names 22's own `verify.py`, verification
  reports and 24-page PDF under their delivery names (here
  `code/22-finite-tests-verify.py` and
  `data/22-finite-tests-verification_report.{json,txt}`; the PDF is not
  shipped); 22's delivered `MANIFEST.sha256` was verified at placement and
  dropped).

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
- [`omnific-groups-and-lattices`](../omnific-groups-and-lattices/) (batch 26,
  written concurrently) proves that for `n ≥ 3` the purely infinite congruence
  kernel of `E_n(Oz)` and of `E_n(Oz[i])` has no nontrivial homomorphism to a
  set-sized group, a group-level strengthening of Theorem 5.1 (pointer at
  Theorem 5.1), built on this report's collision and division lemmas.
- [`omnific-preserving-automorphisms`](../omnific-preserving-automorphisms/)
  (batch 26) holds the other batch-26 omnific items; its algebraic-parameter
  part identifies its commuting derivations `D_b` with Proposition 7.6 here
  (`osq:prop:classder`).
- [`discrete-initial-subgroups-and-omnific-normalization`](../discrete-initial-subgroups-and-omnific-normalization/)
  (batch 28) concerns discretely ordered initial subgroups of `No` in the
  sense of Ehrlich–Kaplan; its "normalization" is not the integral closure
  `𝒩` of Section 15, and its subject is unrelated to Sections 15.8 and 15.9.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 177 pages with no errors, warnings, undefined references,
multiply defined labels, duplicate destinations or overfull or underfull boxes
(the committed text before the sixth merge gave 164 pages, before the fifth
153, before the fourth 140, and before the third 117, also clean). Every
statement, section and equation number of the text before the sixth merge is
unchanged (all 521 earlier labels compared in the `.aux` files); the sixth
merge's statements are Lemma 16.68 to Remark 16.88 and equations (16.25) to
(16.30) in Section 16.10, and Questions 18.19 and 18.20. The finite-check
table of Section 19.1 became a `longtable` in the sixth merge, because the row
for 22 made it taller than a page; this changes only its layout.
Build in a copy of the directory and do not commit the auxiliary files.

The nineteen check programs were rerun for the six merges on copies (Python
3.14.4, SymPy 1.14.0); all pass and reproduce the recorded outputs up to line
endings, the recorded Python version and (18) the recorded time stamp. For
22 the rerun passed all 1,776 assertions in the same 22 categories, and its two
rewritten reports differ from `data/22-finite-tests-verification_report.*` only
in the Python version (3.14.4 for 3.13.5) and in CRLF line endings on Windows;
its printed output equals the text report.
**Several write files by default**:
04 always writes `verification.json` next to the script; 06, 09 and 14 do so
unless given `--output` (14 writes `verification.json`); 07 writes
`verification_results.json` and 15 writes `finite_checks.json` in the working
directory unless given `--output` (15's own README runs it with
`--output finite_checks.json`, which overwrites its recorded result); 12 always
writes `audit_results.json` next to the script; 16 writes
`verification_results.txt` next to the script unless given `--output`; 17
writes `../data/verification.json` relative to the script (here an unprefixed
`data/verification.json` in this directory) unless given `--output`; 18 always
writes `verification_results.json` next to the script; 19 prints to standard
output only, but its `build.sh` would overwrite `checks.txt`; 20 always writes
`verification_results.json` next to the script (and prints it); 21 writes
`verification_results.json` next to the script unless given `--output` (here
that would be a new, unshipped `code/verification_results.json`); 22 always
writes `verification_report.json` and `verification_report.txt` next to the
script and prints the text (here that would be two new, unshipped files in
`code/`; it takes no output option). Run them with
an explicit output in a scratch directory, and run 04, 12, 18, 20, 21 and 22 on a
copy:

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
python code/17-relations-arithmetic-verify.py --output "$T/17.json"           # 347 checks
cp code/18-polynomial-rigidity-verify.py "$T/" && python "$T/18-polynomial-rigidity-verify.py" > "$T/18.out"   # 499 assertions; writes $T/verification_results.json
python code/19-normalization-fibres-checks.py > "$T/19.txt"                   # 253 primary checks; = data/19-...
cp code/20-boolean-branching-verify.py "$T/" && python "$T/20-boolean-branching-verify.py" > "$T/20.out"   # 6,674 assertions; writes $T/verification_results.json
cp code/21-derived-arithmetic-verify.py "$T/" && python "$T/21-derived-arithmetic-verify.py" --output "$T/21.json"   # 1,008 + 600 checks; stdlib; = data/21-... as JSON
cp code/22-finite-tests-verify.py "$T/" && python "$T/22-finite-tests-verify.py" > "$T/22.out"   # 1,776 assertions, seed 23092026; writes $T/verification_report.{json,txt}
```

12 and 19 require SymPy but ship no requirements file (19's README names
SymPy 1.14.0); 14, 16, 17, 18, 20 and 22 ship `sympy==1.14.0` (20's and 22's records were made
with Python 3.13.5; the reruns under 3.14.4 differ only in that field and in line endings); 21 needs
only the standard library, and its rerun equals the recorded JSON in content
(on Windows the rewritten file has CRLF line endings). Run 12 and 21 without
Python's `-O` option (their checks are assertions). The shipped `04-…-Makefile`, `06-…-Makefile`, `10-…-Makefile`,
`09-set-shadows-build.sh`, `11-set-sized-algebra-build.sh`,
`12-homological-dimension-build.sh`, `14-arithmetic-tensors-build.py`,
`18-polynomial-rigidity-build.sh`, `19-normalization-fibres-build.sh`,
`20-boolean-branching-Makefile`, `21-derived-arithmetic-build.sh`,
`21-derived-arithmetic-build.ps1`, `22-finite-tests-build.sh` and
`22-finite-tests-build.ps1` use the
original package file names (`verify.py`, `article.tex`,
`omnific_set_shadows.tex`, `omnific_homological_dimension.tex`,
`code/check_finite_identities.py`, …) and do not run as shipped; they are kept
as provenance. For the second merge an independent exact computation, not
shipped, rechecked Theorem 13.7 in 1,626 cases (every proper subset `F`
included) and Corollary 13.23 for `d ≤ 8`, `n ≤ 12`. For the third merge,
independent exact computations, not shipped, rechecked 17's Pell matrix,
multiplication kernels, self-`Tor` endpoints (`r ≤ 5`) and five `GL_2(Z)`
cases, 18's composition obstruction (27 random cases) and `η` formula, 19's
idempotent identities, Catalan expansion and 36 random cases of the lifting
bound, and the sizes of the Gaussian certificates of
Proposition 16.64 for `n ≤ 3`, `d ≤ 5`. For the fourth merge, an independent
exact computation, not shipped, rechecked in 18 checks 20's certificate
(15.24), the values of the specializations, the many-branch identity of
Theorem 15.70, the simple zeros behind the square classes and the identities
behind Proposition 15.68. For the fifth merge, an independent exact
computation, not shipped, rechecked in 78 checks the converse formula of
Theorem 13.46 in 12 cases, the exponent identities behind it, the Koszul
transition identity, the `Tor_2` and `Ind_2` ranks and discriminants of the
four orders, and the product rank for `Q(√2), Q(√3)`; neither it nor 21's
program proves the infinite `Ext` nonvanishing, which rests on the written
proof of Theorem 13.46. For the sixth merge, an independent exact computation,
not shipped, rechecked in 101 checks the resultant and partial fractions of
Example 16.87, the counts after Theorem 16.70 and the comparison of
Remark 16.71 for `m ≤ 4`, `d ≤ 5`, the bound (16.26) in twelve random
trivariate cases, the inverse shears of Example 16.85, the two Gaussian
denominators and the coefficients of Example 16.74; neither it nor 22's
program verifies an infinite support, a cut above an arbitrary set or a
proper-class statement. `19-normalization-fibres-build.sh`
runs `python3 checks.py | tee checks.txt`, which would overwrite the recorded
result; do not run it in this directory.
