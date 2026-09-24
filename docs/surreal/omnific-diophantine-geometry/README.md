# Omnific Integers and Omnific–Diophantine Geometry

**Retractions, rigidity, definability, and infinite families**
Merged research report, from fifteen manuscripts written independently: three
dated 22 September 2026 (batch items 01, 02 and 05 of the batch placed in
`be06fc8`), two dated 23 September 2026 (batch items 01 and 07 of the batch
placed in `cf350b1`, numbered 06 and 07 here), two more dated 23 September
2026 (batch items 01 and 02 of the batch placed in `a4dcb91`, numbered 08 and
09 here), and five more dated 23 September 2026 (batch items 02, 03, 04, 07 and
08 of the batch placed in `c6359e4`, tagged C10–C14 here after their file
prefixes `10-` to `14-`), one more dated 23 September 2026 (batch item 02 of the
batch placed in `66d7e55`, tagged C15 after its file prefix `15-`), and one more dated
23 September 2026 (batch-31 manuscript 04, placed in `9d28e28`, tagged C16 after its file
prefix `16-`), and one more dated 23 September 2026 (batch-33 manuscript 07, placed in
`aa9c891`, tagged C17 after its file prefix `17-`). Prepared for Vladimir Reshetnikov.

```
article.tex                        the report, standalone LaTeX with an internal bibliography
article.pdf                        the compiled report, 225 pages
README.md                          this guide
RECONCILIATION.md                  the source comparisons and precise proof-review scope
02-diophantine-PROVENANCE.md       source 02's provenance and verification-boundary note, as delivered
05-diophantine-rigidity-BUILD.md   source 05's build and check instructions, as delivered
06-definability-reconstruction-SOURCE_AUDIT.md   source 06's source and novelty audit, as delivered
08-fractions-SOURCE_AUDIT.md       source 08's source and novelty audit, as delivered
10-curve-rigidity-SOURCE_AUDIT.md  source C10's source and novelty audit, as delivered
11-curve-abelian-rigidity-SOURCE_AUDIT.md   source C11's source and novelty audit, as delivered
11-curve-abelian-rigidity-BUILD_AUDIT.md    source C11's build record for its own article
12-curve-logarithmic-SOURCE_AUDIT.md        source C12's source and claim audit (see below)
13-differential-rigidity-SOURCE_AND_PROOF_AUDIT.md   source C13's source and proof audit, as delivered
14-hahn-differential-rigidity-SOURCE_AUDIT.md        source C14's source, novelty and proof audit, as delivered
15-logarithmic-rigidity-PROOF_AUDIT.md      source C15's author-side proof audit, as delivered
16-singular-curves-SOURCE_AUDIT.md          source C16's source, proof and artifact audit, as delivered
17-discriminant-rigidity-SOURCE_AUDIT.md    source C17's repository pin and novelty audit, as delivered
17-discriminant-rigidity-PROOF_AUDIT.md     source C17's author-side proof and hypothesis audit, as delivered
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
  10-curve-rigidity-verify.py               source C10 checks (writes JSON; see below)
  10-curve-rigidity-Makefile                source C10's build and check targets (delivered
                                            names article.tex, verify.py; not this report)
  11-curve-abelian-rigidity-verify.py       source C11 checks (standard library; writes JSON)
  11-curve-abelian-rigidity-Makefile        source C11's build and check targets (delivered names)
  12-curve-logarithmic-verification.py      source C12 checks (writes JSON; see below)
  12-curve-logarithmic-build.sh, .ps1       source C12's build scripts (they run verification.py
                                            and compile article.tex in their own directory)
  13-differential-rigidity-verify_certificates.py   source C13 checks (prints; see below)
  13-differential-rigidity-build.sh         source C13's build script (compiles its own
                                            omnific_differential_rigidity.tex; not this report)
  14-hahn-differential-rigidity-verify.py   source C14 checks (always writes JSON; see below)
  14-hahn-differential-rigidity-Makefile    source C14's build and check targets (delivered names)
  15-logarithmic-rigidity-verify.py         source C15 checks (prints; writes JSON only to --output)
  15-logarithmic-rigidity-build.sh, .ps1    source C15's build scripts (they compile article.tex in
                                            their own directory, code/; not this report)
  16-singular-curves-verify.py              source C16 checks (prints; writes JSON only to --output)
  16-singular-curves-build.sh               source C16's build script (compiles article.tex in its
                                            own directory, code/; not this report)
  17-discriminant-rigidity-verify.py        source C17 checks (prints; writes JSON to --output,
                                            default verification.json in the working directory)
  17-discriminant-rigidity-build.sh         source C17's build script (delivered layout: builds
                                            article.pdf and reruns verify.py in place; see below)
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
  10-curve-rigidity-verification.json                source C10's recorded run
  10-curve-rigidity-BUILD_AUDIT.json                 source C10's build record for its own article
  11-curve-abelian-rigidity-verification.json        source C11's recorded run
  12-curve-logarithmic-verification_report.json      source C12's recorded run
  13-differential-rigidity-verification_report.txt   source C13's recorded run
  14-hahn-differential-rigidity-verification.json    source C14's recorded run
  14-hahn-differential-rigidity-BUILD_AUDIT.json     source C14's build record for its own article
  15-logarithmic-rigidity-verification.json          source C15's recorded run
  15-logarithmic-rigidity-build_report.json          source C15's build record for its own article
  16-singular-curves-verification.json               source C16's recorded run
  16-singular-curves-build_report.json               source C16's build record for its own article
  17-discriminant-rigidity-verification.json         source C17's recorded run
  17-discriminant-rigidity-BUILD_REPORT.json         source C17's build record for its own article
  01-, 02-, 05-, 06-, 08-, 09-, 10-, 12-, 13-, 14-, 15-, 16-, 17-...-requirements.txt   each pins sympy==1.14.0
```

The shipped files of sources C15 (placed in `66d7e55`), C16 (placed in `9d28e28`) and C17
(placed in `aa9c891`) are byte-identical to the deliveries. The shipped files of sources C10–C14 are byte-identical to the deliveries,
except that `12-curve-logarithmic-SOURCE_AUDIT.md` differs from the delivery in
one Markdown hard break normalized for whitespace checks (`a6c68ac`); its
content is unchanged.

Every label in `article.tex` carries the prefix `odg:` (553 labels, counting
both `\label{…}` and `\label[type]{…}`): the 150 labels of the three-source
assembly `bbdd536`, none renamed or removed; nine aliases kept by the
elementary review merged from upstream; 69 labels added by the batch-25
integration; 82 labels added by the batch-27 integration; 95 labels added by
the batch-28 integration; 11 labels added by the batch-29 integration; 55 labels added
by the batch-31 integration; and 82 labels added by the batch-33 integration. The material of
sources 06 and 07 carries the sub-prefix `odg:def:` (63 labels), the fiber and
norm results printed from the sibling report's manuscript 13 carry `odg:dec:`
(6 labels), the material of sources 08 and 09 carries `odg:frac:` (82
labels), the material of sources C10–C14 carries `odg:cr:` (95 labels), and the new
material of source C15 carries `odg:log:` (11 labels), the material of source C16
carries `odg:sg:` (55 labels), and the material of source C17 carries `odg:disc:` (82
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
now Sections 14 and 19, including real-coefficient specialization and the finite
factorization proof of the two-term root obstruction. These reviews exclude the batch-25
material (Sections 11–13, the Section 6 results of sources 07 and 13, and
Remark 10.5). A review of Section 14 (`25e372c`, merged in `ef806c0`) expanded
its proofs. A subsequent pass reviews Section 11: leading degrees, the
quadratic ideal predicate, Pell divisibility, intersectivity and the
order-free integer-defining system. It adds boundary examples for intermediate
rings and expands the finite congruence arguments. A further pass reviews
Section 12: the detector, ideal test, constant-term graph, homomorphisms and
number-field extension. Its root hypothesis already gives an existential
ideal and graph. Section 13 now also has a proof review of reconstruction,
automorphisms and logical consequences. It extends coefficient reconstruction
to the number-field ideal predicates and the c.e.-set classification to
all characteristic-zero coefficient fields using finite equation systems.
The added Gaussian fibers and étale norm arguments in Section 6 now have
a proof review against sources 07 and 13. Basis parameters are unique,
and nonzero kernels give proper-class fibers when an ordinary point exists.
The norm proof spells out separable splitting and coefficient extension;
it extends to abstract Hahn rings in every characteristic, with concrete
zero-level, nilpotent and inseparable counterexamples to weaker hypotheses.
Source 07's quartic in Section 10 is now reviewed too: the proof uses the
ambient support ring before the integer intersection, and constructs
ordinary witnesses for every allowed intermediate ring. The later curve
pointers still need review.
Further passes review all of Section 15: denominator ideals, the
multiplier theorem, rational-function and curve applications, congruence
orbits and density. The focusing formula now handles the zero parameter
and the projective topology is explicit. The fixed rational-function field
is discrete in the induced surreal topology, unlike its degree topology.
The localization review corrects the claim that the two residues agree
only on `ℚ`: their common kernel contains nonzero infinitesimals. It
expands the scale-defect and Tor proofs, distinguishes finite real
dimension from infinite module length, and checks fixed workspaces and
Gaussian normalization.
That pass left the batch-27 additions to Section 20, Section 21.3 and Questions 21.12–21.16 unreviewed; the later scope pass below checks their maintained summaries. No review
covers the full batch-28 material. A further elementary pass reviews
Sections 16.2–16.3 (Lemmas 16.1–16.3 and Corollary 16.4): rings, Euler
derivations and their joint constants. It corrects the trivial-group
valuation-ring exception and distinguishes an image inclusion from a
proper inclusion. A subsequent pass reviews Section 16.4: the squarefree
certificate, degree obstruction, cubic differential and Weierstrass
applications, including singular families. It supplies the missing
positive-integer hypothesis for differential division, qualifies division
by the discriminant and corrects the factor of two in the contraction
comparison. The next pass reviews Section 16.5 through inheritance,
completing the maintained Section 16 proof chain. It explains the tangent
functional, two-ring contraction, symmetric evaluation and constant descent;
the symmetric clause now explicitly requires positive degree. The proof
also yields the proper singular case with globally generated Kähler
differentials, and tangent detection is shown equivalent to tautological
semiampleness for smooth projective schemes. Imported geometric foundations
are identified separately. The next pass reviews Sections 17.1–17.2: positive
genus, the smooth affine classification, logarithmic differentials and all smooth
curves. It distinguishes the real circle's two conjugate punctures from a form
of the affine line, supplies descent across arbitrary field extensions and
explains why the logarithmic valuation centre is a closed boundary point.
Section 17.3 now also has a proof review of exact arithmetic fibers, integer
polynomial arcs, the finite congruence criterion and separated-model descent.
It makes equation descent through injective coefficient maps explicit, allows
nonflat integral models, and distinguishes set-sized workspace fibers from
proper-class fibers. Clearing denominators preserves the entire purely infinite
fiber; finite-support witnesses can be chosen with integer coefficients.
Section 17.4 now has a proof review of unimodular coordinates and invertible
coordinate ideals, including their finite workspace witnesses. It corrects the
comparison with rational curves: rational specialization does not imply a
rational projective point. The Gaussian unit factors and the elliptic
noninvertible-ideal example are explicit. The next review covers Section 17.5
and Sections 17.6.1–17.6.5, through Corollary 17.37: normalization, conductor
certificates, the discrete boundary place, the singular-curve criterion and
its structural consequences. It distinguishes normality in the fraction field
from integral closure in a larger Hahn field, and does not infer a failed
curve lift from a non-normality example. The reducible-curve theorem now
explicitly requires `Γ ≠ 0`. The application review now covers Sections 17.6.6–17.6.8: it restores the
irreducibility hypothesis in the superelliptic theorem, expands ramification
and the seventh-order certificate, and checks arithmetic families and the
Gaussian existence dichotomy. A real isolated node illustrates why a real
normalization preimage is required. The next pass checks the closing singular-curve
scope notes and reviews Sections 18.1–18.4: group rigidity, reduced coefficient
algebras, the dual-number defect and the characteristic/discrete-order
counterexamples. The logarithmic pass now reviews Sections 18.5–18.6,
including all six standard results, the abstract interface and arithmetic
descent. It corrects the ring-map explanation and supplies the local
normal-crossings construction. The scope pass checks Section 20 and
Sections 21.1–21.6 against the maintained statements and Lean ledger. It
corrects the smooth-fiber and product-with-affine-line summaries, gives a
fixed-workspace counterexample to idempotence, and distinguishes vanishing
contractions from vanishing forms. A subsequent comparison pass checks the
geometric pointers in Sections 1, 6, 7 and 14 and the cited statement scopes
in Section 21.7. It restores the nonzero exponent-group and geometric
integrality hypotheses, distinguishes an affine-line real fiber from an
affine-line integral model, and corrects the stale account of the groups
report. Imported proofs and complete source reconciliation remain separate.
The elementary pass also covers the corresponding claims credited to
source C15. Beyond the targeted logarithmic review, remaining batch-29
source reconciliation includes the parallel proofs, credits and remarks
added for source C15 in Sections 16–18, and its additions to Section 1 and the appendices; Sections 20–21.6 now
have the maintained-text scope check described above. Section 18.6 was appended at the end of Section 18, so no section,
statement or equation number changed. Full comparison with the later batch-31 source C16 still needs its
remaining credits in Sections 1, 16 and 17 and the appendix additions.
The maintained Section 20 and Section 21.1–21.6 status notes, including
Questions 21.23–21.30, are covered by the scope pass; their full parallel-source
reconciliation is not claimed. Section 17.6 was appended at the
end of Section 17, after Section 17.5, so again no section, statement or equation number
changed. Apart from the positive-degree hypothesis restored in its opening summary
and the statement-scope check of its sibling-translation comparison, the
batch-33 material of source C17 is unreviewed: Section 19.4, its pointers and
credits in Sections 1, 2, 5, 6, 9, 16 and 20, the status notes in Sections 18.5 and 21,
Questions 21.31–21.40 and the appendix additions. Section 19.4 was appended at the end of
Section 19, after Section 19.3, and its questions after Question 21.30, so again no section,
statement or equation number changed. Inserting Section 15
moved the former Sections 15–17 to 16–18, and inserting Sections 16–18 moved them
on to 19–21; statement numbers in Sections 1–15 are unchanged. See
[RECONCILIATION.md](RECONCILIATION.md) for the elementary claim correspondence,
these proof reviews and the remaining review boundary.

The article has 244 standard results (87 theorems, 44 propositions, 52 lemmas,
61 corollaries), of which 39 are in Section 15, 74 in Sections 16–18 (6 of them in
Section 18.6 and 17 in Section 17.6) and 27 in Section 19.4. The
[ledger](../../FORMALIZATION.md) indexes the standard results of the
report by `odg:` label, including all six results of Section 18.6 and all 17
results of Section 17.6; it does not yet index the 27 results of Section 19.4. Indexing
does not extend the proof-review scope.
The ring and constant-term package `odg:prop:ring` is **Proved**, using
[actual omnific integers](../../../Surreal/Foundations/OmnificIntegers.lean)
and the [complex support ring](../../../Surreal/Surcomplex/NonnegativeSupportRing.lean).
The degree lemma `odg:lem:degree`, unit/finite-element proposition
`odg:prop:units` and exact floor theorem `odg:thm:floor` are also **Proved**.
The [floor construction](../../../Surreal/Foundations/OmnificFloor.lean)
handles the negative infinitesimal correction at an integer coefficient
and proves existence and uniqueness of the omnific integer part.
The [polynomial-root package](../../../Surreal/Foundations/OmnificPolynomialRoots.lean)
also proves `odg:prop:univariate` and transcendence over `ℝ` of every
infinite omnific integer. The [ordinary residue package](../../../Surreal/Foundations/OmnificResidues.lean)
proves `odg:thm:finitequotients`, and
[integer divisor rigidity](../../../Surreal/Foundations/OmnificIntegerDivisors.lean)
proves `odg:prop:finitedivisors`.
The [ordinary arithmetic package](../../../Surreal/Foundations/OmnificOrdinaryArithmetic.lean)
proves the primality, mixed-gcd and Chinese remainder corollary
`odg:cor:mixedgcd`. The [finite quotient package](../../../Surreal/Foundations/OmnificFiniteQuotients.lean)
proves `odg:cor:charideals`, including unique ordinary moduli and
factorization of every finite-target homomorphism through the constant term.
The [constant rigidity package](../../../Surreal/Foundations/OmnificConstantRigidity.lean)
proves `odg:prop:canonicalct`, its noninjective-endomorphism example,
and non-residual-finiteness using an explicit nonzero monomial.
The [p-adic completion](../../../Surreal/Foundations/OmnificPadicCompletion.lean)
is ring-isomorphic to `ℤ_p`; its canonical map is integer constant
extraction followed by the ordinary embedding and has kernel `Π`.
Other results remain **Pending** unless individually mapped in the ledger.

## Fifteen sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **01** | *Omnific Integers and Omnific–Diophantine Geometry* | `2cb9c02` | The base text and structure; the exhaustive quadratic-level dichotomy including degenerate forms (Theorem 8.1); the five-auxiliary three-square guard (Theorem 10.3); rational directions (Theorem 14.5); no real point at infinity (Theorem 9.6); symmetric matrices (Corollary 9.5); the elementary uniqueness of `ct` (Proposition 3.5). Files prefixed `01-diophantine-geometry-`. |
| **02** | *Omnific Integers and Diophantine Geometry* | `2cb9c02` | Exact decomposable fibers (Theorem 6.2(a)); bounded semialgebraic rigidity (Theorem 9.2); decidable homogeneous existence with sign conditions (Theorem 14.2(b)); the square-discriminant criterion (Theorem 19.1); the general pair without a gcd (Theorem 4.10); the explicit Lorentz matrix and the unipotent subgroup (Corollary 8.4); nilpotent tests and mixed gcds. Files prefixed `02-diophantine-`. |
| **05** | *Omnific Integers and Diophantine Rigidity* | `2cb9c02` | Binary rigidity over `C` (Theorem 6.7); Euler derivations (Section 7); separated powers (Theorem 7.4) and unimodular Fermat (Theorem 7.9); the four-square definition of `Z` (Theorem 10.4); a failed existential induction (Theorem 10.10); failed lifting (Proposition 19.4, Example 19.5); finite-support specialization (Theorem 14.7). Also the universal set-sized quotient theorem, which is **printed in the sibling report** and only quoted here (Cited theorem 3.6). Files prefixed `05-diophantine-rigidity-`. |
| **06** | *Definable Arithmetic and Coefficient Reconstruction in Omnific Integer Rings* | `71e9606` | Base of Sections 11–13: the one-witness Diophantine definition of `Π` (Theorem 11.2), the Diophantine graph of `ct` (Theorem 12.8), all homomorphisms preserve `ct` (Theorem 12.12), the multiplier identity (Theorem 13.2), reconstruction of `R`, `No`, order and standard part from the pure ring `Oz` (Theorem 13.4), automorphisms fix `R` (Theorem 13.6), the phase twist and the real–Gaussian asymmetry (Theorem 13.10), c.e. sets (Theorem 13.11); its quintic is Remark 11.10. Files prefixed `06-definability-reconstruction-`. |
| **07** | *Defining Arithmetic Inside Omnific Integers* | `71e9606` | The order-free system in intermediate rings (Theorem 11.9, with 06); the augmentation root detector (Theorem 12.1) and the constant-term detector (Theorem 12.2); support bounds (Proposition 12.3); the ideal test (Theorem 12.6); number-field coefficient rings (Theorem 12.14); norm rigidity over any base field (in Theorem 6.15); recursive saturation (Theorem 13.15); its quartic is Remark 10.5. Files prefixed `07-defining-arithmetic-`. |
| **08** | *Fractions of Omnific Integers: Rational Specialization, Lowest Terms, Denominator Ideals, and Scale Extensions* | `9a385d3` | Base of Section 15: real constants (Theorem 15.7); the multiplier theorem for any retraction and any number of coordinates (Theorem 15.11); the classification of all representations of rational-function tuples at any `0 ≠ t ∈ Π` (Theorem 15.18, Corollaries 15.19–15.21); no lcm (Example 15.27); rational curves (Corollary 15.28); the localization at `Π` and independent residues (Proposition 15.40, Theorem 15.42); polynomial models, the enlargement and scale defects, nonflatness and `Tor_1` (Theorems 15.45–15.47, Proposition 15.48); monomial denominators (Proposition 15.50); the Gaussian dichotomy (Theorem 15.54). Files prefixed `08-fractions-`. |
| **09** | *Omnific Fractions: Rationality, Denominator Ideals, and Dense Arithmetic Fibres* | `9a385d3` | The calculus of denominator ideals and least denominators (Propositions 15.2, 15.3); the unimodular region `𝒱` and its dichotomy (Theorem 15.15); nearly equal values of opposite type (Example 15.24); local density (Proposition 15.26); fibers as congruence orbits (Theorem 15.32, Corollary 15.33); set-wise focusing (Theorem 15.35), dense fibers (Corollaries 15.36, 15.37) and nowhere continuity (Corollary 15.38). Its pair multiplier theorem and its one-scale classification are special cases of 08's Theorems 15.11 and 15.18 and are credited there. Files prefixed `09-fraction-fibres-`. |
| **C10** | *Curve Rigidity over the Omnific Integers: Elliptic equations, differential separation, and semiabelian varieties* | `4cdeaec` | The fiber bijection `Π → ct⁻¹(n)` on affine-line models and the fact that only `s = 0` gives an ordinary point (Theorem 17.11(ii)); quasi-finite maps to semiabelian and other rigid targets (Theorem 18.5); nonsplit tori by faithful flatness (after Lemma 18.3); the general elliptic field point (Remark 17.24); the valuation-ring point and the verticality conclusion (Section 18.5, Section 17.5). Files prefixed `10-curve-rigidity-`. |
| **C11** | *Curve and Abelian Rigidity over the Omnific Integers: A complete smooth-affine-curve dichotomy, support-preserving derivations, and invariance over reduced coefficient rings* | `f6e031a` | Exact fibers over any coefficient ring `𝔬 ⊆ 𝕜` (Theorem 17.11); proper classes of fiber points (Corollary 17.12(c)); positive genus by descent from `𝕜̄` and the one-form remark (Theorem 17.2, Remark 17.3); the quasi-finite theorem for any rigid target (Theorem 18.5); reduced coefficient algebras (Theorem 18.9); the dual-number defect (Theorem 18.11); the characteristic-two elliptic point (Proposition 18.12, with C14); a discretely ordered ring with no omnific copy (Theorem 18.14); curve subalgebras (Corollary 17.9, with C12). Files prefixed `11-curve-abelian-rigidity-`. |
| **C12** | *Curve Rigidity over Omnific Integers: Logarithmic differentials, elliptic equations, and denominator ideals* | `89bec38` | The strict-ideal proof of the squarefree theorem (Theorem 16.6, with C13); the logarithmic proof of the curve classification (Lemma 17.7, Theorem 17.8); descent for separated models over `Z` (Theorem 17.17); coordinate ideals: invertible ⇔ principal ⇔ rational (Lemma 17.19, Theorems 17.20, 17.21) and the explicit ideal (Example 17.23); the singular Weierstrass dichotomy with integer `r` (Proposition 16.11). Files prefixed `12-curve-logarithmic-`. |
| **C13** | *Differential Rigidity of Omnific Points: Smooth-curve classification, squarefree equations, and algebraic groups* | `4cdeaec` | Annihilation of global tensors (Theorem 16.14); symmetric differentials and ample cotangent bundles (Definition 16.18, Theorem 16.19, Corollary 16.20); inheritance (Proposition 16.21); general Weierstrass equations (Corollary 16.10); all smooth curves, including `P¹` (Corollary 17.10); polynomial witnesses (Corollary 17.16); the nonconstant part of commutative groups (Theorem 18.6); the characteristic-`p` example (Proposition 18.13). Files prefixed `13-differential-rigidity-`. |
| **C14** | *Differential Rigidity of Hahn Rings: Curves, Abelian Varieties, and Omnific Diophantine Points* | `4cdeaec` | Base of Sections 16–18: the two-ring principle over any field of characteristic zero and any exponent group (Definition 16.12, Theorem 16.16, Corollary 16.17); the curve classification over every such field (Lemma 17.5, Theorem 17.6); integer polynomial arcs and the congruence criterion (Lemma 17.14, Proposition 17.15); unimodular coordinates over `ℛ_𝔬(𝕜, Γ)` and rational projective points (Theorem 17.18, Corollary 17.22); tori via `𝕜̄` (Lemma 18.3). Files prefixed `14-hahn-differential-rigidity-`. |
| **C15** | *Geometric Rigidity over Omnific Integer Rings: Smooth curves, semiabelian varieties, and logarithmic differential certificates* | `934810a` | Section 18.6: logarithmic symmetric differentials on a smooth proper compactification with normal-crossings boundary contract into the valuation ring (Lemma 18.15) and vanish on the Euler derivations at every point (Theorem 18.16); tangent separation by them, in particular spanning by logarithmic one-forms, forces rigidity (Definition 18.17, Corollary 18.18); the abstract interface with its logarithmic hypothesis (Remark 18.19); descent over any coefficient ring (Theorem 18.20) and the omnific consequence (Corollary 18.21); finite products (Proposition 18.22). Its other results are independent proofs of statements of C10–C14 and are credited there. Files prefixed `15-logarithmic-rigidity-`. |
| **C16** | *Singular Curves over Omnific Integers: Conductor differentials, a complete Hahn-rigidity criterion, and polynomial witnesses at every surreal scale* | `bcac55a` | Section 17.6: for every geometrically integral affine curve over a field of characteristic zero, singular or not, and every `Γ ≠ 0`, nonconstant `𝒜_𝕜(Γ)`-points exist iff the normalization is `𝔸¹`, iff there is a nonconstant polynomial map `𝔸¹ → C`, with finite-support witnesses (Theorem 17.25); Seidenberg's power identity (Lemma 17.27), the conductor certificate `κ^{2ℓ+1} α(∂)^n ∈ 𝒜_𝕜(Γ)` and the derivative-order bound (Theorem 17.28, Corollary 17.29); the place at infinity and the one-place obstruction in every characteristic (Lemma 17.30, Proposition 17.31); positive genus across singularities (Theorem 17.32); scale independence and finite birational invariance (Corollaries 17.34, 17.35); all affine schemes of dimension at most one over an algebraically closed field (Theorem 17.36); witnesses in every fiber (Corollary 17.37); the repeated-root superelliptic test (Theorem 17.38, Corollary 17.39); `Z² = X²(X³ − X + 1)` with a seventh-order certificate (Theorem 17.40); omnific and Gaussian rigidity, arithmetic families and the Gaussian dichotomy (Theorem 17.41, Proposition 17.42, Corollary 17.43); Questions 21.23–21.30. Its rings, Euler derivations, non-normality example, descent of forms of `𝔸¹` and smooth case are credited where printed. Files prefixed `16-singular-curves-`. |
| **C17** | *Constant Discriminants and Étale Unit Rigidity over Omnific Hahn Rings: Translation classification, arithmetic descent, and normal spectral rigidity* (27 pp.) | `efc5446` (tree `aba6982`) | Section 19.4: over any field of characteristic zero and any ordered group, a monic polynomial over `𝒜_𝕜(Γ)` or `𝔬 + Π_𝕜(Γ)` with nonzero constant discriminant is `P̄(X − h)`, `h = −(a₁ − ct a₁)/n` (Theorem 19.12), by a universal root-velocity certificate (Lemma 19.9, Proposition 19.11); the parameterization and coefficient test (Corollary 19.13, (19.10)); the omnific and Gaussian forms (Corollary 19.15); factors, Galois groups, marked values and coherent translations (Proposition 19.18, Theorem 19.19, Corollary 19.20, Theorem 19.21); units of finite étale algebras are algebraic, `𝖡^× = 𝖢_𝖡^×` (Theorem 19.26); monogenic and arithmetic descent (Theorems 19.29, 19.31); the two-translation classification of critical configurations (Theorem 19.33); normal matrices `M = ct M + hI` (Theorem 19.37); five boundary examples (Examples 19.41–19.45); a second proof through a splitting algebra (Lemma 19.46); Questions 21.31–21.40. Its ring, Euler and algebraic-constant lemmas are credited where printed. Files prefixed `17-discriminant-rigidity-`. |

Batch-25 item 03 is manuscript 13 of the sibling report
[`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/),
where its files are shipped with the prefix `13-small-target-rigidity-`. Its
fiber and norm results (its Sections 8–9) are printed here once, tagged `[13]`:
the Gaussian fiber theorem (Theorem 6.3), the converse of the kernel criterion
(Corollary 6.4), the real-kernel remark (Remark 6.5), a rank-deficient level
(Example 6.6) and étale norms (in Theorem 6.15). Its real fiber theorem is
Theorem 6.2(a), printed once. It is not counted among this report's fifteen
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
09 are not shipped because they list the delivered file names. Sources C10–C14
are shipped with their code, data and audits under the prefixes `10-` to `14-`;
the letter C keeps their tags apart from `[13]` and `[14]`, which denote the
sibling report's manuscripts. Their texts, PDFs, delivered READMEs and the
checksum manifests of C10 and C12 are not shipped. Sources C10, C13 and C14 pin
`4cdeaec`, source C11 pins `f6e031a` and source C12 pins `89bec38`, 23, 26 and 27
commits before the archive commit `5610500` (C13 and C14 arrived in `21016dc`); at
all three pins this report had only sources 01, 02 and 05. Source C15 is shipped with
its code, data and proof audit under the prefix `15-`; its text, PDF, delivered
README and checksum manifest are not. It pins `934810a`, 18 commits before `c6359e4`
and 23 before its own placement `66d7e55` (its archive arrived in `65775fb`); at that
pin this report had sources 01, 02, 05, 06 and 07, and C15 saw none of C10–C14. Source C16
is shipped with its code, data and source audit under the prefix `16-singular-curves-`
(the sibling report's manuscript 16 uses `16-fresh-scale-`; it is not a source here); its
text, PDF, delivered README and checksum manifest are not. It pins `bcac55a`, 87 commits
before its placement `9d28e28` (its archive arrived in `39fe674`); at that pin C10–C14 were
placed but not yet written into this article (`ac54217` is not an ancestor of the pin) and
C15 was not placed, so C16 saw only the audits of C13 and C14 among the curve sources.
Source C17 (batch-33 manuscript 07, archive `omnific_discriminant_rigidity`, placed in
`aa9c891`, archive committed in `73043eb`) is shipped with its code, data, source audit
and proof audit under the prefix `17-discriminant-rigidity-` (the sibling report's
manuscript 17 uses `17-relations-arithmetic-`; it is not a source here); its text, PDF and
delivered README are not shipped, and it delivered no checksum manifest. It pins
`efc5446` (tree `aba6982`), 70 commits before `aa9c891`; at that pin C10–C15 were written
into this article and C16 was placed but not written, and C17 read this report's guide,
not its article.

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
directly after Section 14, with the label sub-prefix `odg:frac:`. Sources
C10–C14 all prove one spine: an elementary Bézout certificate for squarefree
`y^m = P(x)` and a two-ring argument in which Euler derivations, which preserve
the one-sided Hahn ring and push the opposite valuation ring into its maximal
ideal, kill every global differential at a point of a proper variety; together
they give the classification of smooth affine curves and the answer to this
report's Question 21.1 for smooth curves, including its Weierstrass test. Source
C14 is the base because it has the weakest hypotheses on the shared theorems
(any field of characteristic zero, any exponent group); C10 and C12 assume an
algebraically closed field for curves, C11 such a field or `R`, and C13 a
divisible exponent group and the fields `R`, `C`. The five are added as one new
part, Sections 16–18, directly after Section 15, with the label sub-prefix
`odg:cr:`. Source C15 arrived after that integration. About three quarters of it
reproves statements of C10–C14 (the squarefree and Weierstrass theorems, abelian,
torus and semiabelian rigidity, quasi-finite maps, the smooth-curve classification,
unimodular coordinates, the characteristic-two point); its new material is the
logarithmic form of the two-ring argument in every dimension, which answers the first
question of Question 21.19 in sufficient form. So it is an addition to the same part,
appended as Section 18.6 with the sub-prefix `odg:log:`, and its duplicates are
credited where they are printed. Source C16 answers the first two clauses of Question
21.17 (singular curves): the smooth classification extends to every geometrically
integral affine curve, with the normalization in place of the curve. It shares the part's
spine and generalizes its main theorem, so it is appended to the same part as Section
17.6, at the end of Section 17 directly after Section 17.5, which states the problem, with
the sub-prefix `odg:sg:`; appending at the end of a section moves no number. Source C17
treats monic polynomials whose coefficients vary at a surreal scale. It answers Question
21.6 (roots with omnific coefficients) for monic polynomials with a nonzero constant
discriminant and the first clause of Question 21.22 in dimension zero, and it uses the
Euler and two-ring mechanism of the curve part; its subject is equations with omnific
coefficients, so it is appended as Section 19.4, at the end of Section 19 (a new section
before Section 20 would renumber Sections 20 and 21), with the sub-prefix `odg:disc:` and
its questions after Question 21.30. None of the fifteen sources, nor source 13 or 14,
contradicts another.

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

**Printed once from sources C10–C14.** All five reprove the rings, `ct`, the
units, the degree rules and the Euler derivations (Sections 2, 7 and 11,
extended in Lemmas 16.1–16.3). Within Sections 16–18, printed once with every
proving source named: the squarefree theorem and the cubic certificate (all
five; Theorem 16.6, Proposition 16.8), the nonsingular and singular Weierstrass
results (Corollary 16.9; Proposition 16.11, from C10, C11, C12, C14), the
two-ring principle and proper rigidity (all five; Theorems 16.14, 16.16), the
canonical-bundle and puncture lemmas (Lemmas 17.1, 17.4), the curve
classification (all five, at different generality; Theorem 17.6), the
arithmetic fibers (C10, C11, C13, C14; Theorem 17.11, Corollary 17.12),
unimodular coordinates (C10, C13, C14; Theorem 17.18), abelian and semiabelian
rigidity (all five; Theorems 18.2, 18.4), the quasi-finite theorem (C10, C11,
C12, C14; Theorem 18.5), the characteristic-two point (C11 and C14, the same
example with exponents rescaled by three; Proposition 18.12), the fixed-workspace
non-normality examples (C10, C12, C13, credited to Proposition 4.12; Section
17.5), the field points outside the ring (C10, C12, C13, C14; Remark 17.24) and
the nonconstant-coefficient examples (Section 18.5). The coordinate clearing
reproved by C10 and C12 is Corollary 4.7 and is not reprinted.

**Printed once from source C15.** Its rings, units, Euler derivations and joint
constants (Lemmas 16.1–16.3, Corollary 16.4), the squarefree theorem by the strict
route and the cubic certificate with its worked example `Δ₀ = 23` (Lemma 16.5,
Theorem 16.6, Proposition 16.8, Corollary 16.9), the singular families (Proposition
16.11), symmetric differentials and ample cotangent bundles (Theorem 16.19, Corollary
16.20), inheritance (Proposition 16.21), the logarithmic dimension count and the curve
classification with `ℙ¹` (Remark 17.3, Lemmas 17.4, 17.7, Theorems 17.6, 17.8,
Corollary 17.10), unimodular coordinates on curves of positive genus and the Fermat
specialization (Corollary 17.22), invariant differentials, abelian, torus and
semiabelian rigidity and quasi-finite maps (Lemma 18.1, Theorem 18.2, Lemma 18.3,
Theorems 18.4, 18.5), the characteristic-two point (Proposition 18.12, C11's example
with `x` and `y` interchanged), and the field and valuation-ring points (Remark 17.24,
Section 18.5) are printed once, with C15 added to their credits. Its workspace lemma
is Lemma 2.6 here.

**Printed once from source C16.** Its ring lemma (units, the retraction, transcendence of
nonconstant elements, no nonzero element of positive valuation; Lemma 16.1), its Euler
derivations and their detection (Lemmas 16.2, 16.3), its fixed-workspace non-normality
example (for any `0 < e < H` with `ne < H`; Section 17.5), its descent of forms of the
affine line (Lemma 17.5) and its smooth case (Theorem 17.6) are printed once, with C16
added to their credits. Its elliptic Bézout polynomials are those of Proposition 16.8 at
`(a, b) = (−1, 1)`.

**Printed once from source C17.** Its ring lemma (the retraction, the intersections with
the valuation ring, the units and the pullback `𝔬 + Π_𝕜(Γ)`; its Lemma 2.1) is Lemma 16.1;
its Euler derivations, logarithmic boundedness and joint constants (its Lemma 3.1) are
Lemmas 16.2 and 16.3; its algebraic constants of the Hahn field (its Lemma 6.3) are
Corollary 16.4 and Lemma 16.1(d), and over `Oz` Proposition 2.8 (Lean-proved, see the ledger);
its example `Σ ω^{1/m}` is the one after Lemma 16.1. C17 is added to their credits.

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
15.52). Squarefree rigidity: the strict-ideal proof of C12 and C13 (Theorem
16.6) and the unit argument at the corner `(2,2)` of C10, C11 and C14 (Remark
16.7); Theorem 7.4 keeps its own proof as a special case. The rigid direction of
the curve classification: C14's proof by descent from `𝕜̄` (Theorem 17.6) and
C12's logarithmic proof (Theorem 17.8). Positive genus: global generation
(Theorem 17.2) and one nonzero form (Remark 17.3). Tori: C14's descent through
`𝕜̄` and C10's faithful flatness (after Lemma 18.3), with C15's descent along a
finite splitting field recorded there. The Weierstrass result has
both an elementary and a geometric proof. C15's proof of the curve classification by
one logarithmic form is described after Corollary 18.18; its local computation works
wherever the centre lies, so it needs no closed-centre step. C16's proof of the smooth
case (one regular differential and its valuation at the centre; a function with a single
pole instead of the unit argument) is a third route to the rigid direction of Theorem 17.6
(Remark 17.33), and for `Z² = X²(X³ − X + 1)` both of C16's proofs are printed, by the
general theorem and by the explicit seventh-order certificate (Theorem 17.40). Both of
C17's proofs of the translation theorem are printed: the universal root-velocity
certificate (Section 19.4.3) and the route through the unit theorem and a splitting
algebra of rank `n!` (Section 19.4.10). For real symmetric omnific matrices the merge
adds a second route to Theorem 19.37 through Corollary 9.5 (Remark 19.40).

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
Question 21.3. Remark 15.39: comparison with the omnific groups report. The
focusing matrices `F_{x,b}` are transposes of that report's non-elementary
unipotents; they lie outside `E_2(Oz)` at centres with irrational standard
part; and `E_2(Oz)·∞` is not dense although `K·∞` is, so the density of
Corollary 15.36 needs non-elementary matrices. Its certificates, the table of
Example 15.23 and the second Bézout lift were checked with SymPy. The batch-28
merge adds three items tagged `[merge]` with complete proofs: the closed-centre
step in C12's logarithmic proof (Theorem 17.8); the comparison with the omnific
groups report (Remark 18.7): `G_a` is nonrigid and the one-dimensional tori are
rigid in both reports, the vector-group kernel of Theorem 18.6 is that report's
unipotent kernel for commutative groups, and real and complex rigidity coincide
for smooth curves but not for groups (`SO_3`); and the observation that C13's
characteristic-`p` curve `y^p = x^p − x` is an affine line (after Proposition
18.13). It also states results of C11 and C13 over every field of
characteristic zero and every exponent group (Corollaries 16.10, 17.10, Theorems
16.14, 17.11, 18.6), with the sources' own proofs. The batch-29 integration of
source C15 adds nothing tagged `[merge]`; Section 18.6 prints C15's own results with
its own proofs. The batch-31 integration of source C16 adds three items tagged `[merge]`
with complete proofs: the observation that the one-place obstruction (Proposition 17.31)
is consistent with the characteristic-two and characteristic-`p` examples, each with one
point at infinity; the third route to the smooth classification (Remark 17.33); and the
superelliptic test over an arbitrary field of characteristic zero, by base change to `𝕜̄`
and Lemma 17.5 (after Theorem 17.38). The batch-33 integration of source C17 adds five
items tagged `[merge]` with complete proofs: the omnific roots at a constant discriminant
(Corollary 19.16: the roots in `Oz` are `h + c` for the integer roots `c` of `P̄`); the
comparison with the square-discriminant criterion and the failed-lifting example
(Remark 19.17); the étale norm theorem 6.15 in characteristic zero as the constant case of
the unit theorem (Remark 19.28); the comparison with the sibling report's canonical
translation and rich targets (Remark 19.35); and the route through Corollary 9.5 for
symmetric omnific matrices (Remark 19.40), with two tagged sentences (the generic image
`√(ω² + 1)` in Example 19.45 and the two-ring pattern in Section 19.4.10).

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
In Sections 16–18 (conventions in Section 16.1) the sources C10–C14 are tagged
with the letter C, because `[13]` and `[14]` already denote the sibling report's
manuscripts. Their rings take the names of Section 11: `𝒜_𝕜(Γ)` for the
nonnegative-support ring (C10's `B_{k,H}`, C11's and C14's `B_Γ(k)`, C12's `B`,
C13's `ℬ_{k,Γ}`), `Π_𝕜(Γ)` for its ideal (C11's `P_Γ(k)`, C12's and C13's `I`),
and `ℛ_𝔬(𝕜, Γ)` for the arithmetic ring (C11's `R_Γ(D,k)`, C14's `R_Γ(D;k)`; `D`
is the Pell parameter here); the new names `ℍ_𝕜(Γ)`, `𝒪_𝕜(Γ)` and `𝔪_𝕜(Γ)`
denote the Hahn field, its valuation ring and its maximal ideal. Three sources use
the `t`-convention `t^γ = ω^{−γ}` and are translated. The Euler derivations are
`∂_λ` with `λ : Γ_Q → 𝕜` (the sources' `D_λ`), and the sources' macros `\OO`
(`𝒪`), `\A` (`𝔸`) and `\dd` are replaced, since `\OO` is the orthogonal group
here. In those sections `A` is an abelian variety, not an intermediate ring, `Σ`
is the boundary of a curve and `⟨a⟩` a coordinate ideal (C12's `J(a)`); C14's
congruence integers `M, D, L` are `N, N_1, N_2`. Source C15 also uses the
`t`-convention: its `𝒜`, `𝓘`, `𝒱`, `ℋ` and `R_D = D ⊕ 𝓘` are `𝒜_𝕜(Γ)`, `Π_𝕜(Γ)`,
`𝒪_𝕜(Γ)`, `ℍ_𝕜(Γ)` and `ℛ_𝔬(𝕜, Γ)`; its `D_ℓ` is `∂_{−ℓ}`, the same family; its
symmetric power `q` is `r` (here `q` is the valuation-ring point); and in Section 18.6
`X̄` is a smooth proper scheme, `E` a normal-crossings boundary and `X = X̄ ∖ E`.
Source C16 (conventions at the start of Section 17.6) uses the `t`-convention: its
`B_{k,Γ}`, `K`, `O`, `𝔪` are `𝒜_𝕜(Γ)`, `ℍ_𝕜(Γ)`, `𝒪_𝕜(Γ)`, `𝔪_𝕜(Γ)`, its `𝒥_R`, `𝒥_C`
are `Π`, `Π_C`, and its `D_λ` is `∂_{−λ}`, the same family; its `Oz[i]` and its
valuation `v` are unchanged. Letters it uses twice, or that the part reserves, are renamed: the coordinate
ring `A` and normalization `Ã` are `𝕜[C]`, `𝕜[C̃]` (`A` is an abelian variety here); the
smooth projective model `X` is `C̄`; the centre `p` is `Q`; the conductor element `d` is
`κ`; the number `m` of terms of a differential presentation is `ℓ` (`m` stays the
superelliptic exponent); the contraction `s = α(D)` is `α(∂)`; a general derivation `D`
is `∂` and a coefficient subring `D` is `𝔬`; the formal variable `z` and Taylor map `E`
are `w`, `𝒯`; the number of roots `r` is `k` and `r_∞` is `n_∞` (`r` stays the vanishing
order); the cofactors `Q`, `S` are `P_1`, `P_odd`; the Bézout polynomial `V` is `W`;
points `P`, `P_0` are `x`, `x_0` (bold); and in the arithmetic families `h`, `a` are `s`,
`β`.
Source C17 (conventions at the start of Section 19.4) uses the `t`-convention: its `𝒜`,
`𝓘`, `𝒪_K`, `K = k((t^Γ))` are `𝒜_𝕜(Γ)`, `Π_𝕜(Γ)`, `𝒪_𝕜(Γ)`, `ℍ_𝕜(Γ)`; its splitting
field `K̂ = k̄((t^{Γ_Q}))` with valuation ring `Ô` is `ℍ_{𝕜̄}(Γ_Q)` with `𝒪_{𝕜̄}(Γ_Q)`; its
`D ⊆ k` and `𝒜_D = D ⊕ 𝓘` are `𝔬` and `ℛ_𝔬(𝕜, Γ)` (`D` is the Pell parameter); its
`P₀ = ct P` is `P̄`, as at the start of Section 19; and its `D_χ` is `∂_{−χ}`, the same
family. Letters it shares with reserved ones are renamed: the finite étale algebra `B`,
its constants `C_B` and the splitting algebra `S` are `𝖡`, `𝖢_𝖡`, `𝖡_P` (`B` is a bilinear
form); the rank `N` is `r` (`N` is a norm form; `r` is the dimension of `E` in Theorem 6.15);
the velocity polynomial `Q`, divided difference `S(X, Y)`, velocities `u_i`, certificates
`F_{n,s}` and characteristic polynomial `H_y` are `Ṗ`, `𝖶(X, Y)`, `ṙ_i`, `ℱ_{n,s}`, `ch_y`;
the spectral idempotents `E_j` are `𝖯_j` (`E` is an étale algebra); the target shift `c` is
`β` (the sibling report's letter); the number `r` of polynomials and graph `G` in the
resultant theorem are `ℓ`, `𝒢` (`G` is the Gram matrix); the quadratic velocities `α, β`
are `b₁, b₂`; the two-sided root `r` is `ρ`. Four readings are separated in Section 19.4:
a *constant* discriminant lies in `𝕜` (it is not merely independent of `X`), the constant
coefficient `a_n` in `X` is not the constant term of a series, a nonzero constant
discriminant need not be a unit, and `𝒜_𝕜(Γ)` is not the set of elements of nonpositive
valuation.
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
   The threshold is sharp at `n = 2`. Theorem 7.4 is the case
   `P(X) = (c − aX^m)/b` of the squarefree theorem of Section 16 (Theorem 16.6).
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
    case); supplied finite-support Bézout witnesses specialize with them. On
   smooth affine curves every nonordinary point shares its constant term with a
   finite-support one (Corollary 17.16).
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
15. **Differential rigidity (Section 16).** Throughout, `𝕜` is any field of
    characteristic zero and `Γ` any set-sized ordered abelian group. Euler
    derivations `∂_λ`, `λ : Γ_Q → 𝕜`, map `𝒜_𝕜(Γ)` into `Π_𝕜(Γ)` and the
    opposite valuation ring `𝒪_𝕜(Γ)` into its maximal ideal `𝔪_𝕜(Γ)`, and their
    common constants are `𝕜` (Lemmas 16.1–16.3, Corollary 16.4). Every solution
    of `y^m = P(x)` in `𝒜_𝕜(Γ)` with `P` squarefree and `m, deg P ≥ 2` is
    constant, by a finite Bézout certificate (Lemma 16.5, Theorem 16.6; the unit
    route is Remark 16.7); this contains Theorem 7.4 and Corollary 7.6. For
    `4a³ + 27b² ≠ 0` every omnific solution of `y² = x³ + ax + b` is an ordinary
    integer solution, also over `Oz[i]` and for general Weierstrass equations
    (Proposition 16.8, Corollaries 16.9, 16.10); if `4a³ + 27b² = 0` then
    `a = −3r², b = 2r³` with `r ∈ Z` for integer `a, b`, and `(s² − 2r, s³ − 3rs)`
    is an injective family (Proposition 16.11). For any subring `R` and valuation
    ring `V` of a field with `∂(R) ⊆ R`, `∂(V) ⊆ 𝔪_V`, `R ∩ 𝔪_V = 0`, every global
    covariant tensor on a proper variety vanishes on the Euler tangents of an
    `R`-point (Theorem 16.14); with joint constants `𝕜`, a smooth proper `X` with
    globally generated cotangent sheaf has `X(R) = X(𝕜)` (Theorem 16.16), so
    `X(𝒜_𝕜(Γ)) = X(𝕜)` (Corollary 16.17). Detection by symmetric differentials, a
    semiample tautological bundle or an ample cotangent bundle also suffices
    (Theorem 16.19, Corollary 16.20), and rigidity passes to locally closed
    subschemes (Proposition 16.21).
16. **Smooth curves and their omnific points (Section 17).** Curves of positive
    genus are rigid (Theorem 17.2). For `Γ ≠ 0`, a smooth geometrically integral
    affine curve has nonconstant `𝒜_𝕜(Γ)`-points exactly when it is `𝔸¹_𝕜`
    (Theorem 17.6), with a second, logarithmic proof over algebraically closed
    fields (Theorem 17.8); every smooth geometrically integral separated curve with
    nonconstant points is `𝔸¹` or `ℙ¹` (Corollary 17.10). Over any subring
    `𝔬 ⊆ 𝕜` the points over `ℛ_𝔬(𝕜, Γ)` are ordinary unless the curve is an
    affine line, and then every fiber of `ct` over an `𝔬`-point is a copy of
    `Π_𝕜(Γ)` (Theorem 17.11). For an affine model over `Z` with smooth generic
    fiber: `𝒞(Oz) = 𝒞(Z)` unless the fiber is `𝔸¹_Q`, and then each fiber over an
    integer point is `{φ(φ⁻¹(n) + s) : s ∈ Π}` (Corollary 17.12), with integer
    polynomial arcs through every integer point (Lemma 17.14), a congruence test
    for the integer points (Proposition 17.15) and finite-support witnesses
    (Corollary 17.16). Separated models over `Z` with rigid complex fiber have only
    ordinary omnific points (Theorem 17.17). On a projective variety rigid over
    `𝒜_𝕜(Γ)`, unimodular tuples over `ℛ_𝔬(𝕜, Γ)` are constant (Theorem 17.18); a
    coordinate ideal is invertible iff principal iff the point is rational
    (Theorems 17.20, 17.21); on a curve of positive genus over `Q` the points with
    unimodular omnific coordinates are its rational points (Corollary 17.22), and
    Example 17.23 gives an explicit noninvertible ideal. Field points outside the
    ring and the status of singular curves are Remark 17.24 and Section 17.5.
17. **Group varieties, coefficient algebras and sharpness (Section 18).**
    Abelian varieties and their locally closed subschemes, tori and semiabelian
    varieties are rigid (Theorem 18.2, Lemma 18.3, Theorem 18.4), and rigidity
    passes along quasi-finite maps (Theorem 18.5). For a smooth connected
    commutative algebraic group `G` with maximal unipotent subgroup `≅ G_a^d`,
    `G(𝒜_𝕜(Γ)) ≅ G(𝕜) ⊕ Π_𝕜(Γ)^d` (Theorem 18.6), consistent with the omnific
    groups report (Remark 18.7). For every reduced `𝕜`-algebra `S` the rigid
    classes satisfy `X(S) ≅ X(𝒜_S(Γ))` (Theorem 18.9); over dual numbers an
    abelian variety gains exactly `Lie A ⊗ Π_𝕜(Γ)` (Theorem 18.11). In
    characteristic two the smooth cubic `y² + y = x³` has the nonconstant point
    `(ω^{1/3}, Σ ω^{2^{−n}})` (Proposition 18.12), and in characteristic `p`
    squarefree rigidity fails (Proposition 18.13). `Z[x, y] ⊆ R((ω⁻¹))` with
    `x = ω²`, `y = ω³(1 − ω⁻⁴)^{1/2}` is a discretely ordered ring with no
    injective homomorphism into `Oz` (Theorem 18.14). Nonconstant coefficients
    and the valuation ring are not rigid (Section 18.5). *Logarithmic
    differentials (Section 18.6, source C15).* For a smooth proper `X̄` over `𝕜` with a
    reduced normal-crossings divisor `E` and `X = X̄ ∖ E`, every global logarithmic
    symmetric differential contracts into the valuation ring at a field point
    (Lemma 18.15) and vanishes on `∂_λ` at every `𝒜_𝕜(Γ)`-point of `X` (Theorem
    18.16); if these differentials separate tangent directions after every field
    extension, in particular if the logarithmic one-forms span the cotangent spaces,
    then `X(𝒜_𝕜(Γ)) = X(𝕜)` (Definition 18.17, Corollary 18.18). An abstract interface
    with the dual hypotheses `∂(R) ⊆ J`, `∂(V) ⊆ V`, `J ∩ V = 0` and `∂u/u ∈ V` is
    Remark 18.19. Separated models over any subring `𝔬 ⊆ 𝕜` with rigid fiber have
    only points in `𝔬` over `ℛ_𝔬(𝕜, Γ)` (Theorem 18.20), so logarithmic complements
    over `Z` and `Z[i]` have only ordinary points in `Oz` and `Oz[i]` (Corollary
    18.21); rigidity passes to finite products (Proposition 18.22).
   *Singular curves (Section 17.6, source C16).* For a geometrically integral affine curve
   `C` over any field of characteristic zero and any `Γ ≠ 0`: `C(𝒜_𝕜(Γ)) ≠ C(𝕜)` iff the
   normalization is `𝔸¹_𝕜` iff there is a nonconstant morphism `𝔸¹ → C`, with
   finite-support witnesses on any scale `ω^γ` (Theorem 17.25). Seidenberg's identity
   gives `κ²(∂b)^n ∈ R` whenever `κb^j ∈ R` for `j ≤ n` (Lemma 17.27); a conductor element
   `κ` then gives `κ^{2ℓ+1} α(∂)^n ∈ 𝒜_𝕜(Γ)` for a differential with an `ℓ`-term
   presentation (Theorem 17.28), and derivatives through order
   `⌊(2ℓ+1)δ/(r+1)⌋ + 1` give the contradiction (Corollary 17.29). A nonconstant point
   selects one boundary place of the normalization, where the valuation is discrete
   (Lemma 17.30); in every characteristic only one boundary point can be missing
   (Proposition 17.31), and in characteristic zero positive genus is rigid across
   singularities (Theorem 17.32). Rigidity does not depend on `Γ` and is a finite
   birational invariant (Corollaries 17.34, 17.35); over an algebraically closed field
   it extends to all affine schemes of dimension at most one (Theorem 17.36), with
   witnesses in every fiber (Corollary 17.37). `Y^m = c∏(X − a_i)^{e_i}` is flexible iff
   exactly one `e_i` is not divisible by `m` and it is prime to `m` (Theorem 17.38); for
   `Y² = P(X)` the test is `deg P_odd ≤ 1`, with a sign condition over `R` (Corollary
   17.39). `Z² = X²(X³ − X + 1)` has only ordinary omnific and Gaussian omnific points,
   by a seventh-order certificate (Theorem 17.40). Rigid singular curves over `Z` or
   `Z[i]` have only ordinary points in `Oz` or `Oz[i]` (Theorem 17.41); over an integer
   point with a real (or complex) normalization preimage there is a proper class of
   finite-support points (Proposition 17.42), and nonordinary Gaussian points exist iff
   the normalization is `𝔸¹_C` and a Gaussian integer point exists (Corollary 17.43).
18. **Omnific coefficients (Section 19).** The square-discriminant criterion
    (Theorem 19.1), initial forms (Proposition 19.3), two-term roots
    (Proposition 19.4, also proved by finite factorization) and simple residue
    roots that do not lift (Example 19.5). Nonmonic quadratics need an extra
    divisibility condition; the omnific lifting failure concerns a different
    ring from finite-surreal standard-part lifting. The sibling report's fresh-scale image-gap theorem contains
    `x² = ω² + 1` (Example 19.2) and the two-term equations as special cases.
    *Constant discriminants (Section 19.4, source C17).* Over any field `𝕜` of
    characteristic zero, any set-sized ordered group `Γ` and any unital `𝔬 ⊆ 𝕜`, a monic
    `P ∈ ℛ_𝔬(𝕜, Γ)[X]` has `Disc(P) ∈ 𝔬 ∖ {0}` iff `P̄` is squarefree and
    `P = P̄(X − h)` with `h ∈ Π_𝕜(Γ)`; then `h = −(a₁ − ct a₁)/n` is unique, even when the
    discriminant is not a unit and `1/n ∉ 𝔬` (Theorem 19.12). The proof: every elementary
    symmetric function of the relative root velocities `w_ij` satisfies
    `Δ^{2s} e_s(w) = ℱ_{n,s}(a, ∂a)` for a universal integer polynomial (Lemma 19.9), so
    it lies in `Π_𝕜(Γ)` and in the valuation ring, hence vanishes (Proposition 19.11).
    Consequences: fibers of `P ↦ P̄` are `Π_𝕜(Γ)`-torsors (Corollary 19.13); a finite
    coefficient test (19.10); over `Oz` and `Oz[i]` the roots are `h + c_i`
    (Corollary 19.15), so the omnific roots are `h + c` for the integer roots `c` of `P̄`
    (Corollary 19.16); monic factors and Galois groups are those of `P̄` (Proposition
    19.18, Theorem 19.19, for the chosen coefficient field); an ordinary value forces
    `h = 0` (Corollary 19.20); a connected graph of constant resultants forces one
    translation (Theorem 19.21). Every unit of a nonzero finite étale `𝒜_𝕜(Γ)`-algebra `𝖡`
    of rank `r` is algebraic over `𝕜`; the algebraic constants `𝖢_𝖡` form a finite étale
    `𝕜`-algebra of dimension at most `r`, `𝒜_𝕜(Γ) ⊗ 𝖢_𝖡 → 𝖡` is injective and is an
    isomorphism iff `𝖡` is generated by units (Theorem 19.26), which contains Theorem 6.15
    in characteristic zero (Remark 19.28); monogenic finite étale algebras are constant,
    over `𝒜_𝕜(Γ)` and over `ℛ_𝔬(𝕜, Γ)` (Theorems 19.29, 19.31). If the critical polynomial
    `f′/d` has nonzero constant discriminant, `f = f̄(X − h) + β` with `h, β ∈ Π_𝕜(Γ)`
    (Theorem 19.33). A normal matrix over `𝒜_ℂ(Γ)` with nonzero constant characteristic
    discriminant is `ct M + hI` (Theorem 19.37). Two-sided coefficients, positive
    characteristic, zero discriminant, nonnormal matrices and finite free reduced algebras
    give counterexamples (Examples 19.41–19.45).

**Questions (Section 21).** Two source questions are recorded as settled by
source 05 (Section 21.1): source 01's `Y² = X³ + 1` and coprime exponents, and
the unimodular half of the Fermat questions of sources 01 and 02. Section 21.2
records that source 06 answers the first part of Question 21.4 (an
existential definition of `Π`) and source 07's closing question on
positive-existential definitions of `Π` and of the graph of `ct`, and that the
report's quartics answer source 06's degree question in part. Section 21.3
records that source 08's rational-curve criterion answers Question 21.3 in part
(Corollary 15.30). Section 21.4 records that sources C10–C14 answer Question
21.1 for smooth curves, including its test `Y² = X³ + aX + b` with `a ≠ 0`
(nonsingular: only ordinary solutions; singular: polynomial families), answer
the existence part of Question 21.8 for smooth curves (Corollary 17.16), and
answer Question 21.3 in part for projective varieties with rigid complex fiber
(Theorem 17.18, Corollary 17.22). It also records that source C15 answers the
first question of Question 21.19, which hypotheses on logarithmic forms force
constancy, in sufficient form in every dimension (Corollary 18.18: tangent separation
by logarithmic symmetric differentials, in particular spanning by logarithmic
one-forms), and adds the rigid logarithmic complements to Question 21.1 (Corollary
18.21); both questions stay open. It records that source C16 answers the first two
clauses of Question 21.17 (Theorem 17.25), the curve part of Question 21.1 (Theorem
17.41, Corollary 17.43; over `Oz` the case of integer points whose normalization
preimages are all nonreal remains), the existence part of Question 21.8 for singular
curves over `Oz[i]` and, at integer points with a real normalization preimage, over `Oz`,
adds a characteristic-free necessary condition to Question 21.21 (Proposition 17.31) and
finite certificates to Question 21.22 (Theorem 17.28, Corollary 17.29); all stay open,
re-scoped. Still open: general affine varieties of higher dimension (Question 21.1,
re-scoped; the omnific groups report answers it for closed subgroup schemes of `GL_N`); primitive,
non-unimodular Fermat triples (Question 21.2); primitive homogeneous solutions
off rational curves and off rigid targets, and the dependence on the integral
model (Question 21.3, re-scoped); which fibers or subideals of `Π` are
Diophantine (the second part of Question 21.4); the guard's complexity, the
least degree of a definition of `Z`, a single Gaussian polynomial and better
quantifier bounds (Question 21.5); roots with omnific coefficients (Question
21.6); the size boundary (Question 21.7); finite-support search in higher dimension and
at real singular integer points without a real normalization preimage (Question 21.8,
re-scoped); coefficient recovery of lower quantifier
complexity (Question 21.9); structure that determines the real form of `Oz[i]`
(Question 21.10; a batch-32 status note records further negative information
from `saut:fs:thm:main-count`, not an answer); infinite algebraic extensions (Question 21.11); from sources
08 and 09, denominator ideals beyond one parameter (Question 21.12), the extent
of `𝒱` (Question 21.13), orbits outside `𝒱` (Question 21.14), several parameters
(Question 21.15) and other scale extensions (Question 21.16); and, from sources
C10–C14, singular curves (Question 21.17, re-scoped to lifting through the
normalization), rigidity beyond cotangent generation
(Question 21.18), affine varieties of higher dimension (Question 21.19,
re-scoped: necessary conditions, a classification of rigid complements, the
converse from the absence of polynomial curves, which C15 also asks, and C10's
surviving tangent directions),
primitive versus unimodular tuples on curves of positive genus (Question 21.20),
positive characteristic (Question 21.21), and omnific coefficients and
effective certificates (Question 21.22); and, from source C16, lifting through the
normalization (Question 21.23), real singular arithmetic fibers (Question 21.24), optimal
certificates (Question 21.25), a certificate-producing procedure (Question 21.26), a
positive-characteristic replacement (Question 21.27), normalization invariance in higher
dimension (Question 21.28), images of the constant term (Question 21.29) and
formalization (Question 21.30); and, from source C17, full and arithmetic étale descent
(Questions 21.31, 21.32), projective modules and nonnormal spectral data (Question 21.33),
sharp certificates (Question 21.34), nonconstant discriminants (Question 21.35), positive
characteristic (Question 21.36), restricted support rings (Question 21.37), several
configurations (Question 21.38), polynomial dynamics (Question 21.39) and formalization
(Question 21.40). Section 21.4 also records that source C17 answers Question 21.6 for
monic polynomials over `Oz` and `Oz[i]` with a discriminant in `Z ∖ {0}` (Corollary 19.16,
coefficient test (19.10)) and the first clause of Question 21.22 in dimension zero
(Theorem 19.12); both stay open, re-scoped, with status notes at the questions. No source
claims that these are open in the literature.

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
  now Section 19) gives a finite-algebra proof of the two-term root
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
- Source C12's logarithmic proof takes "the centre" of the valuation-ring point
  without showing that it is a closed point; if it were the generic point the
  function field would embed into `𝕜`. The step is added (Theorem 17.8).
- Source C13 assumes a divisible exponent group and, for curves and groups, the
  fields `R` and `C`; sources C10 and C12 assume algebraically closed fields for
  curves and C11 such fields or `R`. None of this is needed; the report states
  the results over every field of characteristic zero and every exponent group.
- Sources C10, C11 and C14 treat the corner `m = d = 2` of the squarefree theorem
  by units; the support inclusion `∂(𝒜) ⊆ Π` of C12 and C13 removes it and is
  printed first. That inclusion is already `opa:par:prop:Euler` and
  `osq:prop:classder`, which none of the five cites; the credit is added.
- Source C13 cites Stacks Tag 02AT for differentials, which is Section 111.50 of
  the chapter of exercises; Tag 00RM (Section 10.131), as cited by C10 and C14,
  is used instead. Its Tag 01KF for the valuative criterion was not checked; Tag
  0BX5 (Lemma 29.43.1), cited by C12 and C14, is used. The numbering of Milne's
  *Abelian Varieties* IV 6.7 (proposition in C10 and C11, corollary in C14) was
  not checked.
- The fixed-workspace non-integral-closure examples of C10, C12 and C13 repeat
  the witness `√(ω² + 1)` of Proposition 4.12, which was in this report at their
  pins; only their fixed-workspace forms are new, and the credit is added.
- No other gap was found in sources C10–C14, and none contradicts another source
  or the collection. Source C13's characteristic-`p` example is correct as a
  counterexample to squarefree rigidity; its curve is an affine line in
  characteristic `p`, which is recorded.
- Source C15 says that its example `t^{-1}(1 + t²)^{1/2}` for `Γ = Z` shows that
  "normality really is unavailable" even there. For `Γ = Z` the ring is the
  polynomial ring `𝕜[ω]`, which is normal; the element shows only that the ring is
  not integrally closed in the larger Hahn field. That root lies outside the
  fraction field and cannot obstruct a normalization lift of a nonconstant
  curve point over `𝕜[ω]`. Section 17.5 now explains this distinction next to
  C14's example; non-normality in other workspaces is a separate fact.
- Source C15's abstract says that semiabelian rigidity follows "consequently" from
  logarithmic annihilation; its proof goes through the abelian quotient and the torus
  kernel (Theorem 18.4), and no derivation from Corollary 18.18 is claimed. Its
  abstract interface asks for a valuation ring `V ⊆ K`; the proof needs a valuation
  ring of `K` (Remark 18.19). No gap was found in C15's proofs, and it contradicts no
  other source.
- Source C16 introduces `t^{-1}(1 + t²)^{1/2}` in the Hahn field "over a sufficiently
  divisible group"; the element already lies in `𝕜((t^Z))`, and `ω^γ(1 + ω^{−2γ})^{1/2}`
  lies in the Hahn field for every `Γ ≠ 0` (Section 17.6.9). No gap was found in C16's
  proofs, and it contradicts no other source; its one-place proposition agrees with the
  characteristic-two and characteristic-`p` examples.
- No gap was found in source C17's proofs, and it contradicts no other source. Its
  Lemmas 2.1, 3.1 and 6.3 are printed once as Lemmas 16.1–16.3 and Corollary 16.4.

**Stale repository statements.** Source 01 said the repository's
trigonometry material used the omnific integer part; at the pin the
foundations report already defined `Oz = Π ⊕ Z` (`found:eq:omnific`).
Sources 01, 02 and 05 correctly found no omnific report and no omnific Lean
at their pin. Sources 06 and 07 say that the explicit Diophantine definitions
of `Z` they give were not found in the repository, and source 13 says the same
of its exact fiber formulation; at their pin `71e9606` this was true, but the
collection has contained the quartic guards (Theorems 10.3, 10.4) and the exact
fiber theorem (Theorem 6.2) since `be06fc8`. The collection now has this
report and its sibling, and commit `f879c1e` constructs the actual omnific
ring and its constant-term retraction in Lean. Descriptions of
`docs/NORMAL_FORM_BRIDGE.md`, the `Surreal/Foundations/` workspace modules,
the surcomplex automorphism report's phase twists, the catalogue entry on
coefficient recovery by a dilation, and the formalization ledger remain
accurate. Sources 08 and 09 cite the rational-direction criterion as
"Theorem 11.5", its number at their pin `9a385d3`; it is now Theorem 14.5 (and
09's "§§4, 11" are now Sections 4 and 14). Source 09 describes this report as
built from manuscripts of 22 September, true at its pin; it now has thirteen
sources of 22 and 23 September. Source 08 gives the sibling report its old
title, *The Universal Set-Sized Quotient of the Omnific Integers*; it is now
*Set-Sized Quotients of the Omnific Integers*. Their other citations of this
report (Theorems 4.2, 4.6, 4.10, Corollary 4.3, the floor of Section 2) are
accurate, and 09's statement that its omnific results are pending in Lean
still holds. The sibling report's statement that manuscript 14's Gaussian
direction criterion is printed here was not true before this integration; it
is now (Corollary 15.55). Sources C10–C14 inspected the repository through the
connector at `4cdeaec`, `f6e031a` and `89bec38`, when this report had only
sources 01, 02 and 05 and fourteen sections. All five call `odg:q:affine`
"Question 14.1"; it is now Question 21.1, source C14's "Question 14.2" is
Question 21.2, source C13's "Section 11" is Section 14, and their "Section 14" is
Section 21; Sections 6–7 and Theorem 7.4 keep their numbers. The blob hashes they
record (`4c26f4e` at `4cdeaec`, `47af413` at `89bec38` and `f6e031a`) are
correct. Source C14's "three-source assembly", source C11's "reviewed Sections
1–7" and source C12's "51-report collection" were true at their pins; the report
now has thirteen sources, the reviews extend further, including the
all of Section 16, but not the curve classification and subsequent applications,
and the catalogue has grown. Source C15 inspected the repository through the
connector at `934810a`, when this report had sources 01, 02, 05, 06 and 07, and
quoted correctly its guide's statement that `y² = x³ + ax + b` with `a ≠ 0` was
outside the method; since `c6359e4` the collection settles that equation
independently (Corollary 16.9), and C15's proof is printed there once. Its remarks
that the unimodular Fermat case was already here and that the ledger separates
source assertions, review and Lean coverage are accurate. Source C16 inspected the
repository through the connector at `bcac55a` and did not read the assembled article in
full; it says that this report "and later companion audits" already classify smooth
curves, citing the audits of C13 and C14. At its pin that classification was in those
staged audits, not in the article; it has been Theorem 17.6 since `ac54217`. Its
statement that the audits leave singular curves outside their scope is accurate, and the
report said the same until this integration. Source C17 inspected the repository at
`efc5446` through GitHub, partly through excerpts and a truncated catalogue response,
and read this report's guide, not its article; its account of the repository (the
constant/purely infinite decomposition, coefficient reconstruction, Euler and two-ring
methods, curve and logarithmic results credited to integrated manuscripts) is accurate.
It does not cite Questions 21.6 and 21.22, Theorems 6.15 and 19.1, Corollary 9.5 or the
sibling report's canonical translation; those comparisons are made in Section 19.4. Their absence-of-Lean
statements describe the source pins; the ring package is now formalized,
as recorded above.

## What the report does not claim

No non-claim of any source was dropped. Appendix B lists them per source (01:
24 items, 02: 22, 05: 26, 06: 25, 07: 19, 08: 25, 09: 20, C10: 14, C11: 15,
C12: 13, C13: 13, C14: 12, C15: 18, C16: 19, C17: 22, 7 for the results printed from source 13 and 2 for
the criterion printed from source 14, plus the caveats common to 01, 02 and 05,
to 06 and 07, to 08 and 09, and to C10–C14). The main ones:

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
  theorems, the one-scale classification and the orbit and focusing theorems,
  and sources C10–C14 the two-ring contraction, the squarefree extension, the
  smooth-curve classification and its arithmetic, group, coefficient-algebra
  and projective consequences, and source C15 its geometric package (the
  logarithmic comparison and its consequences), as their most distinctive
  contributions. None is certified new. First-order definability of `Z` in `Oz` and its nonsaturation
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
- **Elliptic curves.** Source 05's separated-power method does not reach
  `y² = x³ + ax + b` with `a ≠ 0`; that stays a boundary of its proof. Sources
  C10–C14 settle the equation by a different certificate (Corollary 16.9); they
  do not list or bound its ordinary solutions.
- **Curve and differential rigidity.** The question answered is this report's
  continuation question, not a literature conjecture, and nothing is claimed by
  C10–C14 about singular curves in general (source C16 now supplies them), affine
  varieties of higher dimension or
  primitive, non-unimodular tuples. Coefficients must be constants; nothing is
  claimed over `No`, `No[i]` or the valuation ring, where nonconstant points
  exist. The Euler derivations are local, not canonical and not the
  Berarducci–Mantova derivation; no spectrum of a proper class is formed.
  Global generation or symmetric detection is sufficient, not necessary, and
  nothing is inferred from nefness, bigness, general type or the absence of
  rational curves. The group-point splitting is not an algebraic splitting; the
  reduced-base principle is not faithful flatness; the congruence criterion is
  an algorithm only once a parametrization is supplied; C14's `Γ = Z` remark does
  not assert non-normality, and a non-normality example is not a failed lift.
  Van den Dries (1981) was not read in full: C11 and C14 consulted its record
  and abstract only, the placement check confirmed the abstract, and no
  comparison or priority is claimed. The characteristic-2
  telescoping is not claimed as new, and the finite-polynomial case of
  positive-genus rigidity is standard.
- **Logarithmic forms (source C15).** Tangent separation is sufficient, not claimed
  necessary. Nothing is claimed about varieties of general type (positivity of the
  canonical bundle need not supply separating symmetric differentials), and no
  equivalence between rigidity and the absence of nonconstant maps from `𝔸¹` is
  established or may be inferred from the curve classification. No classification
  of singular curves by C15 (source C16 now supplies one); `𝒜_𝕜(Γ)` is not assumed normal and a normalization lift is not
  available; quasi-finiteness is essential (`𝔸¹ × G → G`); no morphism between the
  spectra of the ring and the valuation ring is asserted. No enumeration, finiteness
  or height bound for integral points, nothing on Siegel's theorem or Hilbert's tenth
  problem, and affine integer points are not projective integer points. Van den Dries
  (1981) was inspected through its record and abstract only. Its 2,820 finite cases do
  not verify the infinite-support or scheme-theoretic assertions, and its proof audit
  is author-side, not a referee report.
- **Singular curves (source C16).** Characteristic zero, constant coefficients,
  geometric integrality, dimension one and finite type are required; Theorem 17.36 needs
  an algebraically closed field, and in positive characteristic only the one-place
  obstruction is proved (no genus-zero conclusion). The criterion is about existence:
  no lifting of points through the normalization (Question 21.23), no classification of
  real singular fibers or of the isolated real node (Question 21.24), no description of
  fibers or images of `ct` (Question 21.29). The derivative-order bound is not claimed
  optimal, and no algorithm for conductors or differentials is given. Ordinary
  integer-point existence is not decided and no integer points are enumerated; nothing
  is claimed over the Hahn field, `No` or `No[i]`, or in higher dimension. Not refereed
  and not Lean-checked; priority is not asserted, "complete criterion" refers only to
  the stated class, and van den Dries (1981) was compared by record and abstract only.
  Seidenberg's identity, the smooth theorem, normalization, Riemann–Roch and
  Riemann–Hurwitz are credited. Its 113,940 finite assertions are regression checks, not
  proofs.
- **Constant discriminants (source C17).** It does not show that every finite étale
  `𝒜_𝕜(Γ)`-algebra is constant (surjectivity of `𝖢_𝖡 → 𝖡/Π𝖡` is open, Question 21.31),
  assumes no global primitive element, and does not extend the unit theorem to
  `𝔬 + Π_𝕜(Γ)` (Question 21.32); a nonzero constant discriminant is kept apart from a
  unit one. No factorization, prime or birthday result, no large cardinals, no preferred
  surreal derivation (the Euler derivations act on coefficients, not as `d/dX`). The
  exponent `2s` is not claimed optimal; the Galois statement depends on the chosen
  coefficient field (the rational Galois group is not kept after extending to `R`); the
  critical-point theorem is not a conjugacy. The main theorems are false without
  one-sided support, characteristic zero or a nonzero discriminant, and the matrix
  theorem without normality; finite free and reduced does not suffice for the unit
  theorem. The `𝕜[Y]` case (the Stack Exchange question of Oblomov) and its multivariable
  form are not claimed new. The coefficient test is not an algorithm for arbitrary
  presentations. Its 1,126 finite assertions do not prove the arbitrary-support
  theorems; no Lean, no refereeing, no novelty certification; the repository comparison
  was focused and partly through excerpts; its questions are not a certified catalogue.
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
- **Formalization.** The proposed Lean modules (Section 20.2) are proposals, as is
  source C17's implementation order (Section 19.4.11).
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
  its GCD hypothesis (`bst:hyp:gcd`) is about the rank-one ring with support
  bounded in both directions over an algebraically closed coefficient field.
  Its units are nonzero monomials; Theorem 4.10 concerns `Oz`, whose units
  are `±1`. These are different rings, with different support restrictions.
- [`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/)
  prints source 05's universal set-sized quotient theorem with its proof; its
  preliminaries overlap Sections 2–4 here. Its manuscript 13 supplies the
  Gaussian fiber and étale norm results printed here once (Section 6), and
  its manuscript 16 (files `16-fresh-scale-`) proves the fresh-scale image-gap
  theorem generalizing Example 19.2 and Proposition 19.4. Its manuscript 14
  (files `14-arithmetic-tensors-`) proves the direction criterion printed here
  as Corollary 15.55; its `osq:tn:thm:duals`, `osq:tn:thm:syzygy`(iii) and
  `osq:tn:thm:hom` contain the rank-two case of Theorem 15.7, the intersection
  of Example 15.27 for monomial `t`, and the scalar step of Theorem 15.11;
  `osq:prop:fractions`(iii) gives `M⁻¹Oz = No`, and `osq:cor:smallprimes` agrees
  with the residue field `Q` of `Oz_Π` (Proposition 15.40). Its class-valued
  derivations `Oz → Π` (`osq:prop:classder`) have the support inclusion
  `∂(𝒜) ⊆ Π` of Lemma 16.2; this need not be a proper inclusion; its vanishing of derivations of the class ring into
  set-sized modules (`osq:thm:derivations`) is no conflict, since the Euler
  derivations here act on set-sized workspaces, rather than on the full class
  with a set-sized module as codomain. Its manuscript 18's canonical
  translation and rich-target theorems (`osq:or:thm:canonical`, `osq:or:thm:eta`,
  `osq:or:thm:targets`) give the normal forms `f = ct_*(f)(X − η)` and
  `f = ct_*(f)(X − η) + β` of Theorems 19.12 and 19.33 for integer-valued
  polynomials with more inputs in one ordinary-output coset than their
  degree. This differs from the constant-discriminant hypothesis;
  discreteness alone is insufficient (Remark 19.35).
- [`omnific-groups-and-lattices`](../omnific-groups-and-lattices/): its
  cusp-residue obstruction and non-elementary unipotents
  (`ogl:el:prop:cuspresidue`, `ogl:el:thm:nonel`) show that the focusing
  matrices of Lemma 15.34 lie outside `E_2(Oz)` at irrational centres and that
  the density of Corollary 15.36 needs such matrices (Remark 15.39). It also
  answers Question 21.1 for closed subgroup schemes of `GL_N`; its remark
  `ogl:alg:rem:affine` now records the smooth classification and the singular
  normalization criterion. It also retains the unresolved real arithmetic
  case: affine-line normalization, but no real normalization preimage of
  any integer point. The Gaussian existence criterion is complete under
  the stated geometric integrality hypothesis. The two geometric answers
  agree (Remark 18.7): `G_a`
  is nonrigid and the one-dimensional tori (`G_m`, `SO(2)`) are rigid; the
  commutative-group kernel of Theorem 18.6 is its unipotent kernel
  `ogl:alg:prop:bch` for commutative groups; semiabelian rigidity extends its
  torus freezing beyond linear groups; and real and complex rigidity coincide
  for smooth geometrically integral affine curves over the coefficient
  support rings, but not for groups (`SO_3`). Arithmetic existence separately
  requires the relevant ordinary point.
- [`omnific-preserving-automorphisms`](../omnific-preserving-automorphisms/):
  its Euler derivations map `ℛ_𝔬(k, Γ)` into `Π_k(Γ)` (`opa:par:prop:Euler`),
  the support inclusion used in Sections 16–17; sources C10–C14 did not cite it.
  Its batch-32 `opa:tc:thm:oztopology` (every Hahn-compatible ring topology on
  `Oz` is pulled back along `ct` from `Z`) shows that the non-Hausdorff
  congruence topologies after (3.3) are forced (status note there).
- [`hahn-tate-uniformization`](../../surcomplex/hahn-tate-uniformization/): its
  Tate points are field points of curves with nonconstant `j`-invariant, outside
  the constant-coefficient hypothesis of Section 17; like Remark 17.24 and
  Section 18.5 they show that field points and varying coefficients are not
  constrained by the ring rigidity here.
- [`surcomplex-field-automorphisms`](../../surcomplex/surcomplex-field-automorphisms/)
  constructs the phase twists and the dilations `S_a`; source 06 credits it and
  proves that the twist of Lemma 13.9 preserves `Oz[i]`. Its batch-32
  `saut:fs:thm:main-count` (valued, summation- and `Oz[i]`-preserving
  involutions fall into `2^𝔠` conjugacy types with nonisomorphic fixed fields)
  is recorded as negative information on Question 21.10.
- [`holonomic-rigidity-for-entire-hahn-functions`](../../surcomplex/holonomic-rigidity-for-entire-hahn-functions/):
  its factorial floor profile (`hol:fh:thm:floor`) is a case of Theorem 2.7
  (note after that theorem), and its undecidability inside a rigid class of functional
  equations (`hol:pc:cor:undecidable`) reduces through `ct` and MRDP as Corollary 5.2
  does (note after that corollary).
- [`entire-functions-at-arbitrary-rank`](../../surcomplex/entire-functions-at-arbitrary-rank/):
  `ent:as:thm:sampling` and `ent:as:thm:integer` treat entire series over a
  fixed workspace, the case excluded by the non-claim on polynomial lifting
  (Appendix B; pointer added there in batch 32).
- [`single-dilation-hahn-support`](../../surcomplex/single-dilation-hahn-support/)
  defines the coefficient field and constant coefficient of a full Hahn
  field of characteristic zero from the named exponent dilation `S_2`,
  with a nonzero, 2-divisible exponent group. Theorems 13.2 and 13.4 recover
  them from the pure ring `Oz` instead.
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

The current build gives 225 pages with no errors, warnings, undefined
references, multiply defined labels or overfull boxes. The batch-32
cross-report notes (after Theorem 2.7 and (3.3), after Question 21.10 and in the
non-claim on polynomial lifting) are unnumbered and changed no label number
(compared in the `.aux` files against a build of the text before them). The text before
source C17 was integrated built to 202 pages with the same zero counts, and every one of
its 942 `.aux` label entries has the same number in the present build. The earlier combined
C16/projective review built to 198 pages. (The text at `4253328`, before source C16
was integrated, built to 178 pages with the same MiKTeX installation and the same zero
counts, and every label it defines has the same number in the present build. The text
at `6f47cf9`, before source
C15 was integrated, built to 162 pages with the same MiKTeX installation and the
same zero counts, and every label it defines has the same number in the present
build. Before the merge that joined the
reviews of Sections 12, 13 and 15.1–15.4 to Sections 16–18, the text at
`ac54217` built to 157 pages and the reviewed text at `3d40856`, without
Sections 16–18, to 122. The text at `c6359e4`, before
Sections 16–18, built to 118 pages with the same MiKTeX installation, with the
same zero counts; the text at `a4dcb91`, before Section 15, built to 87 pages,
and the PDF committed then had 86 pages.) As in the text at `c6359e4`, the
sources note of the title page runs onto the second page. The Makefiles of
sources C10, C11 and C14 and the build scripts of C12 (`.sh`, `.ps1`) compile
the delivered `article.tex` in their own directory and run the delivered
`verify.py` or `verification.py`; source C13's `build.sh` compiles its delivered
`omnific_differential_rigidity.tex`. None of those files is shipped under those
names, and none of these scripts builds this report. Source C15's
`code/15-logarithmic-rigidity-build.sh` and `.ps1` change to their own directory
(`code/`) and run `pdflatex` on an `article.tex` there, which does not exist; they do
not build this report either, and its shipped build record and proof audit describe
its own article and file names (`code/verify.py`, `data/verification.json`). Source
C16's `code/16-singular-curves-build.sh` changes to its own directory (`code/`) and runs
`latexmk` or `pdflatex` on an `article.tex` there, which does not exist; it does not
build this report, and its shipped source audit and build record describe its own
article and file names (`verify.py`, `verification.json`, `SHA256SUMS.txt`, which is not
shipped). Source C17's `code/17-discriminant-rigidity-build.sh` changes to its own
directory (`code/`), creates `build/` there and runs `latexmk` on an `article.tex` that
does not exist, so it fails without building this report; in its delivered layout it
would overwrite `article.pdf` and rerun `verify.py --output verification.json` in place.
Do not run it here. Its shipped audits and build report describe its own article and
file names (`verify.py`, `verification.json`, `BUILD_REPORT.json`). The shipped source audits
of sources C10–C14 and the build records of C10, C11 and C14 describe their own
articles and file names (`verify.py`, `verification.json`,
`verification_report.json`, `verify_certificates.py`), shipped here with the
prefixes `10-` to `14-`. Source 08's `code/08-fractions-Makefile` and
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

The checks of sources 01, 02, 05, 06, 08, 09, C10, C12, C13 and C14 need
Python 3.9 or later (3.10 for sources 06, 08, C10, C13 and C14) and SymPy (tested
with 1.14.0); those of sources 07 and C11 need Python 3.10 or later and the
standard library only. From this directory:

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
python code/10-curve-rigidity-verify.py --output <scratch>/10-verification.json
python code/11-curve-abelian-rigidity-verify.py --output <scratch>/11-verification.json
python code/12-curve-logarithmic-verification.py --output <scratch>/12-verification_report.json
python code/13-differential-rigidity-verify_certificates.py
cp code/14-hahn-differential-rigidity-verify.py <scratch>/verify.py
python <scratch>/verify.py
python code/15-logarithmic-rigidity-verify.py
python code/15-logarithmic-rigidity-verify.py --output <scratch>/15-verification.json
python -m pip install -r data/16-singular-curves-requirements.txt
python code/16-singular-curves-verify.py
python code/16-singular-curves-verify.py --output <scratch>/16-verification.json
python -m pip install -r data/17-discriminant-rigidity-requirements.txt
python code/17-discriminant-rigidity-verify.py --output <scratch>/17-verification.json
```

The safest course for sources C10, C11, C12 and C14 is to run copies of the
scripts in a scratch directory, as these reports were checked; with `--output`
pointing outside this directory, as above, the first three also leave `code/`
unchanged. Their scripts **write** reports next to themselves by default
(`verification.json` for C10 and C11, `verification_report.json` for C12), and
source C14's script **always** writes `verification.json` next to itself, so it
must be run on a copy. Source C11's script also prints its report. Source C13's
script prints its report and writes a file only to a path given with
`--output`; its delivered README's rerun line `--output verification_report.txt`
would overwrite a report file, so do not point it at the shipped record
`data/13-differential-rigidity-verification_report.txt`.

Source C15's script prints its report and writes a file only to a path given with
`--output`; do not point that option at the shipped record
`data/15-logarithmic-rigidity-verification.json`. It needs Python 3.9 or later and
SymPy.

Source C16's script likewise prints its report and writes a file only to a path given
with `--output`; do not point that option at the shipped record
`data/16-singular-curves-verification.json` (its delivered README's line
`python verify.py --output verification.json` would overwrite a file of that name in the
working directory). It needs Python 3.10 or later and SymPy (`sympy==1.14.0` pinned).

Source C17's script **writes** its report: to the path given with `--output`, and without
it to `verification.json` in the current working directory; it also prints the report.
Always pass `--output` with a path outside this directory, as above, and never point it
at the shipped record `data/17-discriminant-rigidity-verification.json`. It needs Python
3.10 or later and SymPy (`sympy==1.14.0` pinned); the seed 20260923 is fixed.

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

When Sections 16–18 were written, the five scripts of sources C10–C14 passed on
copies in a scratch directory with Python 3.14.4 and SymPy 1.14.0. Source C10's
3,991 assertions in eight groups (the cubic certificate, squarefree certificates
for eleven polynomials and `2 ≤ m ≤ 8`, the degree obstruction for
`2 ≤ d, m ≤ 30`, parametrizations, binomial coefficients, the constant-term
boundary, finite-support Euler laws in lexicographic ranks one to three, and
clearing) gave a report differing from its record only in the Python version, run
time and timestamp. Source C11's 13,049 assertions in 19 categories (over `Q` and
`F_2`: the cubic and divisibility identities, Euler laws, the characteristic-two
tail, the discretely ordered ring, binomial coefficients, the dual-number example)
gave a report identical to its record. Source C12's 49 checks (35 differential
certificates, the cubic and singular identities, the elliptic root coefficients,
400 finite-support trials) and source C14's 3,440 assertions in five groups
(symbolic, finite series, degrees, arithmetic including the congruence example,
characteristic two) differ from their records only in the Python version (3.13.5
there). Source C13's 12,874 assertions in 17 checks printed a report identical to
its record except for the Python version. The identities and expansions printed
in Sections 16–18 were checked separately with SymPy.

When Section 18.6 was written, source C15's script passed on a copy in a scratch
directory with Python 3.14.4 and SymPy 1.14.0: seven groups and 2,820 cases (the
universal cubic identity and its case `Δ₀ = 23`, 49 differentiated superelliptic
certificates, 2,401 valuation-margin samples, the cusp and node families, 300 finite
rank-two Hahn examples, 64 characteristic-two telescoping checks with the partial
derivatives, and the valuation-ring binomial series). Run without `--output` it only
printed; the report written with `--output` differs from the shipped record only in
the recorded Python version (3.13.5 there).

When Section 17.6 was written, source C16's script passed on a copy in a scratch
directory with Python 3.14.4 and SymPy 1.14.0: 113,940 assertions in 28 groups, with the
same group counts as the shipped record (264 rational and 8 symbolic checks of
Seidenberg's identity, 1,493 finite Hahn checks, 200 rank-two comparisons, 36,071
superelliptic multiplicity patterns with three checks each and 21 normalization
identities, the elliptic and conductor identities, the node, cusp, acnode and real
parametrizations, and 3,696 derivative-order checks). The report written with `--output`
differs from the shipped record only in the recorded Python version (3.13.5 there) and
the run time. The parametrizations and identities printed in Section 17.6 were checked
separately with SymPy.

When Section 19.4 was written, source C17's script passed on a copy in a scratch
directory with Python 3.14.4 and SymPy 1.14.0, with `--output` in that directory: 1,126
assertions in 13 groups (96 translation, 20 discriminant, 20 factorization, 420
velocity-certificate, 510 velocity-symmetry, 6 velocity-trace, 2 quadratic-certificate,
8 resultant, 18 critical, 9 matrix, 8 characteristic-`p`, 7 counterexample and 2 example
checks), the same group counts as the shipped record. The report differs from the record
only in the recorded Python version (3.13.5 there). These checks cover finite identities
and examples only, not the arbitrary-support theorems.


## Positive-exponent correction after the power-rigidity merge

The incoming formalization `365bea6` exposes a missing hypothesis in
`odg:rem:powers` (alias `odg:cor:powers`). The remark now states positive
ordinary `m,n` and a nonzero ordinary integer level. Its gcd reduction uses
positive quotient exponents, and it records the checked counterexample
`ω^0 − 0² = 1` with `gcd(0,2) = 2`. The closing sentence now limits the
separated-power theorem to `m,n ≥ 2`; exponent one admits the family
`y = x^m − c`. The question-status summary is aligned. The corrected gcd
statement and zero-exponent counterexample are proved in Lean; the coprime
separated theorem remains pending there. The remark changes, but all 244
standard theorem/lemma/proposition/corollary statements are unchanged.
