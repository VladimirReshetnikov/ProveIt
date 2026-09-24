# Cofinality, Factorization and Scalar Extension for Entire Hahn Functions at Arbitrary Rank

**A merged research report, 160 pages, from eight manuscripts.** Everything in
this directory other than `article.tex`, `article.pdf` and this README is
preserved source material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled 160-page report
README.md     this guide
07-scale-moderate-interpolation-SOURCE_AUDIT.md   source 4: provenance, scope and novelty audit
09-prime-spectra-SOURCE_AUDIT.md                  source 6: provenance, claim boundaries and literature
10-entire-rectification-SOURCE_AUDIT.md           source 7: provenance, literature, proposed contributions, non-claims
11-arithmetic-sampling-SOURCE_AUDIT.md            source 11 (the eighth): repository snapshot, literature, proposed contributions, checks
code/         the eight source verification programs, unmodified, and five delivered build helpers
data/         the recorded verification runs, the sources' build reports, source 4's
              package manifest, source 5's research audit, source 7's and source 11's
              requirements files, and source 11's artifact manifest
```

Every label in `article.tex` carries the prefix `ent:`. Material added from
the fourth source carries `ent:sm:`, from the fifth `ent:mv:`, from the sixth
`ent:ps:`, from the seventh `ent:rc:`, and from the eighth `ent:as:`. File
names keep the local numbers they were placed under: `06` is the first source,
`03` the second, `01` the third, `07` the fourth, `08` the fifth, `09` the
sixth, `10` the seventh and `11` the eighth. Because this report already has a
file prefix `09` of its own, the eighth manuscript (batch 32, manuscript 09) is
called **source 11** after its file prefix, in the article and here.

| file prefix | source | pinned commit | contribution |
|---|---|---|---|
| `06-cofinality-bezout-trichotomy` | 1 | `4896a28` | trichotomy, non-Bézout pair |
| `03-cofinality-and-scalar-extension` | 2 | `aa84627` | scalar-extension package |
| `01-exact-jet-image` | 3 | `a3124af` | exact image of the infinite jet map |
| `07-scale-moderate-interpolation` | 4 | `0097304` | second proof of the image; ideal theory above the product |
| `08-multivariate-extension` | 5 | `4cf691c` | several variables: exact extension domains |
| `09-prime-spectra` | 6 | `465a54b` | all prime ideals above a one-simple-node product; cofinal splitting |
| `10-entire-rectification` | 7 | `71e9606` | several variables: rectification dichotomy, reduction obstruction, fat-point ideals |
| `11-arithmetic-sampling` | 8 (source 11) | `343dc2c` | ordinary points: coefficientwise division, faithful flatness over `k[X]`, arithmetic sampling, exceptional ideals, halting barrier |

The sixth source's files are `code/09-prime-spectra-verify_finite.py`,
`code/09-prime-spectra-build.sh`, `data/09-prime-spectra-verification_results.json`,
`data/09-prime-spectra-BUILD_REPORT.json` and `09-prime-spectra-SOURCE_AUDIT.md`.
Its own article (`prime_spectra_at_surreal_infinity.tex`, 28 pages), PDF and
delivery README are not shipped; its build helper and build report refer to
them.

The seventh source's files are `code/10-entire-rectification-verify.py`,
`code/10-entire-rectification-build.sh`,
`data/10-entire-rectification-verification-results.json`,
`data/10-entire-rectification-BUILD_REPORT.json`,
`data/10-entire-rectification-requirements.txt` and
`10-entire-rectification-SOURCE_AUDIT.md`. Its own article
(`entire_rectification.tex`, 25 pages), PDF and delivery README are not
shipped; its build helper and build report refer to them, and its source
audit refers to "Sections 10–11 of the article" (its provenance and proof
audit), which are summarized in Section 11.15 and Appendices A–C here.

Source 11's files are `code/11-arithmetic-sampling-verify.py` (delivered as
`verify.py`), `code/11-arithmetic-sampling-build.py` (`build.py`),
`data/11-arithmetic-sampling-verification.json` (`verification.json`),
`data/11-arithmetic-sampling-build_report.json` (`build_report.json`),
`data/11-arithmetic-sampling-requirements.txt` (`requirements.txt`),
`data/11-arithmetic-sampling-ARTIFACT_MANIFEST.json` (`ARTIFACT_MANIFEST.json`)
and `11-arithmetic-sampling-SOURCE_AUDIT.md` (`SOURCE_AUDIT.md`). Its own
article (`arithmetic_sampling.tex`, 24 pages), PDF and delivery README are not
shipped. The audit, the manifest and the build report use the delivery names;
the manifest hashes nine files, of which the six shipped here match and three
(the article, its PDF and the delivery README) are not shipped, and the build
report hashes the unshipped article and PDF.

## What the report is

Two independently written manuscripts, both dated 21 September 2026, each
written against its own pinned snapshot of this repository, studied the same
object: ordinary power series `sum a_n Z^n` over a **fixed** Hahn field
`K_Gamma = C((t^Gamma))` with `Gamma` a set-sized divisible ordered abelian
group of arbitrary valuation rank, where *entire* means strongly
Hahn-summable at every point of that one field. Both explicitly disclaim all
of `No[i]`. This report is their **union**, not a selection. They proved the
same engine — coefficient criterion, cofinality dichotomy, support-controlled
preparation, root counts, genus-zero canonical product, factorization by
zeros, change-of-workspace criterion — and each is printed **once**; their two
payloads, a ring-theoretic trichotomy and a scalar-extension package, are both
kept in full.

A **third manuscript** (22 September 2026, pinned at `a3124af`) was written
against the merged report and answered the question it had recorded as open
under the heading *The missing image of the infinite jet map*, now Question
16.1, marked answered. Its contribution is Theorem 1.6, proved in Section 8.
Its `rho_n` was a value-group radius and its `a_(n,j)` a field point, the
reverse of this report; everything taken from it was rewritten.

A **fourth manuscript** (22 September 2026, pinned at `0097304`) set out to
answer the same question. At its pin the question was open, so its claim to
resolve it was accurate there; it is **stale now**, because the third source
had been merged at `de84d8b`, about an hour after that pin. It is recorded as
an **independent second proof** of Theorems 8.6, 8.7 and 8.26 under the same
hypotheses, not as their source. Its sufficiency construction, by cardinal
corrections with an explicit truncation bound, is kept as a marked second
route (Section 8.5). Its genuinely new results are the finite-generator and
membership criteria, the exact threshold for paired zeros, and the complete
list of maximal ideals above a one-node-per-shell product, with its topology,
residue-field type and boundary coordinate (Sections 8.7 and 8.9). Two of its
letters are **swapped** with this report's: its `C_n` is our convex subgroup
`H_n`, and its `H_n` is a correction, our `C_n`. Several more shift. The
conversion tables are in Section 2.5.

A **fifth manuscript** (22 September 2026, pinned at `4cf691c`, after the
third source was merged) answers the scalar-extension clause of Question 16.5
(`ent:q:several`), and only that clause. It is the new Section 11, which also
absorbs the finite-variable criteria formerly in Appendix B; their labels
`ent:app:multivariate`, `ent:thm:multi-criterion` and `ent:thm:multi-unit`
are kept, and the appendices after it moved up one letter (checks are now
Appendix B, the source ledger Appendix C).

A **sixth manuscript**, *Prime Spectra at Surreal Infinity* (September 2026,
pinned at `465a54b`, after the fifth source was merged; this directory is
identical at that pin and at the base of the merge), answers the "prime
ideals" clause of Question 16.4 (`ent:q:spectrum`) for one **simple** node
per shell, and the non-claim at the end of Section 8.9 ("Prime ideals below
these maximal ideals are not classified"), which is kept as written with a
re-scoping pointer. It is the new **Section 12** (`ent:ps:`), inserted after
Section 11, so the later sections moved down one number: assembly is now
Section 13, examples 14, relation to the collection 15, scope and questions
16, conclusion 17 (questions are 16.1–16.11). It credits the quotient
(Theorem 8.7, Corollary 8.13) and the maximal ideals (Theorems 8.33, 8.36,
8.37) as already here; its reproof of the simple-node interpolation theorem is
the first route of Theorem 8.6 specialized, so it is printed once, by
citation (Remark 12.2). It states that its ultraproduct and valuation-domain
mechanism is classical (Finocchiaro–Frisch–Windisch; the Stacks Project).

A **seventh manuscript**, *Entire Automorphisms at Surreal Scales: An
order-unit dichotomy, omnific rectification, and exact fat-point ideals*
(23 September 2026, pinned at `71e9606`, after the sixth source was merged;
this directory is identical at that pin and at the base of the merge), asks
when an infinite configuration of points of `K^d` can be carried into a
coordinate line by an entire automorphism, and what the ideals of points with
multiplicities are once it has been. It presented this as a problem different
from the report's; it is in fact a partial answer to the ideal-theory and
interpolation clauses of Question 16.5 (`ent:q:several`), and is placed
accordingly. It is **Sections 11.9–11.15** (`ent:rc:`), the closing
subsections of Section 11, chosen so that **no existing section, theorem,
question or equation number changed**: its items are numbered 11.33–11.70,
its displayed equations (R1)–(R29), and its five questions 16.12–16.16. Its
analytic tools duplicate this report and are printed once, by citation: its
criterion is Theorem 11.3, its products and division are Theorem 7.3,
Lemma 6.4, Corollary 7.5 and Proposition 8.8, its countability lemma is
Lemma 7.2, its separated scales are Lemma 8.1, and its interpolation theorem
is a special case of Theorems 8.6 and 9.2 (its explicit series is kept as a
second proof of Lemma 11.44). Its reduction theorem generalizes
`hol:cf:lem:reduction` of the holonomic-rigidity report and this report's
Lemma 8.4 and Theorem 4.1 argument, which it did not cite; the merge credits
them.

An **eighth manuscript**, source 11, *Arithmetic Sampling in Surreal Hahn
Fields: Entire rigidity, coefficientwise algebraic division, omnific
exceptional loci, and a computability barrier* (23 September 2026, 24 pages,
batch 32 manuscript 09, pinned at `343dc2c`, after the seventh source was
merged; this directory is identical at that pin and at the base of the merge),
asks what happens when arithmetic values are prescribed at **ordinary**
coefficient-field points of `K^d`, rather than along escaping sequences. It
presented that as a question different from the report's; it is a partial
answer to the ideal-theory clause of Question 16.5 (`ent:q:several`) and is
placed accordingly, as **Sections 11.16–11.26** (`ent:as:`), the last
subsections of Section 11, after the seventh source's, so that **no existing
section, theorem, question or equation number changed**: its items are
numbered 11.71–11.111, its displayed equations (S1)–(S25), and its ten
questions 16.17–16.26. See the section *Source 11* below.

## Source 11 (batch 32): Arithmetic Sampling in Surreal Hahn Fields

| | |
|---|---|
| manuscript | batch 32, manuscript 09; archive `arithmetic_sampling_surreal` (delivered in `aa268a4`, placed in `7d04483`); main file `arithmetic_sampling.tex`, 24 pages, 23 September 2026 |
| title | *Arithmetic Sampling in Surreal Hahn Fields: Entire rigidity, coefficientwise algebraic division, omnific exceptional loci, and a computability barrier* |
| pin | `343dc2c471212bb9b53ff4623bace2e1943f255b` (this directory unchanged from the pin to the merge base) |
| contributes | Sections 11.16–11.26 (`ent:as:`, 87 labels), items 11.71–11.111, equations (S1)–(S25), Questions 16.17–16.26 |
| answers | part of the ideal-theory clause of Question 16.5 (ideals extended from `k[X]`) |

**Placement.** The material is the last eleven subsections of Section 11, after
the seventh source's, not a new section, so that no existing section, theorem,
question or equation number changes; its displayed equations are numbered (S1),
(S2), … for the same reason. Section 11 already works without divisibility,
which source 11 needs; its standing hypotheses are Convention 11.71 (`k = R` or
`C`, any `Gamma`, including `0`).

**Renamed symbols** (full table in Section 2.5, with the tempting false
readings): its `D` (`Z` or `Z[i]`) is `Z_k` (our `D` is a divisor); its
omnific ring `A = D + Pi` is `Oz_K` (our `A_Gamma` is the Hahn algebra
`C[X]((t^Gamma))`, and `A` a Bézout cofactor); its `B = k + Pi` is the seventh
source's `K^{<=0}`; its `Pi` is `Pi_K` (not the class `Pi`, not the shell
factors `Pi_n`); its scale `gamma`, weight `rho` and bound `beta` are `eta`,
`gamma` and `b` (our `rho` is a node); its `p_gamma(F)` is `p_eta(F)`
(sans-serif), its `P_B(F)` is `F_{<=0}`, its `R_0` is `k[X]`, its matrices
`M`, `H` are `M`, `N` (bold) and its affine `H` is `L` (our `H` is a convex
subgroup) with new variables `Y` for its `Z`, its `H_F` and `D_0` are `gcd_+(F)` and `n_0`, its `J_r(F)` is
`I_{+,m}(F)`, its `Delta_j` is the forward difference `nabla_j` (our `Delta`
is a larger value group), its `I(S)` and `V_k(I)` are `I_k(S)` and `V_k(I)`
(blackboard V), its machine `M` is `M` (typewriter), and its examples `L`, `P`,
`T` are `F_loc`, `P_esc`, `Theta`. No normalization changes: valuations have
the same sign as ours.

**Printed once.** Its locally finite families lemma is Lemma 11.2(a); its
entire coefficient criterion is Theorem 11.3, already proved for any trivially
valued field and any group, so its claim to remove divisibility adds nothing;
its cofinality dichotomy is Corollary 3.3 with the last clause of Theorem 11.3
and Proposition 11.4; its full-class corollary is Corollary 10.12 and
Proposition 11.32 (its short route is kept in Remark 11.109). For divisible
`Gamma` its affine changes (Proposition 11.74) are in Lemma 11.40 and its
ordinary fibres (Corollary 11.85) are the one-point case of Corollary 11.63.

**Merge additions**, marked "the merge's" in the article: Corollary 11.92
(vanishing ideals of ordinary point sets and, over `C`, of algebraic sets, via
the Nullstellensatz); the identification of `p_eta` with the coefficients
`P_eta` of the Hahn algebra and `P_(n,eta)` of Theorem 11.27; the remark that
`E_d ⊆ k[X]((t^Gamma))`; the comparisons after Corollary 11.85, Theorem 11.94
and Corollary 11.95 (set-sized-quotients report) and at the end of Section 11.21
(the fifth source's Theorems 11.27–11.28); the last paragraph of Section 11.24;
the note after Question 16.17 (in one variable `K[Z] -> E` is faithfully flat);
the status note on Question 16.5 and the related notes on Questions 16.2 and
16.7; the abstract, the eighth notation table (Section 2.5), and the paragraphs in
Sections 1.3, 1.4, 11 (head), 11.8, 13, 15, 16.3, 16.4, 16.5, 17 and
Appendices A–C.

**Verification.** `code/11-arithmetic-sampling-verify.py`, rerun on a copy:
8,774 exact assertions in ten groups, seed 20260923, all pass, identical to the
delivered record except the Python version. The mathematics was re-read for
this merge; no false statement was found. The finite checks prove no infinite
theorem (Appendix B, Suite H).

## What the report claims

Write `cf(Gamma)` for the cofinality of the value group as an ordered set,
and call `delta > 0` an **order unit** when its positive integer multiples
are cofinal in `Gamma`.

**1. The trichotomy (Theorem 1.5).** For `Gamma != 0`, the entire ring
`E_Gamma` is a GCD domain with units exactly `K_Gamma^times`, and exactly one
of:

| Value group | Entire series | Ideal structure |
|---|---|---|
| `cf(Gamma) > aleph_0` | only polynomials | PID |
| an order unit exists | nonpolynomial series exist | Bézout, non-Noetherian, full Hermite interpolation |
| `cf(Gamma) = aleph_0`, no order unit | nonpolynomial series exist | GCD but **not** Bézout |

For `Gamma = 0`, strong Hahn summability gives `E_0 = C[Z]`.

In the third case, with `gamma_(n+1)` exceeding every finite multiple of
`gamma_n` and cofinal, the canonical products with roots
`rho_n = t^(-gamma_n)` and `sigma_n = t^(-gamma_n) + t^(gamma_(n+1))` have
**disjoint simple zero sets and gcd 1, yet generate a proper ideal**
(Theorem 8.29). Section 4 makes the middle case **sharp**: a nonconstant
valuation-restricted series is invertible in `T_Gamma` if and only if its
least coefficient gap is a positive order unit (Theorem 4.1).

**2. The exact image of the infinite jet map (Theorem 1.6).** Group the nodes
of an infinite radially finite divisor `D` into valuation shells of radii
`gamma_1 < gamma_2 < ...`, let `R_n` be the finite Hermite polynomial of shell
`n` in the normalized coordinate, and let `V_n` be the valuation ring that
kills the Archimedean scale of `gamma_n`. An entire function realizing all
the prescribed jets exists **if and only if** `R_n` has coefficients in `V_n`
for all sufficiently large `n` (Theorem 8.6), with no bound on nodes per
shell, jet orders or scale exponents. So `E_Gamma / (P_D)` is an algebraic
restricted product of finite shell algebras (Theorem 8.7), and
`A P_D + B F = 1` is solvable exactly when `F` is nonzero at every node with
eventually `V_n`-bounded values (Theorem 8.26). Two independent sufficiency
proofs are printed: the sequential one of the third source and the cardinal
one of the fourth (Lemmas 8.17–8.19, truncation bound Corollary 8.20).
Without an order unit the restriction never disappears (Corollary 8.16). The
restricted product is an algebraic union, **not** a topological or adelic
object.

**3. Ideals and maximal ideals above a canonical product (fourth source).**
- `(P_D, G_1, ..., G_s) = E` exactly when at every node some `G_l` is
  nonzero and, on late shells, some `G_l` has value valuation in `H_n`,
  equivalently a gcd condition over the residue field, residue collisions
  allowed (Theorem 8.27). For one simple node per shell, membership of an
  arbitrary `F` in `(P_D, G)` is decided by the ratios `F/G` at the nodes
  (Corollary 8.28).
- For the paired products with `sigma_n = rho_n + t^(theta_n)`, and no
  Archimedean domination assumed, the pair generates the unit ideal **iff**
  `theta_n` lies in `H_n` eventually (Theorem 8.30); Theorem 8.29 is the
  case `theta_n = gamma_(n+1)`.
- For one node per shell, **any multiplicities**, the maximal ideals
  containing `P_D` are exactly the evaluation ideals and one ideal
  `M_U` per nonprincipal ultrafilter, with residue field
  `prod_U C((t^(H_n)))` (Theorem 8.36; Theorem 8.33 is the simple-node
  construction). The maximal spectrum of `E/(P_D)` is homeomorphic to
  `beta N` (Theorem 8.37). For the paired example the maximal ideals
  containing both functions are exactly the `M_U` with
  `{n : theta_n not in H_n}` in `U` (Corollary 8.38). The residue fields are
  algebraically closed (real closed over `R`) (Corollary 8.39), and `Z`
  maps to a transcendental coordinate (Proposition 8.40, a Henriksen
  Theorem 5 analogue, not claimed as a new phenomenon).
- All of Section 8's image, quotient, Bézout and ideal statements also hold
  over `R((t^Gamma))`, without algebraic closedness (Proposition 8.42,
  Remark 8.43).

**4. The scalar-extension package (Theorem 1.7).** For any ordered-group
extension of nonzero divisible groups `Gamma` inside `Delta`, *every* nonpolynomial entire series over
`K_Gamma` has the **same** exact strong evaluation domain in `K_Delta`: the
valuation ring `D_(Gamma,Delta)` of `v_Delta` coarsened by the convex hull
`H` of `Gamma`, with residue field `C((t^H))`. Entireness survives exactly
for cofinal extensions; no new zeros appear; on a noncofinal extension no
alternative entire series agrees with the old one even on `C`; and `Gamma`,
the slopes `v(a_n)/n` for `n >= 1` with `a_n != 0` and the negated
valuations of nonzero zeros generate the same
convex subgroup.

**5. Several ordinary variables (Sections 11.1–11.8, fifth source).** Here **no
divisibility** is assumed and the coefficient field is any trivially valued
field. For a whole-family entire `F = sum a_alpha X^alpha` and a point `z`
with nonzero coordinates in the larger field, the family `(a_alpha z^alpha)`
is strongly summable **iff** the weight set
`{ sum_j alpha_j (v(z_j) + H) : a_alpha != 0 }` is well ordered in
`Delta/H` (Theorem 11.8). Infinite fibres are allowed; within the entire
category higher Hahn tails do not matter (Corollary 11.9), which corrects the
guess in Question 16.5. The one-variable domain is recovered without
divisibility (Corollary 11.10); semilinear supports give finitely many weak
inequalities (Theorem 11.15); the domain can be a nonclosed cone
(Theorem 11.17). For the separate **homogeneous-block** convention, which is
never called entire: along old-field rays the domain is `K_Delta` or
`D_(Gamma,Delta)` according as the line restriction is a polynomial
(Theorem 11.23); the polynomial-direction locus is a countable union of
projective algebraic sets with dense complement (Theorem 11.27), every proper
such union is realized when `cf(Gamma) = aleph_0` (Theorem 11.28), and in two
variables the loci are exactly the at most countable subsets of `P^1(C)`
(Corollary 11.29). The finite-variable coefficient criterion is now stated
division-free under these weaker hypotheses (Theorem 11.3); the unit criterion
(Theorem 11.5) keeps the report's standing hypotheses.

**6. Prime ideals above a one-simple-node product (Section 12, sixth
source).** Here `cf(Gamma) = aleph_0`, the coefficient field `k` is `R` or
`C`, `rho_n = t^(-gamma_n)` for a positive cofinal sequence `gamma_n`, and
`P_D = prod_n (1 - t^(gamma_n) Z)`. By Theorem 8.7 and Corollary 8.13,
`E/(P_D)` is the sequence ring `R_D = {(b_n) : b_n in V_n eventually}`
(display (68)); the sixth source's `A` is this `R_D`, not our Hahn algebra.
- **All primes (Theorem 12.9).** The primes of `R_D` are the evaluation
  ideals `e_n` and, for each nonprincipal ultrafilter `U` and each convex
  subgroup `C` of `Gamma_U = prod_U (Gamma/H_n)`, the prime `p_(U,C)`: the
  inverse image of a prime of the ultraproduct valuation domain
  `V_U = prod_U V_n` (Proposition 12.6). Parameters are unique, fibres are
  incomparable, inclusion reverses; the fibre's minimal prime is
  `p_(U,Gamma_U)` and its maximal prime `p_(U,0)` pulls back to `M_U` of
  Theorem 8.33, so the maximal ideals are those of Theorem 8.36 (recovered,
  not claimed). An entire `F` lies in `p_(U,C)` iff its node values vanish
  on a set in `U` or `[v(F(rho_n)) + H_n]_U > C` (Corollary 12.10). Local
  rings are valuation domains with value group `Gamma_U / C`, residue tower
  ending in `L_U` (Theorem 12.11). `Spec` maps onto `beta N` with the
  valuation spectra as fibres, and `Min` and `Max` are both homeomorphic to
  `beta N` (Theorem 12.13); the ring is semiprimitive (Corollary 12.15).
- **Dichotomy (Theorem 12.17).** An order unit exists iff `R_D = K^N` iff
  `R_D` is von Neumann regular iff `dim R_D = 0` iff `R_D` is Jacobson.
  Otherwise every nonprincipal fibre contains a strict chain of primes
  indexed by `(0,1)`, so `E/(P_D)` has infinite Krull dimension although
  every zero of `P_D` is simple; entire witnesses without zero node values
  separate the chain (Proposition 12.18). The quotient is claimed
  zero-dimensional in the order-unit case, **not** `E` itself.
- **Finite algebra (Theorems 12.21, 12.23, Proposition 12.24).** `R_D` is
  reduced, every finitely generated ideal is principal and projective
  (semihereditary, a Bézout ring with zero divisors), every finite matrix has
  a Smith form, `Q(R_D) = K^N`, `R_D` is integrally closed there and not
  Noetherian. So every finitely generated ideal of `E` containing `P_D` is
  `(P_D, G)` (Remark 12.22, the merge's translation).
- **Contraction under cofinal extension `Gamma ⊆ Delta` (Theorem 12.29).**
  Contraction keeps the ultrafilter and intersects convex subgroups,
  `p_(U,C') ∩ R_D^Gamma = p_(U, C' ∩ Gamma_U)`; the extensions of a prime are
  exactly an interval `C_min ⊆ C' ⊆ C_max` of convex subgroups
  (Lemma 12.28). Minimal and maximal spectra are stable (Corollary 12.31);
  unique extension holds iff `C_min = C_max`, e.g. with an order unit
  (Corollary 12.30).
- **Splitting without new zeros (Theorem 12.33, Corollaries 12.35 and
  12.37).** For `Gamma_infinity = ⊕_j Q omega^j` inside
  `Delta_Q = ⊕_{q in Q>=0} Q omega^q`, the product
  `prod_n (1 - omega^(-omega^n) Z)` keeps exactly its simple zeros
  `omega^(omega^n)`, yet one intermediate prime is the contraction of a
  chain of continuum many primes, and even an old maximal ideal has
  continuum many nonmaximal extensions; entire functions with
  `G_u(omega^(omega^n)) = omega^(-omega^(n+1+u))` separate them
  (Proposition 12.34).
- **Multiplicity (Theorem 12.40).** For `prod_n (1 - Z/rho_n)^(m_n)`, `F` is
  in the radical iff some `d` has `d ord_(rho_n) F >= m_n` for all `n`; the
  radical is `(P_D)` iff `sup m_n < infinity`, and then the prime spectrum
  is the reduced one (prime spaces and dimension only, not regularity or
  semiheredity). For unbounded `m_n` some prime contains the product but
  not `P_D`; such primes are not maximal (the merge's remark after
  Theorem 12.40, from Theorem 8.36).

**7. Rectification and fat points (Sections 11.9–11.15, seventh source).**
Here `Gamma` is divisible, the coefficient field `k` is `R` or `C`, *entire*
is whole-family entire in `d` ordinary variables, `v(p) = min_j v(p_j)`, and
`X ⊂ K^d` is **radially finite** when it meets every polydisk `v(p) >= gamma`
in finitely many points. It is **line-rectifiable** when an entire
automorphism (with entire inverse) maps it into `K × 0^(d-1)`.
- **Dichotomy (Theorem 11.35).** For `d >= 2` and `cf(Gamma) = aleph_0`:
  every radially finite set is line-rectifiable **iff** `Gamma` has an order
  unit, and then an affine map plus one triangular shear suffices
  (Proposition 11.50). The cofinality hypothesis is needed: for
  `cf(Gamma) > aleph_0` every radially finite set is finite (Lemma 11.46).
- **Without an order unit (Theorem 11.36, Corollary 11.51).** Every radially
  finite subset of `(K^{<=0})^d`, series supported in `Gamma_{<=0}`, is still
  line-rectifiable; this covers the omnific integers `Z + R((t^{Gamma<0}))`
  and Gaussian omnific integers `Z[i] + C((t^{Gamma<0}))` of a workspace
  (displays (R12)–(R13)), and sets whose radii are eventually distinct. The
  rectifying map is **not** claimed to preserve the omnific ring. The tool is a
  denominator formula for cardinal interpolation (Lemmas 11.43–11.44,
  Corollary 11.45).
- **Reduction and obstruction (Theorems 11.53, 11.57).** Along an exhaustion
  by proper convex subgroups, finitely many entire series eventually have
  integral coefficients, polynomial reductions and compatible evaluation;
  an automorphism and its inverse reduce to inverse polynomial automorphisms
  with Jacobian in `GL_d(V_H)` (Corollary 11.54). So the escaping
  infinitesimal simplices `p_n = t^(-gamma_n) u_1`, `p_n + t^(gamma_(n+1)) u_j`
  stay affinely independent under every entire automorphism at all late
  scales (Proposition 11.56): no automorphism puts them, or any cofinite
  subset, in a hyperplane.
- **Fat points (Theorems 11.37, 11.62, 11.66; Corollaries 11.63, 11.65;
  Proposition 11.67).** On a line-rectifiable configuration with bounded
  multiplicities of maximum `m̄`, the ideal of functions of order `>= m_i` at
  `p_i` is generated by `P_<|alpha|>(X_1) X'^alpha`, `|alpha| <= m̄`, and needs
  exactly `binom(m̄+d-1, d-1)` generators; simple points give the complete
  intersection `(P, X_2, ..., X_d)` with `E_d/I = E/(P)`; constant
  multiplicity gives `I^m̄`; unbounded multiplicities and `d >= 2` give an ideal
  that is **not finitely generated**, with a radical strictly smaller than the
  vanishing ideal although the zero sets agree. In dimension one these ideals
  are principal.
- **Evaluation (Corollary 11.64, the merge's).** On a line-rectifiable
  configuration the values taken by entire functions are exactly those allowed
  by Theorem 8.6 at the image nodes, and `E_d/I` is the restricted product of
  Theorem 8.7; with an order unit arbitrary values on any radially finite
  subset of `K^d` are interpolated.

**8. Arithmetic sampling at ordinary points (Sections 11.16–11.26, source
11).** Here `k = R` or `C`, `Gamma` is **any** set-sized ordered abelian group
(not divisible, possibly `0`), `K = k((t^Gamma))`, *entire* is whole-family
entire in `d` variables, `Pi_K` is the series supported in `Gamma_{<0}`,
`K^{<=0} = k + Pi_K` the polynomial-part ring, and `Oz_K = Z_k + Pi_K`, with
`Z_R = Z` and `Z_C = Z[i]`, the omnific integers of the workspace. The scale
polynomial `p_eta(F) = [t^eta] F` is an ordinary polynomial in `k[X]`
(Lemma 11.76).
- **Division and flatness (Theorem 11.81, Corollaries 11.82, 11.84, 11.85,
  Theorem 11.83).** For a matrix `M` over `k[X]`, `F` is in `M E_d^s` iff every
  `p_eta(F)` is in `M k[X]^s`, with a lift using no new scales; so
  `F in I E_d` iff every `p_eta(F) in I`, `(I E_d) ∩ k[X] = I`, cosets have
  unique normal forms, ordinary fibres are `K`, and `k[X] -> E_d` is
  **faithfully flat** for every `Gamma`. The key step is a bounded-degree
  lifting lemma (Lemmas 11.79–11.80).
- **Sampling (Theorem 11.87, Corollaries 11.88, 11.89, Theorem 11.90).**
  `K^{<=0}`-values on a Zariski-dense set of ordinary points force
  `F in K^{<=0}[X]`; in one variable a nonpolynomial entire function has only
  finitely many ordinary points with omnific values; affine Hahn images of
  dense sets, including infinitesimally spaced grids, work too; and
  `F(S) ⊆ K^{<=0}` iff every positive scale polynomial vanishes on `S`.
- **Vanishing ideals (Corollary 11.92, the merge's).** The entire functions
  vanishing on a set `S` of ordinary points are `I_k(S) E_d`; for `k = C` those
  vanishing on the `K`-points of an algebraic set `V(I)` are `sqrt(I) E_d`.
- **Omnific-preserving entire maps (Theorem 11.94, Corollary 11.95).**
  `F(Z_k^d) ⊆ Oz_K` iff `F(Oz_K^d) ⊆ Oz_K` iff
  `F in Int(Z_k^d, Z_k) ⊕ Pi_K[X]`; over `R`, a finite binomial expansion with
  coefficients in `Oz_K`. The polynomial half is the set-sized-quotients
  report's `osq:pm:thm:numreal`/`numgaussian` in its workspace form
  `osq:or:cor:workspace`; the new step is the collapse to a polynomial.
- **Exceptional loci (Theorems 11.99, 11.101, 11.104, 11.107).** The ordinary
  `K^{<=0}`-valued locus is the zero set of the finitely generated
  positive-tail ideal `I_+(F)`, and the omnific locus adds `p_0(F)(s) in Z_k`
  (not Zariski closed in general); in one variable at most `n_0 + 1` actual
  scales generate `I_+(F)`, sharply; the same scales control every jet order;
  every ideal is `I_+(F)` of some polynomial, and every nonzero ideal of a
  nonpolynomial entire `F` when `cf(Gamma) = aleph_0`.
- **Halting barrier (Theorem 11.111).** In `R((t))` with coefficients in
  `Q[t]` and `v(a_m) >= (m-1)^2`, the family `F_M` has exceptional set `{0,1}`
  or `{0}` according as the machine `M` never halts or halts, so
  `{M : F_M(1) omnific}` is `Pi^0_1`-complete: finite certificates exist but
  cannot be computed in general.

## Three things to read before using a theorem from here

**The two extension statements are one statement (Remarks 1.8 and 10.6).**
One source states the noncofinal case negatively — the series is *not
entire* over `K_Delta`, and `E_Delta ∩ K_Gamma[[Z]] = K_Gamma[Z]` — while the
other proves the same series stays strongly summable on exactly
`D_(Gamma,Delta)` and keeps all its zeros there. They are the coarse and the
exact form of one fact; Section 14.3 exhibits the concrete pair.

**One name for the order invariant (Remark 1.4).** *Order unit* and
*cofinal-cyclic element* are the same condition; the report keeps **order
unit**. It is **not** `cf(Gamma)`: an order unit forces countable cofinality
but not conversely, and that gap is exactly the third case of the trichotomy.

**Ring discipline and summation discipline (Convention 1.2, Section 11).**
Every statement names its coefficient ring:
`K_Gamma[Z] ⊆ E_Gamma ⊆ T_Gamma ⊆ A_Gamma ⊆ K_Gamma[[Z]]`, all with Hahn
series over `C` as coefficients, never `O(U)((t^Gamma))` or
`C{z}((t^Gamma))`. In several variables, *entire* means summability of the
whole monomial family; homogeneous-block evaluation is a different convention
and is never called entire.

## Explicit examples

`Gamma_infinity = ⊕_{j>=0} Q*omega^j` has countable cofinality and no order
unit. In it the Bézout counterexample has roots `omega^(omega^n)` and
`omega^(omega^n) + omega^(-omega^(n+1))`; the maximal ideals containing the
pair are exactly the `M_U`, `U` nonprincipal, with residue fields built on
`⊕_{0<=j<=n} Q e_j` (the fourth source's own group omits `e_0`); the values
`omega^(n! omega^n)` at `omega^(omega^n)` are interpolated by an explicit
cardinal series (Remark 8.21) while `omega^(omega^(n+1))` are not. The
product `prod_{j>=0} (1 - t^(e_j) Z)` has the simple positive surreal zeros
`omega^(omega^j)`. `Q^d` lexicographic and `Q e_1 + Q e_2` have order units
and are Bézout; `Gamma_(omega_1)` has uncountable cofinality and admits only
polynomials — **rank is not the driver**. Section 14.2 has the rank-two
hidden-tail pair and Section 14.6 the separation table. In several variables
(Section 11): `sum t^(n^2) (XY)^n` is evaluable at `X = omega^omega`,
`Y = omega^(-omega)`; `sum t^(n^4) X^n Y^(n^2)` has a nonclosed domain; and
`1 + sum t^(n^2) prod_(j<=n) (Y - c_j X)` has polynomial directions exactly
`[1 : c_m]`. For rectification (Section 11.13): the omnific centres
`omega^(omega^(2n)) u_1` lie on a line, but their refinements by the clusters
`+ omega^(-omega^(2n+1)) u_j` are not line-rectifiable (display (R19),
Corollary 11.58); with the scales `e_n` instead, the first two points of each
cluster are the close pair of the Bézout counterexample (Remark 11.59). The
nodes `omega^(omega^(2i))` with multiplicities `i+1` give a non-finitely
generated fat-point ideal on a straight line (Example 11.70).

## What the report does not claim

- No named published conjecture is solved. Priority is **not** certified by
  any source; literature checks were targeted, and searches returning nothing
  were not treated as evidence of absence. None of the seven manuscripts was
  refereed or machine-checked; **no Lean verification is claimed**.
- Classical inputs are credited, not claimed: rank-one factorization, Newton
  polygons and canonical products, the Hahn–Neumann support lemmas, algebraic
  closedness of Hahn fields, the rank-two distinction between positive
  valuation and topological nilpotence, the ultrafilter method for maximal
  ideals (Henriksen, Bruno), the finite-word well-quasi-order theorem, the
  Hilbert basis theorem, Conway normal forms, and the Ma–Neelon realization of
  algebraic unions as convergence sets (which are **not** polynomial-direction
  loci). The sixth source states that its **ultraproduct and valuation-domain
  mechanism for primes is classical** (Finocchiaro–Frisch–Windisch for
  products of rings, including Prüfer domains; the Stacks Project for primes
  of valuation rings), as are the Hahn support calculus, the normal forms and
  the valuation-ring elimination behind its Smith forms; it proposes only the
  analytic prime fibres, the reduced-divisor dichotomy and the cofinal
  splitting construction, "not found in the compared sources", which it says
  is not proof of their absence.
- Outside Section 11, `Gamma` must be divisible and algebraic closedness is
  used essentially in the factorization theory. Section 11 works under weaker
  hypotheses, and none of the divisible-group results — in particular zero
  conservation — is transferred to it. (This describes Sections 11.1–11.8;
  the seventh source's Sections 11.9–11.15 keep divisibility, take `k = R` or
  `C`, use the uncountability of `k` once, and use no algebraic closedness.)
- The maximal-ideal classification is for **one node per shell** only;
  several nodes per shell, prime ideals, and maximal ideals of `E_Gamma`
  containing no such product are not treated (Question 16.4 stays open,
  re-scoped). The unit-ideal criteria are **not** a corona theorem. The
  ultrafilter characters are ring homomorphisms and are not asserted to
  preserve strong sums; `Phi_U(P_D)` must not be computed termwise.
  *Re-scoped by the sixth source:* prime ideals are now classified above a
  product with one **simple** node per shell (Section 12), and for uniformly
  bounded multiplicities as prime spaces and dimension only. Primes above
  several nodes per shell or unbounded multiplicities, and prime or maximal
  ideals containing no such product, are still not classified.
- The sixth source's limits (Section 12.10): "entire" has fixed-field scope,
  nothing is claimed for `No[i]`; the quotient, maximal ideals, residue
  fields, `Max = beta N` and cofinal-extension entireness and zeros are
  inherited, not new; in the order-unit case only the quotient `E/(P_D)` is
  zero-dimensional, not `E`; bounded multiplicities transfer prime spaces and
  dimension, not von Neumann regularity or semiheredity; no change of zeros
  under extension is asserted; no tensor-product description of scalar
  extension is claimed; the suggested Lean dependency order is not code.
- In several variables only the scalar-extension clause is answered:
  preparation, interpolation, divisors, ideals and GCD/Bézout remain open
  (Question 16.5), as do the block domain at arbitrary new-field tuples
  (Question 16.6) and effective support classes (Question 16.7). The number
  of variables is finite; all fields are full Hahn fields.
  *Re-scoped by the seventh source:* for configurations of **points** that an
  entire automorphism carries into a coordinate line, the ideal theory
  (fat-point generators, their sharp number, non-finite generation for
  unbounded multiplicities) and the interpolation of **values** are now
  settled (Sections 11.9–11.15). Preparation, GCD/Bézout, divisors with
  positive-dimensional support, ideals of non-rectifiable configurations and
  jet interpolation in several variables remain open.
- The seventh source's limits (Section 11.15): every result is relative to one
  fixed Hahn workspace, radial finiteness is not fine discreteness and is lost
  in a larger workspace, and there is no class-global entire theory on `No` or
  `No[i]`; constant coefficients are trivially valued (`exp(X)` is not
  entire); the coefficient field is `R` or `C` and uncountability is used,
  with no countable-field or descent statement; no classification of all
  ideals of `E_d`, all entire automorphisms, all non-rectifiable sets or all
  entire functions on the class; line-rectifiable is **not** claimed
  equivalent to Rosay–Rudin tameness or Winkelmann's extension properties,
  and the classical comparison is not a transfer principle; the rectifying
  maps are not claimed to preserve `Oz`, nothing concerns ring automorphisms
  of `Oz` or field automorphisms of `No`, ordinary integers are not radially
  finite, and extension of arbitrary bijections of omnific configurations is
  not claimed; no omnific factorization question is settled, and the
  Berarducci–Mantova derivation is not used; the simplex obstruction is not
  shown to be the only one, and no threshold is uniform over all
  automorphisms; the interpolation lemma is sufficient, not an exact image;
  ideal generation is algebraic, no countable generation is implied, and no
  Noetherianity, coherence or Nakayama lemma is assumed; the evaluation map
  `E/(P) -> prod K` is not claimed surjective without an order unit, and no
  unrestricted product description of the evaluation quotient is given; the
  radical distinction is not claimed new as a phenomenon; projection-and-shear
  is classical and jet counting elementary; "proposed" means only not found in
  a bounded search; no named conjecture is settled.
  *Re-scoped by source 11 (batch 32):* for `k = R` or `C` and ideals extended
  from `k[X]`, membership, normal forms and contraction are decided scale by
  scale and `k[X] -> E_d` is faithfully flat (Sections 11.18–11.19); the
  vanishing ideals of ordinary point sets, and for `k = C` of algebraic sets
  over `C`, are extended ideals (Corollary 11.92, the merge's). Ideals not
  extended from `k[X]`, preparation and GCD/Bézout theory remain open.
- Source 11's limits (Section 11.26, a numbered list of seventeen): strong
  Hahn summation is not complex convergence; nonpolynomial results live in fixed
  set-sized workspaces, and an entire series on the whole class `No[i]` is a
  polynomial; the omnific locus carries the residue condition and need not be
  Zariski closed, and the leading valuation is not an omnific test; flatness
  and the image theorem are over `k[X]`, not `K[X]`; `E_d` is not claimed
  Noetherian, a PID or Bézout; `Oz_K` is not an integer polynomial ring and
  `Frac(Oz_K) = K` is not assumed; the binomial basis is not a basis of
  `Int(Z[i]^d, Z[i])`, and an infinite sample gives polynomiality, not
  integer-valuedness; the classification is inside `E_d`, not about arbitrary
  functions on `Oz_K`; sharpness of `n_0 + 1` concerns actual scales;
  certificates exist but are not computable in general, the undecidability
  concerns one presentation, restricted classes and the integer conditions
  `p_0(s) in Z_k` are not decided, and it is not a new negative solution to
  Hilbert's tenth problem; the scale polynomials depend on the coefficient field
  and monomial section, and the Gaussian automorphism problems of the companion
  reports are not settled; the 8,774 checks are finite; no Lean, no referee, no
  repository build, priority not certified, no named conjecture settled; the
  repository comparison was targeted, the omnific Diophantine-geometry article
  and most of the collection were not read, and a failed search is not evidence
  of originality; Wikipedia was orientation only.
- All supports and index sets are sets; the extension theorems keep the
  coefficient field fixed; the hidden-tail table covers monomial arguments
  only; strong summability, intrinsic valuation convergence and the fine
  surreal topology are never identified. "Entire" always has fixed-field
  scope, and nothing here argues against all-scale polynomial rigidity, which
  the report re-derives and credits.
- The constructions are finite-step only relative to exact field operations
  and valuation certificates; they are not algorithms for arbitrary Hahn
  input. Section 16.3 preserves every limitation recorded by any source.

## Open questions, re-scoped

- Question 16.1 (the image): answered by the third source, independently by
  the fourth.
- Question 16.3 (finitely generated ideals): answered for one generator a
  canonical product; now also for finitely many generators, and membership of
  arbitrary elements for one simple node per shell. For one simple node per
  shell every finitely generated ideal containing `P_D` is `(P_D, G)`
  (sixth source, Remark 12.22). Open: shells with several nodes or
  multiplicities, and the ideal `(f, g)` beyond membership tests.
- Question 16.4 (maximal spectrum): answered above a one-node-per-shell
  product (fourth source). Its "prime ideals" clause is answered by the sixth
  source for one simple node per shell (Theorem 12.9), with bounded
  multiplicities (Theorem 12.40). Open: several nodes per shell, unbounded
  multiplicities, whether every non-evaluation maximal ideal contains such a
  product, primes containing no such product, relations between divisors.
- Question 16.5 (several variables): the "In particular" clause answered by
  the fifth source; the rest open. Questions 16.6 and 16.7 are new.
  *Re-scoped by the seventh source:* the ideal-theory clause and interpolation
  of values are answered for configurations of points that an entire
  automorphism carries into a coordinate line (Theorems 11.35, 11.37, 11.62,
  11.66, Corollary 11.64); Bézout/GCD, preparation, positive-dimensional
  divisors, ideals of non-rectifiable configurations and jet interpolation
  remain open. The text of the question and of its earlier notes is kept.
- Question 16.2 (what the image theorem does not decide): its several-variable
  part now has an answer for values on line-rectifiable configurations
  (Corollary 11.64); jets and other configurations remain open.
- Questions 16.9–16.11 are the sixth source's: several nodes on a shell,
  unbounded multiplicities, and when the prime spectrum is invariant under
  cofinal extension.
- Questions 16.12–16.16 are the seventh source's: a rectifiability criterion
  without an order unit, lower-dimensional targets, ideals of non-rectifiable
  configurations, extension of prescribed maps, and countable coefficient
  fields and descent.
- *Status (batch 32):* Question 16.5's ideal-theory clause is partly answered
  further by source 11, for ideals extended from `k[X]` (Corollaries 11.82,
  11.84, Theorem 11.83) and for vanishing ideals of ordinary point sets and,
  over `C`, of algebraic sets defined over `C` (Corollary 11.92, the merge's).
  Still open: ideals not extended from `k[X]` (in particular from `K[X]`,
  Question 16.17), the Bézout obstruction and GCD theory, preparation,
  non-algebraic zero sets, non-rectifiable configurations, jet interpolation.
  Questions 16.2 and 16.7 carry a note that source 11's undecidability theorem
  concerns a different test and answers neither.
- Questions 16.17–16.26 are source 11's: polynomial matrices with Hahn
  coefficients (flatness of `K[X] -> E_d` for `d >= 2`; the merge notes the
  one-variable case is positive), meromorphic arithmetic rigidity, effective
  certificate classes, sampling sets beyond affine grids, intrinsic exceptional
  ideals, function theory on varieties, composition, other integer parts and
  coefficient rings, characteristic and cardinal extensions, and formalization
  with proof certificates. It calls them proposed directions, not published
  open problems.

## Stale statements corrected

- The fourth source presents itself as resolving "the repository's explicitly
  unidentified infinite jet image". True at its pin `0097304`; stale now, since
  the third source answered the question first in this tree. Recorded as an
  independent second proof (Section 1.4, Appendix C).
- Its phrase "a previously known disjoint-zero counterexample" is Theorem 8.29,
  and the "nonconstructive assertion that some non-evaluation maximal ideal
  contains a proper two-generated ideal" is Corollary 8.32; both hold.
- The fifth source's "Appendix `ent:app:multivariate`" is now Section 11.2.
  Its pinned blob `f034bdb` differs from the base of this merge only in the
  two appendices updated for the third source.
- The earlier text said that `m_gamma(FG) = m_gamma(F) + m_gamma(G)` "is never
  needed"; the cardinal route needs it, and Section 2.5 says so. Scope
  paragraphs that posed the several-variable replacement as open, and the
  non-claims attached to Theorem 8.33, now state what the new sources proved
  and what remains open.
- The sixth source's statements about this report (the quotient, the
  maximal ideals with ultraproduct residue fields, `Max = beta N`, non-Bézout
  without an order unit, finite shell algebras for several nodes, and the
  seven labels its audit cites) were checked against the current text and
  hold; the report directory is unchanged between its pin `465a54b` and the
  merge base, so no stale statement was found. The report's own text that
  prime ideals are "not classified" (end of Section 8.9, the scope paragraph
  on the image theorem, Question 16.4) is kept and now carries a re-scoping
  pointer to Section 12.
- The seventh source calls its question "a different several-variable global
  problem" from this report's; it partly answers Question 16.5, and the
  statements that only the scalar-extension clause is answered (Section 1.3,
  the head of Section 11, Section 11.8, Section 16.3, Questions 16.2 and 16.5,
  and this README) are kept as written with a re-scoping sentence. Its account
  of this report (coefficient criterion, products and division, order-unit
  interpolation, restricted-product interpolation, several-variable criteria
  and scalar extension) was checked and holds. Its search for
  "rectification" found nothing at its pin; the word now occurs only in its
  own placed files. At its pin the collection had no omnific-integer
  report; it now has two, and Section 15 records the relation (a shared normal
  form, no shared theorem). It did not credit `hol:cf:lem:reduction` or this
  report's Lemma 8.4 and Theorem 4.1 argument; Section 11.12 does. The
  sentences "the sixth source's letters are translated by the last table of
  Section 2.5" (and the same for the fifth) had become inaccurate once a
  later table was appended; they now name the table.
- Source 11 says it gives "a proof that allows arbitrary rank and does not
  assume divisibility" of the coefficient criterion; that adds nothing here,
  since Theorem 11.3 (`ent:thm:multi-criterion`) is already stated and proved
  for any trivially valued field and any, not necessarily divisible, group by
  the same descending-sequence argument. Printed once, as are its lemma on
  locally finite families (Lemma 11.2(a)), its cofinality dichotomy
  (Corollary 3.3 with Proposition 11.4) and its whole-class corollary
  (Corollary 10.12, Proposition 11.32). Its account of this report, read at
  `343dc2c`, is current: the directory is unchanged between that pin and the
  merge base. It did not cite the fifth source's exceptional-direction
  theorems (Theorems 11.27–11.28), which run parallel to its exceptional
  ideals, nor the set-sized-quotients report's numerical-polynomial theorems,
  which are the polynomial half of Theorem 11.94; Sections 11.20–11.21 and
  Section 15 record both.
- The statements that the seventh source's subsections are the "closing" or
  "last seven" subsections of Section 11 (Sections 1.3, 11 and 16.3, Question
  16.2's note and Appendix C) became inaccurate once source 11's subsections were
  appended; they now name the subsections. The counts "seven manuscripts",
  "seven suites" and "five of them arrived with letters that collide" are now
  eight, eight and six. The sentence of Section 16.3 that Section 11 has "no
  preparation, divisor or ideal theory" and the Section 11.8 limits bullet are
  kept, with a sentence on what source 11 adds.

## Relation to the rest of the collection

- **`surcomplex/rank-one-berkovich` — this report extends it.** Rank one is
  `cf(R) = aleph_0` with `1` an order unit, so it lands in the **Bézout**
  case. Its `prop:rankobstruction` is why Lemma 9.1 builds a *coarsening*,
  not an embedding. Its ring chain resembles ours and is not the same chain.
- **`surcomplex/analysis` and `foundations-and-computation/foundations`.** The
  whole-class rigidity corollaries (Corollary 10.12 and Proposition 11.32) are
  re-derivations in their whole-family forms; the foundations localization
  principle is consumed, and Lemma 11.30 gives the fifth source's short proof
  of it with credit.
- **`surcomplex/global-divisors` — a different ring.** Its support-restricted
  Chinese remainder theorem restricts something else, for other reasons, in
  `O(U)((t^Gamma))`; Section 15 states the difference, which covers the fourth
  source's restricted product too.
- **`surcomplex/analytic-geometry`** calls an ideal *free* when it has no
  common zero, and its "boundary" is that of a fixed disk. The fourth source's
  *free ultrafilter* and *boundary ideal* are written "nonprincipal" and
  "non-evaluation" here. Different rings; nothing transfers. Its prime
  spectrum of the fixed-polydisk ring `O(D)((t^R))`
  (`analytic:thm:fixed-gauge-prime`, `analytic:thm:fixed-fibre`) also has
  continuum chains built from the power gauges `n^r` that Lemma 12.16 uses;
  there the chain lies in one classical fibre and comes from growth of Hahn
  valuations at a fixed divisor, here from the quotient groups
  `Gamma/H_n`, which vanish for the order-unit group `R`. Its citation of
  Henriksen's 1953 paper on prime ideals of classical entire functions is
  recorded in Section 15 as context; the sixth source does not cite it.
- **`surcomplex/holonomic-rigidity-for-entire-hahn-functions`** uses the same
  whole-family convention in several variables. The covering step of Theorem
  11.27 is the countable-field device of its `hol:lem:generic`. Its
  `hol:cf:lem:reduction` (one-variable polynomial reduction modulo a proper
  convex subgroup) is the antecedent of Theorem 11.53, which is its
  several-variable form with evaluation compatibility, applied to an
  automorphism and its inverse; the seventh source did not cite it. Its
  `hol:pc:prop:composition` reproves the polynomial case of the composition
  clause of Proposition 3.5, and `hol:pc:prop:pullback` computes the Gauss
  value, active exponents and residue polynomial of `F ∘ P` at large scales
  (batch-34 note after Proposition 3.5; its scale sign is opposite to ours).
- **`surreal/omnific-diophantine-geometry`** and
  **`surreal/set-sized-quotients-of-omnific-integers`** were placed after the
  seventh source's pin. The only omnific input of Sections 11.9–11.15 is the
  normal form `Oz = Pi ⊕ Z` read in a workspace, which agrees with
  `found:eq:omnific`, `odg:def:rings` and `odg:lem:workspace`; no theorem is
  shared, and the rectifying maps are not asserted to preserve `Oz`.
- **`surreal/set-sized-quotients-of-omnific-integers` — source 11 shares a
  theorem.** The polynomial half of Theorem 11.94 and Corollary 11.95 is that
  report's `osq:pm:thm:numreal`, `osq:pm:thm:numgaussian`, `osq:pm:thm:grid` and
  `osq:pm:lem:binomial`, transferred to fixed workspaces by
  `osq:or:cor:workspace` (its `A_Gamma = Z ⊕ J_Gamma`, with `J_Gamma` our
  `Pi_K` with the exponent sign reversed); `osq:or:thm:matrix` is the
  polynomial counterpart of the jet conditions of Theorem 11.104. The analytic
  half, the collapse of an entire series to a polynomial, is what that report
  excludes ("entire Hahn series and expressions of nonstandard degree are
  outside the theorems", after `osq:or:cor:workspace`, and in its limits
  lists). A reciprocal note there is proposed, not made.
- **`surreal/omnific-diophantine-geometry`** lists among its non-claims that
  "Polynomial lifting does not license evaluating infinite power series";
  source 11 shows what does hold for entire series in one fixed workspace
  (Theorems 11.87 and 11.94) and does not contradict it. Source 11 did not read
  that article. A reciprocal note is proposed, not made.
- **`surreal/omnific-preserving-automorphisms`** studies the automorphism
  distinctions on which source 11's scale polynomials depend (Section 11.25);
  source 11 read its README and source audits 12 and 13, and uses no theorem of
  it.
- **`surcomplex/nonabelian-support`** uses `Pol` for a normalized polar
  factor; the polynomial-direction locus is written `Pdir` here.
- **`surreal/transcendence-over-bounded-support` — the same alternative for
  finite extensions (batch 32).** Its Galois part proves
  `bst:gr:thm:transition`: for an inclusion of nonzero set-sized ordered
  groups, the smaller divisible, a cofinal inclusion keeps every finite
  extension of the smaller complex bounded-support fraction field a field of
  the same degree over the larger one, and a noncofinal one splits every such
  extension completely. A paragraph after Remark 1.8 records it as the
  algebraic counterpart of Theorem 1.7 (b), (d); the objects differ and
  neither theorem is used for the other.
- **`surreal/omnific-continued-fractions`** meets both invariants of Remark
  1.4 in `R((ω^G))`: some infinite continued-fraction code is uniquely
  realized exactly when `cf(G) = aleph_0` (`ocf:cor:cofinality`), some
  eventually periodic one exactly when `G` has a positive order unit
  (`ocf:thm:orderunit`). A batch-34 sentence at the end of Remark 1.4 records
  it; neither report uses the other.

## What was run

- At the fifth merge, all five earlier suites, from copies outside the repository, on Python 3.14.4:
  `06-…-verify-examples.py` 831 of 831, identical to the delivered record
  except its recorded Python version; `03-…-verify.py` 664;
  `01-exact-jet-image-verify.py` 1958; `07-scale-moderate-interpolation-verify.py`
  1876 in 12 categories; `08-multivariate-extension-verify_examples.py` 1072 in
  10 categories. The last four outputs are identical to the delivered records
  up to line endings.
- For the sixth merge, `09-prime-spectra-verify_finite.py --json <scratch>`
  on a copy, Python 3.14.4: **PASS, 10,889 assertions** in 13 categories,
  200 Smith matrix cases; the output is identical to
  `data/09-prime-spectra-verification_results.json` up to line endings.
- The SHA-256 hashes in `data/07-…-package_manifest.json` match the three
  source-4 files shipped here (the script, the record and the source audit);
  the manifest also lists that manuscript's own `article.tex`, `article.pdf`
  and `README.md`, which are not shipped. `data/08-…-build.json` likewise
  hashes the fifth manuscript's own source and PDF, not shipped.
- For the seventh merge, `10-entire-rectification-verify.py --output <scratch>`
  on a copy, Python 3.14.4 with SymPy 1.14.0: **all finite checks passed**
  (four padded-cardinal node values, one linear-division identity, two
  normalized simplex determinants in dimensions 2 and 3, 40 jet-count cases,
  two finite fat-point ideals with 40 and 30 generator-jet equalities and 35
  and 51 kernel vectors reduced to zero by a Gröbner basis). The output is
  identical to `data/10-entire-rectification-verification-results.json`
  except the recorded Python version (3.13.5 there).
- For the eighth merge, `11-arithmetic-sampling-verify.py --output <scratch>`
  on a copy, Python 3.14.4 with SymPy 1.14.0: **PASS, 8,774 assertions** in
  ten groups (450, 1193, 1000, 720, 521, 421, 260, 87, 3818 and 304), about 11
  seconds; the output is identical to
  `data/11-arithmetic-sampling-verification.json` except the recorded Python
  version (3.13.5 there) and line endings. The SHA-256 hashes in
  `data/11-arithmetic-sampling-ARTIFACT_MANIFEST.json` match the six source-11
  files shipped here; the build report's hashes of the unshipped article and
  PDF match a fresh extraction of the delivered archive.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`: 160
  pages, 0 errors, 0 undefined references or citations, 0 multiply defined
  labels, 0 duplicate PDF destinations, no overfull or underfull boxes, no
  LaTeX or package warnings (the committed 133-page baseline builds the same
  way). 278 numbered statements: 60 theorems, 49 lemmas, 22 propositions, 52
  corollaries, 15 definitions, 4 conventions, 13 examples, 26 questions, 37
  remarks. The sixth merge kept all 266 earlier labels and added 61
  (`ent:ps:`), 327 in all; the seventh kept those 327 and added 79 (`ent:rc:`),
  406 in all; the eighth kept those 406 and added 87 (`ent:as:`), 493 in all.
  Every one of the 406 earlier labels resolves to the same number as before
  the eighth merge (compared through the `.aux` files of the two builds).
  The batch-32 reciprocal paragraph on `bst:gr:thm:transition` (after
  Remark 1.8, unnumbered) takes the build from 159 to 160 pages, with the
  same clean log; it adds no label, and all 493 labels keep their numbers.
  The two batch-34 paragraphs (end of Remark 1.4, after Proposition 3.5)
  leave the build at 160 pages with the same clean log; no label is added and
  all 493 keep their numbers.

The checks prove no infinite theorem. In particular the **finite truncations
of the counterexample pair are coprime polynomials and do satisfy polynomial
Bézout identities**, so no finite computation can witness the main negative
result. Appendix B states what each suite checks and cannot check.

## Build and reproduce

A normal TeX Live or MiKTeX installation with the packages named in
`article.tex` and `latexmk` is sufficient. The bibliography is embedded: no
BibTeX file, external graphics, shell escape or repository checkout is needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

**Run the programs on a copy, or with an output path outside this
directory.** The first six use only the Python standard library; the seventh
needs Python 3.10 or later and SymPy (`pip install -r
data/10-entire-rectification-requirements.txt`, which pins `sympy==1.14.0`);
source 11's needs Python 3.9 or later and the same SymPy
(`data/11-arithmetic-sampling-requirements.txt`).

- `06-cofinality-bezout-trichotomy-verify-examples.py` requires `--output`
  and exits nonzero without one; it cannot overwrite the delivered record by
  accident.
- `03-cofinality-and-scalar-extension-verify.py` takes no arguments and writes
  `verification.json` and `verification.txt` into the `data/` directory next
  to its own `code/` directory. Copy it into a scratch `code/` folder first.
- `01-exact-jet-image-verify.py` requires an output path and refuses to
  overwrite an existing file.
- `07-scale-moderate-interpolation-verify.py` and
  `08-multivariate-extension-verify_examples.py` take an optional `--output`
  and otherwise only print. Their documented commands write
  `data/verification.json`; name a scratch path instead.
- `09-prime-spectra-verify_finite.py` takes an optional `--json PATH` and
  otherwise only prints. Its documented command
  (`--json verification_results.json`) rewrites the delivered record in
  place; name a scratch path instead.
- `10-entire-rectification-verify.py` takes an optional `--output PATH`;
  without it, it writes `verification-results.json` **next to the script**.
  In the source's layout that rewrites the delivered record in place; here it
  would add a file to `code/`. Name a scratch path, on a copy.
- `11-arithmetic-sampling-verify.py` takes an optional `--output PATH` and
  otherwise only prints; its documented command (`--output verification.json`)
  rewrites the delivered record in place. Name a scratch path, on a copy.

```sh
mkdir -p /tmp/ent/code /tmp/ent/data
cp code/*.py /tmp/ent/code/
python /tmp/ent/code/06-cofinality-bezout-trichotomy-verify-examples.py --output /tmp/ent/A.json
python /tmp/ent/code/03-cofinality-and-scalar-extension-verify.py        # writes /tmp/ent/data/
python /tmp/ent/code/01-exact-jet-image-verify.py --output /tmp/ent/C.json
python /tmp/ent/code/07-scale-moderate-interpolation-verify.py --output /tmp/ent/D.json
python /tmp/ent/code/08-multivariate-extension-verify_examples.py --output /tmp/ent/E.json
python /tmp/ent/code/09-prime-spectra-verify_finite.py --json /tmp/ent/F.json
python /tmp/ent/code/10-entire-rectification-verify.py --output /tmp/ent/G.json
python /tmp/ent/code/11-arithmetic-sampling-verify.py --output /tmp/ent/H.json
```

`code/03-cofinality-and-scalar-extension-Makefile`,
`code/06-cofinality-bezout-trichotomy-build.sh`,
`code/09-prime-spectra-build.sh` and `code/10-entire-rectification-build.sh`
build their source manuscripts in their
original layouts and do not build this report; they are kept only as
delivered. `09-prime-spectra-build.sh` expects the unshipped
`prime_spectra_at_surreal_infinity.tex` and an unprefixed `verify_finite.py`
in its own directory, so here it fails; in its original layout it overwrites
the delivered PDF and rewrites `verification_results.json` in place.
`10-entire-rectification-build.sh` likewise expects the unshipped
`entire_rectification.tex` and an unprefixed `verify.py`; in its original
layout it reruns `verify.py`, rewriting `verification-results.json` in place,
and overwrites the delivered PDF.
`code/11-arithmetic-sampling-build.py` compiles the unshipped
`arithmetic_sampling.tex` next to itself in a temporary directory; here it
exits for lack of that file. In its original layout it copies the PDF back
over the delivered one and rewrites `build_report.json` beside the output
PDF, even when `--output` names another PDF path.

## Maintained review scope

The maintained proof review read the first two manuscripts and their former
finite-variable appendix before the three later manuscripts were incorporated.
The expanded portions have not received that review. It clarified the fixed-element order-unit
equivalence, the nonzero-group convention and the nonzero indices in the
extension summary; strengthened the growth barrier to require a sequence
that tends cofinally to infinity (with a counterexample to mere cofinality
of its range); supplied direct linear-division and multivariable
coefficient-criterion arguments; and separated the preparation-based finite
zero bound from algebraic closedness. The conclusion now states the
universal Bézout property separately from identities for individual pairs.
The imported Hahn-field scope was checked against Poonen, Section 3 and
Corollary 4; the positive-valuation versus topological-nilpotence distinction
against Conrad, Section 6.2; and the complete real-valued setting of the
classical entire-function results against Cherry's lectures. These checks
do not establish priority or independent peer review.

The review reran the first two unmodified programs on temporary copies:
**831/831** and **664/664** checks passed. This does not verify the later suites
or the infinite mathematical statements. Section 12, from the sixth source,
Sections 11.9–11.15, from the seventh, and Sections 11.16–11.26, from source
11, have not received that review either.
