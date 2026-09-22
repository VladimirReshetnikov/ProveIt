# Surcomplex Spectral Theory

**Singular Values, Infinitesimal Rank, Multiscale Stability, Exact
Determinantal Ramification, and Hankel Square-Class Profiles**

One article, `article.tex` (70 pages compiled), assembled from **three
separately delivered manuscripts** (21 and 22 September 2026), with `code/`
and `data/` holding all three sets of exact symbolic checks and their recorded
output. The manuscripts themselves are not shipped.

```
article.tex                            the report, standalone LaTeX with an internal bibliography
article.pdf                            the compiled report, 70 pages
README.md                              this guide
repository-audit.md                    manuscript A's historical coverage audit (pin e260237)
03-hankel-ramification-PROOF_AUDIT.md  manuscript C's dependency map and verification boundary
code/   verify-examples.py, build.sh, build.ps1                          (A)
        02-determinantal-ramification-descent-{verify.py,build.sh,build.ps1}   (B)
        03-hankel-ramification-{check_examples.py,build.sh}                 (C)
data/   verification-report.{json,txt}, build-report.json, requirements.txt    (A)
        02-determinantal-ramification-descent-{verification.json,verification.txt,
                                               build-report.json,requirements.txt}   (B)
        03-hankel-ramification-{verification_results.json,verification_output.txt,
                                requirements.txt}                            (C)
```

**Labels.** The article keeps three label schemes, and none will be renamed:
`docs/FORMALIZATION.md` cites labels by name. The 102 bare labels (`thm:scales`,
`prop:positive`, …) come from manuscript A's standalone origin; the 82 `spec:`
labels were added with manuscript B; the 56 `spec:hank:` labels belong to
manuscript C's section. The files under `code/` and `data/` carry the local
source numbers `02-` (B) and `03-` (C); A's files are unprefixed.

## Provenance

| manuscript | contribution |
| --- | --- |
| **A**, "Surcomplex Spectral Theory: Singular Values, Infinitesimal Rank, and Multiscale Stability" (delivered as `01-determinantal-singular-value-scales.tex`, 21 September 2026) | The base. Every section except §9–§12 is A's. |
| **B**, "Spectral Descent and Exact Ramification in Surcomplex Matrix Calculus" (archive `spectral_descent_surcomplex`, delivered as `02-determinantal-ramification-descent.tex`, 21 September 2026) | §9–§11 and the removal of the divisibility hypothesis. |
| **C**, "Hankel Square-Class Profiles over Surreal Hahn Fields: Exact Factor Counts, Splitting Fields, and Definite Pencils" (archive `surreal_hankel_ramification`, 22 September 2026) | §12, the polynomial counterpart of §10–§11, and the definite-pencil item that `spec:rem:divisibility` used to list. |

B cites A by name and explicitly declines to reclaim its content: "the SVD
over real closed fields, determinantal singular scales, positive Cauchy–Binet
identities, and perturbation theory … are not claimed again as new here." So
the shared mathematics is printed **once**, in A's form — `thm:scales` and
`thm:gram` are A's theorems, and B's re-derivations of them appear only as the
one-line corollary `spec:cor:gramscales`.

C cites this report and reclaims none of its theorems. It reproved four
inputs to isolate the field properties it uses; all four were already here and
are **cited, not reprinted**:

| C's reproved input | printed here as |
| --- | --- |
| positive square classes (its Lemma 2.1) | `spec:lem:scalarroot` at `q = 2` (Lemma 10.1) |
| Pythagorean property (its Cor. 2.2) | `spec:lem:normroot` (Lemma 9.8) |
| finite monomial extensions: degree and basis (its Lemma 2.3) | `spec:lem:finiteindex` (Lemma 10.2); the real Galois group and the **intermediate fields**, which were not here, are the new Lemma 12.2 |
| Hahn principal axes (its Prop. 3.2) | the real case of `spec:thm:hermitian` (Theorem 9.12) |

C's proof of principal axes is different — coprime Hensel lifting through
universal formal series, then polynomial idempotents, with no contour
argument — and is kept as a marked **second route** (Lemma 12.4, Remark
12.5). Where the merge had to choose:

- C is placed in this report, after §11, rather than in `polynomial-algebra`.
  That report works in divisible workspaces, where `Γ/2Γ = 0` and every
  invariant of §12 vanishes.
- C's letters `α_k = v(h_k)`, `β_k`, `d_k = h_k/h_{k−1}`, and its `q` for a
  quadratic form and for a second polynomial are renamed (`π_k` for pivots,
  `ξ_k` for their classes, `φ`, `τ_p`, `p̃`), to keep them apart from this
  report's `γ_k`, `Δ_k` and root order `q`. Remark 12.1 states the meaning of
  `h_k` here: the `k`-th leading principal minor of the Newton-sum Hankel
  matrix. The letter has other meanings elsewhere in the collection and in
  the proof of `spec:lem:positivetrace`.
- Two short observations linking §12 to §10–§11 are added and **marked in the
  text as made by the merge**, not by C: after Corollary 12.10, that
  `spec:lem:positivetrace` needs no basis choice, so `Σ_k √h_k` is also
  primitive; and Remark 12.11, that `spec:cor:gramcriterion` applied over
  `Λ_p` gives `R_2(H_p) ⊆ D_p`.
- C's numbering changes. Its Theorems 5.1 and 6.2 are Theorems 12.8 and 12.13
  here.

The three manuscripts audited the repository at different pinned revisions:
A at `e260237`, B at `aa84627`, C at `4cf691c`. All three declared their
audits targeted rather than line-by-line.

## What the report is

The linear algebra chapter the collection did not have: **finite** matrices
over a real closed field `F` and its complexification `F[i]`, and then over a
set-sized Hahn workspace inside `No[i]`. Every dimension is an ordinary
finite integer. It has four strands.

**The classical strand, without compactness.** Hermitian and normal
diagonalization, positive square roots and congruence, the SVD, polar
decomposition, a generalized Hermitian eigenproblem, operator and Frobenius
norms, Courant–Fischer and Ky Fan variational principles with **attained**
extrema, eigenvalue and singular-value perturbation, Moore–Penrose inverses,
least squares, and best low-rank approximation. The point is the
justification: these need **real closedness, not Archimedean completeness**.
The proofs exhibit the relevant witnesses explicitly, so a maximum is
produced rather than extracted from a compactness argument — which matters
here, because the usual compactness is unavailable and class-sized
compactness questions never have to be raised.

**The scale strand.** Over a Hahn workspace a nonzero singular value has a
valuation, and the list of those valuations is extra structure invisible in
an ordinary complex matrix. The synthesis is a pair of theorems:

- *Singular scales are determinantal scales* (`thm:scales`). With
  `Δ_k(A) = min v(det A_{I,J})` over `k × k` minors, `Δ_k = γ_1 + ... + γ_k`
  where `γ_k` is the `k`-th singular valuation. The slopes are
  nondecreasing, and `(γ_1, ..., γ_r)` is a complete invariant for
  equivalence under integral invertible row and column operations. The
  valuation ring need not be Noetherian or discrete — only finitely many
  minors are involved, so the minimum exists.
- *Positive Cauchy–Binet* (`thm:gram`). Writing
  `det(I + s A*A) = Σ c_k s^k`, one gets `c_k = e_k(σ_1^2, ..., σ_r^2)` and,
  crucially, `c_k > 0` and `v(c_k) = 2Δ_k(A)`. **Positivity is what forbids
  leading cancellation**, so the Gram polynomial's coefficient valuations
  give every singular scale, and its standard parts give the leading
  singular amplitudes one scale block at a time — with no eigenvector
  computation and no polygon drawn in an ordinary real plane.

What that buys: an intrinsic rank filtration separating exact rank from
standard-part rank, a root-free minimum-valuation elimination algorithm with
a stated exact-operation contract, precision certificates for singular
scales valid for arbitrary-rank value groups, distance to singularity as an
attained **minimum** rather than an infimum, ordered pseudospectra for
nonnormal matrices, gap-sensitive spectral projectors and subspace
perturbation (with an explicit warning about Gram squaring), Schur-complement
corrections at degenerate clusters, a genuine matrix Hahn-summability
theorem separated from algebraic inversion, regularization read as an
explicit scale filter, and a finite Schmidt/tensor example with
infinitesimal components.

**The arithmetic strand (manuscript B).** The workspace convention is now a
set-sized ordered abelian `Γ` that is **not assumed divisible**. Passing to
the divisible hull is harmless for existence and fatal for arithmetic: it
makes every positive square root free, and so erases the distinction between
a matrix whose spectral data need no new scales and one whose positive root
genuinely does.

- *Spectral descent* (`spec:thm:hermitian`, `spec:cor:normal`,
  `spec:thm:svd`). Hermitian and normal diagonalization and the SVD exist
  over `K_Γ` with **every exponent in the subgroup generated by the input
  exponents**, by a finite splitting tree of at most `n−1` nontrivial nodes
  — a bound independent of the order type of the supports and of the rank or
  cardinality of `Γ`. The infinite series are licensed by strong Hahn
  summability and a Higman-type word-finiteness lemma (proved here, not
  cited), never by convergence.
- *The determinantal ramification law* (`spec:thm:ramification`). For
  positive semidefinite `A` of rank `r` and any `q ≥ 2`,
  `K_Γ(A^{1/q}) = K_{Γ + Σ_k Z·Δ_k(A)/q}`, of degree `|R_q(A)| ≤ q^r` where
  `R_q(A)` is the subgroup the classes `Δ_k + qΓ` span in `Γ/qΓ`; finite,
  abelian, **totally ramified**, with Galois group `Hom(R_q(A), μ_q)`. So
  `A^{1/q}` is defined over `K_Γ` **iff** every `Δ_k(A)` lies in `qΓ`, and
  the degree is computed from finitely many minor valuations with no
  eigenvalue and no eigenbasis. The same invariant that measures singular
  scales controls a finite radical extension.
- *The exact Gram criterion* (`spec:cor:gramcriterion`). `A = C*C` with `C`
  over `K_Γ` iff `Δ_k(A) ∈ 2Γ` for all `k` — necessary for every rectangular
  Gram representation, and `C` may be taken square.
- *The primitive trace* (`spec:thm:primitivetrace`). The single scalar
  `tr(A^{1/q})` generates that entire extension, and so does any
  `Σ a_j λ_j^{1/q}` with `a_j` **strictly positive** in `F_Γ`. Proved by a
  mechanism, not by genericity: positivity keeps every needed coset of
  `Λ/Γ` visible, so the *specific* unweighted trace never degenerates.
- Plus finite-witness simultaneous diagonalization (`spec:thm:simultaneous`),
  joint ramification for several roots with no commutation assumed
  (`spec:cor:joint`), an order-preserving transport proposition, and the
  surcomplex transport `spec:cor:surcomplex`, which reads all of this off the
  **exact** input support group `H` rather than its divisible hull.

**The polynomial strand (manuscript C, §12).** The same arithmetic question
for a polynomial. Throughout, `Γ` is arbitrary (not divisible, any rank),
`F_Γ = R((t^Γ))`, and `p` is **monic, squarefree and real-rooted** of degree
`n`. From the coefficients alone form the Newton sums `s_j`, the Hankel matrix
`H_p = (s_{i+j})`, and its leading principal minors `h_1, …, h_n` (`h_0 = 1`),
the Hankel subdiscriminants; each is positive (Proposition 12.7, classical:
Hermite, Sylvester, Roy).

- *Exact splitting field* (Theorem 12.8, `spec:hank:thm:field`).
  `F_Γ(√h_1, …, √h_n) = F_{Γ + Σ_k Z v(h_k)/2}` is **exactly** the
  splitting field — not merely an upper field — of degree `2^{dim D_p}`, where
  `D_p` is the span of the classes `v(h_k) + 2Γ` in `Γ/2Γ`, with Galois group
  `Hom(D_p, ±1)`; the same over `K_Γ = C((t^Γ))`. So `p` splits over `F_Γ` iff
  every `v(h_k) ∈ 2Γ` (Corollary 12.9), and a basis-indexed sum of `√h_k` is
  a coefficient-defined primitive element (Corollary 12.10).
- *Factor count and profile* (Theorem 12.13, `spec:hank:thm:profile`). The
  number of irreducible factors of `p` over `F_Γ` is
  `#{k : v(h_k) − v(h_{k−1}) ∈ 2Γ}`. More precisely, the multiplicity
  function `m_p` of the pivot classes `v(h_k/h_{k−1}) + 2Γ` equals
  `Σ_j 1_{D_j}`, one subspace indicator per irreducible factor, with factor
  degrees `2^{dim D_j}`. It rests on Lemma 12.12: square-class multiplicities
  of a positive diagonal form are congruence invariants. Consequences:
  irreducibility without factorization (Corollary 12.14); `m_p` is the
  character multiplicity of the permutation representation on the roots
  (Corollary 12.15); a profile is realizable iff it is a finite sum of
  subspace indicators, and then with all roots positive units (Theorem 12.17).
- *Base change, invariance, precision* (Theorems 12.18, 12.20, Proposition
  12.19, Corollary 12.21). Over any ordered `Γ' ⊇ Γ` the factor count is
  `#{k : v(h_k/h_{k−1}) ∈ 2Γ'}`; the profile is additive for coprime products
  and affine invariant; and if `v(h_k(p̃) − h_k(p)) > v(h_k(p))` for all `k`,
  then `p̃` is squarefree and real-rooted with the same profile and the same
  splitting field.
- *Definite pencils* (Theorem 12.22, `spec:hank:thm:pencil`). For
  `A = A*`, `B = B* ≻ 0` over `K_Γ`, the generalized eigenvalues generate
  exactly `K_{Λ_p}`, computed from the squarefree part `p` of
  `det(XB − A)/det B`, with `r_p ≤ min(⌊d/2⌋, d − m_p(0))`. A size-`2r`
  positive definite pencil realizes any `r`-dimensional `D`, with every
  eigenvalue a positive unit of valuation zero, and no smaller pencil can
  (Theorem 12.24); one primitive eigenvalue costs size `2^r` (Proposition
  12.25).

### What still needs divisibility

`spec:rem:divisibility` (Remark 2.1) says it in one place: the Schur
triangularization of a non-normal matrix (`prop:normal`), the positive square
root of an arbitrary positive semidefinite matrix with the Cholesky
factorization built on it (`prop:positive`), the reduction of the
generalized eigenproblem with its `G`-orthonormal eigenbasis, and obtaining
all eigenvalues of an arbitrary square matrix. These constructions can be
carried out in `Γ ⊗ Q`. The exact cost computed by `spec:thm:ramification`
concerns principal positive matrix roots, not the splitting field of an
arbitrary matrix. **The generalized eigenvalues of a definite pencil no
longer need divisibility:** `spec:hank:thm:pencil` computes their exact field
over an arbitrary `Γ`. Their `B`-orthonormal eigenbasis still can need further
square roots (`spec:hank:warn:normalization`: the `1 × 1` pencil
`A = B = t^γ` has eigenvalue `1`, but a unit vector needs `t^{−γ/2}`). The
pseudospectrum over `K_Γ` and its perturbation characterization remain valid
without divisibility. Everything else — the Hermitian and normal spectral
theorems, the SVD, the polar decomposition, every norm and variational
principle, `thm:scales`, `thm:gram`, the rank filtration, the scale
algorithm, the perturbation certificates, `thm:series`, and all of §12 —
holds over an arbitrary `Γ`.

### The anti-theorems

These are among the most valuable things B and C bring to a report that
worked where they were invisible, and they are kept in full.

- The raw input **monoid** is not preserved, only the subgroup:
  `spec:ex:monoid` has input exponents 3 and 4 and an eigenvalue exponent 5.
- Degrees can **drop** under enlargement of the base group
  (`spec:warn:degreedrop`): `Z ↪ Q` kills all ramification. Degree is
  preserved under isomorphism onto the image, not under enlargement.
  Theorem 12.18 says exactly how factor counts change.
- A Gram witness can use a **larger group than its own product**
  (`spec:ex:gramwitness`) — which is why every statement names both the
  matrix and the base group.
- `(x, y; y, −x)` has **no eigenvalue in `C[[x,y]]`** (`spec:warn:crossing`),
  so this is explicitly not a multivariable analytic eigenbasis theorem.
- Partial sums need not converge even when the Hahn identity holds
  (`spec:ex:nonconvergence`), so a remainder bound is never used as a
  convergence proof.
- Positivity cannot be dropped from the trace theorem
  (`spec:warn:positivity`): the signed root `diag(t^{d/2}, −t^{d/2})` is a
  Hermitian square root generating a quadratic extension whose trace is
  **zero**.
- Membership in `qΓ` is extra group data and need not be decidable from
  black-box order comparison (`spec:warn:qgamma`), so the exact criterion
  `Δ_k ∈ qΓ` may be unevaluable by a representation that can compute every
  `Δ_k`. §12.8 needs the same at `q = 2`.
- Root valuations do not see ramification: `(X − 1)^2 − t^γ` has both roots of
  valuation zero and is irreducible for `γ ∉ 2Γ` (Example 12.26).
- One discriminant is not enough: `X^4 − 2(a+b)X^2 + (a−b)^2` has a **square**
  discriminant and is irreducible with a biquadratic splitting field (Example
  12.28) — it is the orbit polynomial of `spec:ex:biquadratic`.
- The profile does **not** determine the factor degrees or the number of
  base-field roots: `P = p_prim·(X−2)(X−3)` (degrees 4, 1, 1) and
  `Q = (X²−a)(X²−b)(X²−ab)` (degrees 2, 2, 2) have the same profile, the same
  splitting field and the same factor counts over every enlargement, but `P`
  has two base-field roots and `Q` none (Example 12.29).
- The hypotheses are needed (Warning 12.31): `X³ − t` is not real-rooted and
  needs `t^{1/3}`; repeated roots must be removed first; over `Q((t^Γ))` the
  formulas fail.

### Which spectrum this is

`§1.5` fixes the word once. Here *spectrum* is the algebraic **eigenvalue
list** of a finite matrix, with the valuations of eigenvalues and singular
values. It is **not** the differential *phase spectrum* of
[`differential-equations`](../differential-equations/), a multiset of purely
infinite surreal parts of primitives of eigenvalues — not numbers of the same
kind, and not finite angles. It is **not** the *prime spectrum* of a ring,
the sense in which [`analytic-geometry`](../analytic-geometry/) discusses
maximal and prime ideals. It is **not** the spectrum of an operator on an
infinite-dimensional space, which
[`infinite-dimensional-hahn-spectral-theory`](../infinite-dimensional-hahn-spectral-theory/)
treats. And the visible-rank levels `r_{<θ}, r_{≤θ}` of §13 are a list of
scales, not a spectrum in any of those senses. Likewise *profile*: §12's
Hankel square-class profile `m_p` is a multiplicity function on `Γ/2Γ`, not
the determinantal profile `(Δ_k)` and not `polynomial-algebra`'s Newton
profile; and its span `D_p`, built from **leading principal** minors of one
Hankel matrix, is not the group `R_2(A)`, built from minima over **all**
minors.

## Where it sits among the existing reports

It can be read **independently of the analytic coefficient-ring machinery** —
unusually for this family, the `analysis` and `analytic-geometry`
prerequisites do not apply. What it needs is the workspace convention: fix a
set-sized `Γ` and work in `K = C((t^Γ))`, licensed by the localization
theorem in
[`foundations`](../../foundations-and-computation/foundations/) (every *set*
of surcomplex numbers already lies in one such workspace). The article keeps
ordered magnitude, Hahn valuation, strong summability and workspace-relative
topology as four separate structures, and its matrix series theorem is
explicitly *not* a claim of fine-topological convergence — consistent with
[`analysis`](../analysis/), where every set of surcomplex numbers is closed
and discrete in the fine topology.

- [`polynomial-algebra`](../polynomial-algebra/) is the closest neighbour and
  the intended bridge: its Newton profiles of scalar polynomials are what
  `thm:gram` feeds, via the Gram polynomial `det(I + s A*A)`. The adjacent
  matrix ingredients it already carries — an algebraic Schur inequality, the
  differentiating compression, Hermite signature counting — are cited rather
  than re-proved. Its Hermite trace form `T_1` (`polynomial:thm:hermite`) is,
  in the monomial basis, exactly §12's Hankel matrix `H_p`; that theorem
  works over a real closed field, where `Γ/2Γ = 0` and every §12 invariant
  vanishes. Its `polynomial:thm:hensel` is a support-controlled coprime
  Hensel factorization over `K_Γ`, proved by a different recursion than
  Lemma 12.4. Its *rootwise* condition number is a different object from the
  matrix condition numbers here, and the two should not be conflated.
- [`prony-reconstruction-at-surreal-scales`](../prony-reconstruction-at-surreal-scales/)
  shares **only the classical Hankel/moment identity** with §12: `H_p = VᵀV`
  is its weighted moment Hankel matrix at unit weights. No theorem is shared.
  §12 reads the square classes of leading minors over a nondivisible `Γ`;
  that report studies metric stability of perturbed weighted moments. The
  precision certificates sit at different levels (Hankel minors here, moments
  there, coefficients in `polynomial:thm:stability`).
- [`infinite-dimensional-hahn-spectral-theory`](../infinite-dimensional-hahn-spectral-theory/)
  is the infinite-dimensional sibling, with its own hypotheses. It treats
  Hahn–Hilbert spaces, spectra of Hahn operator series, and operators compact
  on an ordinary Hilbert space; no theorem of it is used here, and this report
  remains finite-dimensional.
- [`finite-deformations`](../finite-deformations/) also has Gram matrices,
  but they are **residue** pairings in a finite free Frobenius algebra
  (`det Gram` a unit even where the discriminant vanishes). Those are not the
  positive-definite Hermitian Gram matrices of this article, and no theorem
  transfers between them. §12's trace form is the nondegenerate trace form of
  a squarefree algebra, which degenerates at a repeated root; it is not the
  residue pairing either.
- [`differential-equations`](../differential-equations/) uses eigenvalues of
  constant complex matrices for its non-oscillation results. That is a
  different use of spectra — over `C`, not over `K` — and nothing here is
  needed to read it. Its *phase spectrum* is a different object again; see
  above.
- [`computer-algebra`](../../foundations-and-computation/computer-algebra/) is
  where the exact-operation contracts belong: §14.2, which operations a
  symbolic scalar representation must supply for the scale algorithm to run;
  §14.4, why finite truncation cannot certify every exact rank;
  §14.3, the strictly harder contract for the splitting-tree construction
  together with `spec:warn:qgamma`; and §12.8, the Hankel contract, which
  also needs decisions modulo `2Γ`. That report's own inventory already makes
  a related distinction on the implementation side: a fixed rational exponent
  lattice permits fractional exponents that a fixed integer lattice may lack.
  This is only an exponent condition. Even `sqrt(1+t)` has integer exponents
  but requires an algebraic or series representation beyond rational functions.
  This cross-reference does not claim to solve that
  report's representation or computability problems.
- The letter `h_k` means the Hankel subdiscriminant only in §12. Other
  reports use it for unrelated quantities (for example
  [`markov-generators-at-every-scale`](../../surreal/markov-generators-at-every-scale/)
  and the Prony report).

Two later reports touch this one without extending it.
[differential-equations](../differential-equations/) Part V computes a
non-Hermitian phase spectrum from the eigenvalues of a residual matrix
(`diff:rs:prop:phasespectrum`). [hahn-herglotz-positivity](../hahn-herglotz-positivity/)
gives negative information only about spectral measures: a cyclic algebraic
unitary with no positive coefficientwise spectral measure (`herg:cor:unitary`).

## Scope of the historical coverage audits

The original audit at `e260237` compared the catalogue, the polynomial report's
inventory and opening sections, and nearby matrix material. It distinguished
polynomial-root tools and residue pairings from this report's systematic SVD,
conditioning and singular-scale development. That targeted reading explains
why this report was added; it does not prove that every other source lacked
every relevant theorem. The collection has since expanded, including Hermitian
spectral arguments in differential equations and surquaternions. Consult the
current reader map and local hypotheses when transferring those results.

C's audit at `4cf691c` inspected the reader map with its foundation
conventions, the spectral-theory inventory and opening source, and the
polynomial-algebra inventory. It found
this report's descent, ramification and primitive-trace theorems and
`polynomial:thm:hermite`, and no matching statement of its central package.
This was re-checked for the merge: at `4cf691c` the words "Hankel" and
"subdiscriminant" occur nowhere under `docs/`. The Prony report placed in the
same batch now uses Hankel matrices, for a different question.

## What it does not claim

Every limitation the three manuscripts shipped with is kept here.

**From A and B:**

- A rigorous integrated exposition with a non-Archimedean interpretation.
  **No priority claim**, and no claimed solution of a named open problem —
  manuscript B's status box says it "selects the new theorems alternative in
  the request, not a claimed solution of a named published open problem".
  Real-closed-field spectral theory, the SVD, low-rank approximation,
  pseudoinverses and classical perturbation theory are **not** presented as
  new; nor is priority claimed for the determinantal/valuation consequences.
  The arbitrary-rank determinantal and primitive-trace package is offered as
  a *candidate original contribution* from a targeted, admittedly
  non-exhaustive search; **priority is not certified**.
- Predecessors are conceded, not displaced: Adkins 1991 (normal matrices over
  hermitian DVRs), Keller–Ochsenius 1995 (iterated real Laurent-series fields
  and one infinite-rank Hahn field), Parusiński–Rond 2020, and the February
  2026 preprint arXiv:2602.08313 (Dai–Liang–Lu–Zhi). Neither "a spectral
  theorem beyond `R`" nor "no fractional exponents in a Laurent-series
  eigenbasis" is claimed as new, and the Hahn support foundations are
  standard Hahn–Neumann and word-order ideas, reproved only for
  self-containment.
- No infinite-dimensional operator theory: no Hilbert spaces over `No[i]`,
  bounded-operator spectra, compact or trace-class operators, spectral
  measures. The collection now has
  [`infinite-dimensional-hahn-spectral-theory`](../infinite-dimensional-hahn-spectral-theory/)
  for the first two and for operators compact on an ordinary Hilbert space,
  under its own hypotheses; trace-class operators and spectral measures are in
  neither report, and nothing here depends on that one.
- No global analytic choice of eigenvectors through collisions or across
  multiple parameters, and no removal of the obstructions in the
  multivariable formal power-series category — see `spec:warn:crossing`. What
  *is* now proved is the support-controlled construction for a **single**
  matrix over an arbitrary value group.
- Not effective. The exact decompositions do not by themselves give
  algorithms for arbitrary surreal inputs. The splitting tree is a finite
  tree of **set-valued** support data, not a finite list of monomials — one
  node can carry an uncountable well-ordered support — and exact zero tests,
  support access and leading-coefficient extraction must be supplied by the
  representation. `thm:series` is a strong-summability statement, not
  fine-topological convergence.
- The coefficient fields remain the full `R` and `C`; preservation of a
  smaller coefficient field such as `Q` is **not** asserted.
- All matrix dimensions are ordinary finite integers, and all field and
  extension statements are set-sized. No proper-class sums or class-sized
  Hahn workspaces anywhere.
- The symbolic checks exercise the listed finite identities on their stated
  inputs. They do **not** machine-verify the general proofs, arbitrary Hahn
  supports, arbitrary ordered groups, the proper-class foundations, or an
  effective representation of all surreal numbers. Exact symbolic zero tests
  are not replaced by truncation. Assertion counts include individual zero
  coefficients and are **not** counts of independent theorems. The original
  source reports did not supply a complete proof-assistant formalization.
  The current [coverage ledger](../../FORMALIZATION.md) separately maps checked
  prerequisites and source claims; §21's proposed dependency order is not
  evidence that the whole spectral package has been compiled. These are AI-assisted
  drafts, not refereed. B's PDF metadata names its author as "OpenAI,
  research assistance for Vladimir Reshetnikov".
- The audits behind A and B were targeted. A's
  (`repository-audit.md`) inspected the catalogue, `polynomial-algebra`'s
  full inventory and the opening of its source, and the opening of the
  `foundations` README. B's own source audit, delivered with the
  manuscript, inspected the repo map, the main README, the full spectral
  README, and selected visible material of the differential-equations article. Neither was
  line-by-line, and neither treats a search returning no matches as proof
  that a topic occurs nowhere.

**From C (§12):**

1. §12 is **not a new spectral theorem**. Hahn spectral descent (§9), trace
   forms, the Hermite and Sylvester criteria, and subdiscriminants with their
   Hankel expressions and sums-of-squares identities (Roy; Domokos) are
   classical or already here. Adkins and Keller–Ochsenius 1995 are credited
   for spectral descent. Keller–Ochsenius 2008 already has multiquadratic
   upper fields, power-of-two irreducible degrees and irreducible operators
   built from sums of independent square roots; no priority is claimed for
   those mechanisms or examples. The size bounds and pencil examples use
   elementary group theory and classical radical constructions, not
   advertised as independent discoveries.
2. **Priority is not certified.** The novelty search was targeted; the exact
   formulas may have equivalents in the language of quadratic trace forms,
   ordered valued fields or permutation characters. The package is a
   candidate original contribution with proofs, pending independent review.
   Not refereed; no Lean formalization; the repository's formalizations are
   not asserted to verify it. The checks are finite examples only and do not
   verify the Hahn support theorem, the intermediate-field classification or
   the graded-form invariant.
3. `m_p(0)` counts irreducible **factors**, not roots, and the profile does
   not determine the list of factor degrees or the number of base-field roots
   (Example 12.29).
4. The realizability classification is combinatorial, not an efficient
   search, and indicator decompositions are not unique.
5. The precision certificate is **sufficient, not optimal**. It certifies
   field and factor-count invariants, not roots or their series
   coefficients; the required precision must be known in the ordered group,
   and a truncated prefix is not a certificate.
6. The eigenvalue field of a pencil is **not** the field of a normalized
   eigenbasis (Warning 12.23).
7. Squarefreeness and real-rootedness are essential (`X³ − t`), the constant
   field must be real closed (`Q((t^Γ))` fails), and multivariable
   power-series rings (Parusiński–Rond, Dai–Liang–Lu–Zhi) are not covered.
8. The extensions are **relative**: `F_Γ ⊆ F_{Λ_p}` inside `No`, not
   extensions of `No` or `No[i]` (Warning 12.32). `F_Γ` is the full Hahn
   field, not the field generated by the coefficients. The ambient
   `F_{Γ⊗Q}` need not be algebraic over `F_Γ`.
9. Operation counts are arithmetic counts, not bit complexity, and not the
   cost of an arbitrary Hahn-series oracle. A valuation oracle does not
   decide membership in `2Γ`.
10. No named published conjecture is solved. C's three continuation
    questions (factor-degree lists, efficient pivot parity, non-real-closed
    residue fields), recorded in §21, are directions, not theorems.

## Proof review: 22 September 2026

This review predates manuscript C; §12 was not part of it.

The main mathematical reading followed finite Hermitian geometry, variational
principles, determinantal scales, support-controlled splitting, ramification
and primitive traces, then the stability and matrix-series applications.
The maintained revision clarifies the following boundaries:

- The Gram-factorization criterion uses `2Γ`; `qΓ` controls the principal
  `q`th root. Root-field sums use only `1 ≤ k ≤ rank A`, avoiding the added
  infinite valuations of vanishing higher minors.
- Perturbation statements explicitly retain Hermitian inputs and orthogonal
  projectors. Zero norm squares and the empty Ky Fan sum are treated separately.
- The finite-precision rank obstruction assumes `Γ ≠ {0}`. For the trivial
  group, truncation through zero gives every coefficient.
- The elimination contract includes valuation extraction. Exponent permission
  and full root representation are distinct computational requirements.
- The hypothesis ledger now lists actual assumptions and proof mechanisms in
  their respective columns, including the arbitrary-group scale theorems.
  `O_v(β)` consistently takes an exponent threshold.

Historical verification code and data are unchanged. Imported foundational
results and any complete formalization remain separate from this proof review.
The historical symbolic suites were not rerun for this documentation revision.
The corrections received a second independent review.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
latexmk -c
```

Run from **this** directory. A standard TeX Live or MiKTeX installation with
the packages named in the preamble (AMS, Latin Modern, microtype, geometry,
booktabs, tabularx, longtable, xcolor, enumitem, fancyhdr, titlesec,
hyperref, aliascnt, cleveref) is sufficient. The bibliography is embedded;
there is no BibTeX step, no external figure asset, no custom font, and no
shell escape. Without `latexmk`, run `pdflatex` three times. Last build
(MiKTeX, after the merge of C): **70 pages**, 0 errors, 0 undefined
references or citations, 0 multiply defined labels, 0 LaTeX or package
warnings, 0 overfull and 0 underfull boxes.

None of the three build scripts works from `code/`. All of them
(`code/build.sh`, `code/build.ps1`, their `02-` counterparts, and
`code/03-hankel-ramification-build.sh`) `cd` to their own directory before
compiling `article.tex`, which is in the parent. They were written for flat
delivery layouts — use the command above instead. B's README says its
`build.ps1` was supplied for convenience and was not executed. C's script runs
`pdflatex` three times.

## Rerunning the finite checks

**Run these on a copy of the directory, or redirect the output.** A's and B's
scripts default their output directory to `../data`, and C's script writes
`verification_results.json` into its own directory, so running any of them in
place writes files next to the shipped evidence:

```sh
python -m pip install -r data/requirements.txt                       # sympy==1.14.0
python code/verify-examples.py --output-dir "$TMPDIR/spectral-check"
python code/02-determinantal-ramification-descent-verify.py \
       --output-dir "$TMPDIR/spectral-check-2"
cp code/03-hankel-ramification-check_examples.py "$TMPDIR/check_examples.py"
python "$TMPDIR/check_examples.py" > "$TMPDIR/verification_output.txt"   # never with -O
```

Python 3.9 or newer. No floating-point sampling is used anywhere; A's matrix
generator uses the fixed seed `20260921`, and so does B's finite-quotient
enumeration. C's script uses `assert` statements, so it must not be run with
`python -O`.

The default path is the destructive one for A and B, and nothing in either
script warns about it. B's own README does suggest `--output-dir
rerun-results`, but the argparse default is
`Path(__file__).resolve().parents[1]/"data"` and the two report files are
written there unconditionally. In this repository the ingest renaming happens
to blunt the hazard rather than fix it: B's script writes bare
`verification.json` and `verification.txt`, while the shipped evidence is at
`data/02-determinantal-ramification-descent-verification.{json,txt}`, so a
bare run **adds** files beside the recorded ones rather than replacing them.
The same is true of A's script, which writes underscore filenames while the
delivered evidence was renamed to hyphens, and of C's, which writes
`code/verification_results.json` while the evidence is under `data/`. Do not
rely on that: run on a copy or pass `--output-dir`.

What is recorded, and what has been rerun:

- `data/verification-report.json` and `.txt` are **A's** delivered run:
  **176 exact assertions across 18 matrix-profile cases, PASS**, under
  Python 3.13.5 and SymPy 1.14.0. It was rerun for this collection and passed
  again with the same figures under Python 3.14.4 and SymPy 1.14.0.
- `data/02-determinantal-ramification-descent-verification.json` and `.txt`
  are **B's** delivered run: **PASS, 807 exact scalar assertions** — 378
  projector and polar-series coefficients, 144 finite ramification-group
  checks, 105 rational-matrix checks, 96 character checks, 55 block and
  low-degree terms, 29 displayed identities — across 48 finite quotient cases
  and six rational 3×3 positive semidefinite profiles, with a 3×3 Hermitian
  projector and polar construction checked through formal degree 6 over 1674
  nonzero residue-path contributions. Recorded under Python 3.13.5 and SymPy
  1.14.0. It was **rerun for this collection with an explicit output
  directory and reproduced PASS with exactly 807 assertions and the identical
  category split** under Python 3.14.4 and SymPy 1.14.0 (33.7 s).
- `data/03-hankel-ramification-verification_results.json` and
  `data/03-hankel-ramification-verification_output.txt` are **C's** delivered
  run under SymPy 1.14.0 (the Python version is not recorded), ending "ALL
  EXACT SYMBOLIC CHECKS PASSED". For six polynomials (`X²−a`, `(X−1)²−a`,
  the product and primitive quartics, and the two degree-six polynomials of
  Example 12.29) it computes companion matrices, Newton sums, Hankel minors
  and valuations in `Z + Zω`, and asserts `MᵀH = HM`, `h_n = Disc p`, the
  predicted factor counts and splitting degrees, and the equality of the two
  degree-six profiles; separately, the `2×2` pencil block, the sign-product
  identity of the quartic, affine covariance, squarefree reduction of
  `(X²−a)³`, and the quartic's square discriminant. It records no assertion
  count. It was **rerun for this collection on a copy** under Python 3.14.4
  and SymPy 1.14.0 and reproduced both files exactly, apart from line endings.
- The shipped JSON files of A and B still record Python 3.13.5, because they
  are the delivered artifacts and were deliberately not overwritten.

A's valuation and elimination kernel is restricted to `Q(i)(t,u)`, with
`v(t) = (0,1)` and `v(u) = (1,0)` ordered lexicographically — so `u` is
smaller than every positive finite power of `t` in the corresponding Hahn
interpretation. The **least** polynomial monomial, not SymPy's default
leading monomial, determines the Hahn valuation. The two-by-two spectral
examples are checked separately with exact square-root expressions.

## Shipped-layout notes

Files were renamed on ingest, and text carried over from the manuscripts
still names their delivery paths.

- The historical `repository-audit.md` uses `code/verify_examples.py` and
  `data/verification_report.json`. The maintained Appendix B now uses the
  actual paths `code/verify-examples.py` and `data/verification-report.json`.
- B's §12.2 names `code/verify.py`, `data/verification.json` and
  `data/verification.txt`; the files carry the
  `02-determinantal-ramification-descent-` prefix.
- `03-hankel-ramification-PROOF_AUDIT.md` is C's delivered `PROOF_AUDIT.md`,
  unchanged. Its section and theorem numbers are the manuscript's own. Its
  Sections 2–3 are §12.1 here, Section 4 is §12.2, Sections 5–8 are
  §12.3–§12.6, Section 9 is §12.7, Section 10 is §12.8 with Appendix B,
  Section 11 is §12.9, and Section 12 is §12.10 with §1.4. Statement by
  statement: 2.1 → `spec:lem:scalarroot` at `q = 2`; 2.2 →
  `spec:lem:normroot`; 2.3 → `spec:lem:finiteindex` plus Lemma 12.2; 2.4 →
  Corollary 12.3; 3.1 → Lemma 12.4; 3.2 → the real case of Theorem 9.12,
  with C's proof as Remark 12.5; 4.1–4.2 → 12.6–12.7; 5.1–5.3 → 12.8–12.10;
  6.1–6.4 → 12.12–12.15; its unlabeled Warning 6.5 → Warning 12.16;
  6.6 → 12.17; 7.1–7.4 → 12.18–12.21; 8.1–8.4 → 12.22–12.25.
- C's delivered `README.md`, `article.pdf` (22 pages, pdfTeX 1.40.26 by its
  README), `article.tex` and `SHA256SUMS.txt` (nine files) were not carried
  into the repository.
- `data/build-report.json` is A's, as delivered, and records
  `pdf_bytes: 492771`, which no longer matches the `article.pdf` beside it:
  the PDF is rebuilt on ingest, as every PDF in this collection is, and the
  article has since grown by two merges. Its `article_source_bytes: 88965` was
  exact for A's text as delivered.
  `data/02-determinantal-ramification-descent-build-report.json` is B's, and
  records its own delivered build: pdfTeX from TeX Live 2025/dev/Debian, 3
  passes, 26 pages, 0 TeX errors, 0 package warnings, 0 overfull or underfull
  boxes, 0 unresolved references.
- Both of A's and B's delivery notes list a `MANIFEST.sha256` that was not
  carried into the repository; in B's case no such file was present in the
  delivered package at all. File hashes are not reproduced here.
