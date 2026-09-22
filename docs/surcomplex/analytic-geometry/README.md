# Infinitesimal Analytic Geometry over the Surcomplex Numbers

**Radius-Free Germs, a Nullstellensatz, and Finite Maps**

One merged research article, `article.tex` (73 pages compiled), built from
three source manuscripts that prove the *ring* theory of infinitesimal
surcomplex analytic geometry rather than only its deformation theory.

## Provenance

| Source manuscript | What it is the sole source of | Where it lands |
|---|---|---|
| `01-radius-free-germs-nullstellensatz.tex` | the radius-free ring `A_n`, its strictness over `R_n`, germ-level division and preparation, the Noetherian / weak / strong Nullstellensatz / regularity package over `A_n`, workspace invariance and the full-surcomplex corollary, the analytic–formal comparison, the quantitative Hensel–Rouché theorem with root matching, and the two `A_2` examples | §3.1, §4.1, §5, §11.1, §11.2, §12, §§13.1–13.2 |
| `07-finite-geometry-of-zeros.tex` | Noether normalization and finite maps over `R_n`, parameterized preparation and division on one fixed ordinary domain, the Koszul conjugacy and the vanishing of all higher Koszul homology, the base-change theorem, the contour-expansion residue `Lambda_F` and the constant residue frame, the length-five collision and the nonpolynomial corollary, and the predecessor assessment governing the novelty section | §1.4, §3.2, §4.2, §§6–7, §9.3, §10.1, §11.1, §§13.3–13.4 |
| `08-corona-obstruction-spectral-fibres.tex` | the entire positive theory of the **fourth** ring, the fixed-polydisk ring `O(D)((t^Gamma))`: uniform Banach norm, fixed-divisor interpolation quotient, the exact finite-leading-valuation unit and Bézout criteria, the normed corona obstruction, the geometric DVRs, and the prime spectrum with its continuum chain in one fibre | §§14–17, plus the fixed-polydisk row of §1.2 and the fifth overview theorem in §1.3 |

Their code and data are in `code/` and `data/`, under the same filename
prefixes.

## What the report is

Fix a nonzero divisible set-sized ordered subgroup `Gamma` of the surreal
numbers and put `K = C((t^Gamma))`, algebraically closed by Poonen's
Corollary 4. The article studies the infinitesimal neighbourhood (the
*monad*) `m_K^n` of an ordinary point, over **two** coefficient rings whose
theorems look nearly identical and are not interchangeable:

- `A_n = C{z_1,...,z_n}((t^Gamma))` — the **radius-free** ring: each Hahn
  coefficient is an ordinary convergent germ, with **no** common radius of
  convergence required;
- `R_n = lim_U H_Gamma(U)` — the **common-domain** ring: germs of Hahn
  families all of whose coefficient functions are holomorphic on *one*
  ordinary neighbourhood.

Two further rings appear in the naming table and are kept distinct from
these: the fixed-polydisk ring `O(D)((t^Gamma))` and the formal-coefficient
ring `F_n = C[[z]]((t^Gamma))`. The article proves

    O(D)((t^Gamma))  ->  R_n  (strictly contained in)  A_n
                             (strictly contained in)  F_n,

with explicit witnesses in both directions, and proves *separately of each
of* `A_n` *and* `R_n` that it is a Noetherian Jacobson domain of dimension
`n` whose maximal ideals are exactly the infinitesimal evaluation ideals
`m_a = (z_1-a_1, ..., z_n-a_n)`, `a` in `m_K^n`, with residue field `K`,
regular local rings, and completions `K[[X_1,...,X_n]]`. Neither ring is
local: each records every infinitesimal point at once, which is the formal
content of the distinction between a stalk on the whole monad and a fine
germ at one surcomplex point.

Every numbered statement names the ring it is about. No theorem proved of
one ring is transferred to another; where a statement holds of both rings it
is stated twice, with the two proofs given and compared, because the proofs
use different resources (germ-level division with no fixed domain, versus a
fixed ordinary domain supporting Cartan's theorem B and an ordinary residue
cycle).

### The fourth ring, and what it does and does not satisfy

The same package is **not** claimed for the fixed-polydisk ring
`O(D)((t^Gamma))`, here or anywhere in this collection. §1.2 records the
obstruction the companion finite-deformations report supplies — the positive
ideal of the positive-support coefficient ring is not finitely generated
when `Gamma` is nonzero and divisible — and states what that report actually
proves over the fixed polydisk, which is the deformation package without
Noetherian hypotheses rather than with them. An earlier revision of §1.2
asserted the package for all four rings and mis-attributed the fourth case;
that sentence was retracted in commit `d0e61c4`, and the mis-citation was
this report's own. The finite-deformations report is not its source and is
not being criticised.

§§14–17 now give the fourth ring its own positive theory, for `D` the
ordinary unit disk in one variable, and the picture splits cleanly:

- **Locally it is as good as the germ rings.** At every geometric point
  `a` of `D^# = {c + eps : c in D, v(eps) > 0}` the evaluation ideal
  `(z - a)` is maximal with residue field `K`, its localization is a
  discrete valuation ring of dimension one, and its completion is `K[[X]]`.
  This is proved directly, from a global Taylor divided-difference identity,
  and never from a global Noetherian statement.
- **Globally almost nothing else survives.** For `Gamma = R` the ring is a
  complete uniform non-Archimedean Banach `K`-algebra whose norm is exactly
  the supremum of actual surcomplex evaluations, so neither incompleteness
  nor a norm/geometry mismatch is available as an excuse; and in it the
  explicit pair `h(z) = sin(pi/(1-z))`,
  `F = sum_n t^(2 - 1/n) e_n` satisfies `||h|| = 1`, `||F|| = e^-1`,
  `inf over D^# of max{|h|_v, |F|_v} = e^-2` exactly (not attained), and
  `inf over U,V of ||1 - hU - FV|| = 1`. So `(h,F)` is a proper,
  nonprincipal, two-generated ideal with **empty geometric zero set**, local
  Bézout identities exist on ordinary neighbourhoods of every point of `D`
  while no global one does, and no enlargement of the value group repairs
  it. A change of function class, not of workspace size, would be required.
  In particular no Nullstellensatz `I(Z(I)) = sqrt I` can hold for finitely
  generated ideals of this ring, in sharp contrast to §§5.3 and 6.
- **The exact criterion is finiteness, not boundedness.** Modulo the fixed
  simple divisor `h`, a nowhere-zero value family is invertible precisely
  when its set of leading valuations is *finite*; the counterexample
  exponents `2 - 1/n` are bounded and increasing, which is why boundedness
  is not enough. The proof is a two-orders lemma: a set well ordered in both
  its own order and its reverse is finite.
- **One fibre of its prime spectrum is infinite-dimensional.** Over a single
  classical free maximal ideal `m_U` of `O(D)`, growth gauges produce a
  continuum-sized strictly descending chain of primes `P_r`, all contracting
  to `m_U`, all with the same norm closure `P_0` while their inclusions stay
  strict, and all lying below an explicit **nongeometric** maximal ideal
  `J_U` (coefficientwise reduction to `k_U((t^R))`). The ascending chain
  `P_1 ⊂ P_(1/2) ⊂ P_(1/3) ⊂ ...` refutes Noetherianity directly — not by
  the invalid inference from infinite Krull dimension alone — and no `P_r`
  is contained in any evaluation kernel, so these primes are genuinely
  nongeometric rather than evaluation at a point with an overlooked
  infinitesimal displacement. The corona element `F` is an explicit nonzero
  element of `J_U / Q_U`, so coefficientwise Hahn reduction is not scalar
  residue-field base change.
- **Real forms and value-group sensitivity.** The same pair works in the
  conjugation-symmetric real form, with constant field `R((t^R))` inside
  `No`. And for a *discrete* rank-one `Gamma = Z*delta` — where the article
  deliberately drops its own standing divisibility hypothesis — a bounded
  well-ordered valuation set is finite, so for that pair a uniform upper
  bound on `v(F(a_n))` does imply solvability; the unbounded variant
  `sum_n t^(n*delta) e_n` still gives a proper zero-free two-generated
  ideal, and the prime chains already exist over `O(D)((t^Z))`.

The fixed-divisor interpolation quotient `H/(h) ≅ B_Gamma` used throughout
§§14–17 is credited to the companion global-divisors report as the simple
undeformed case of its support-restricted Chinese remainder construction,
not relabelled as new. None of this transfers to `R_n`, `A_n` or `F_n`: it
needs infinitely many ordinary centres approaching the boundary of the fixed
disk, a resource lost on localizing at one centre. It also does not refute
the finite-isolated-zero deformation theorem, since `h` has infinitely many
ordinary zeros; at each individual geometric point the DVR theorem
independently confirms the positive regularity statement.

## Which archives it came from, and what each contributed

The three source manuscripts are not shipped with this report; each arrived
with its own README and, for the third, its proof audit, and what each one
contributed is recorded below.

### `01-radius-free-germs-nullstellensatz.tex` — the base

Contributed, and is the sole source of:

- the **radius-free ring** `A_n` and the proof that it is a *strict*
  enlargement of the common-domain ring: Example 3.7,
  `F(z) = sum_{r>=1} t^{r*eta}/(1 - r z)`, whose coefficient at `r*eta` has
  a pole at `1/r`, so no common ordinary disk carries the family (article
  Example 3.10);
- support-controlled Weierstrass division and preparation over `A_n`, and
  the prepared-hypersurface fibre corollary;
- the full Noetherian / weak / strong Nullstellensatz / regularity package
  over `A_n`, with the remark that the **nonzero-value-group hypothesis is
  essential**, not aesthetic: for `Gamma = {0}` the strong Nullstellensatz
  fails at `I = (0)`;
- **workspace invariance** and the **full-surcomplex corollary**: every
  common zero over any larger divisible workspace already lies in
  `K_Gamma^n` with unchanged multiplicity, so the count `sum_a e_a = mu`
  accounts for all zeros infinitesimal relative to `C` in the whole proper
  class `SC = No[i]`;
- the **analytic–formal comparison**: `A_n -> C[[z]]((t^Gamma))` is
  faithfully flat, with the same maximal ideals, residue fields,
  completions and finite-colength quotients; strictness witness
  `sum r! z^r`;
- the **quantitative Hensel–Rouché theorem** with root matching, the
  inverse-Jacobian valuation loss `kappa_a`, the separation corollary, the
  finite-cluster bijection, and the example proving the strict factor two
  sharp;
- the four-root example `F_1 = x^2 - Ay`, `F_2 = y^2 - Bx` splitting across
  different valuation ranks, and the genuinely radius-free two-variable
  system `F_1 = x^2 + sum_{r>=1} t^r/(1 - r x - r^2 y)`, `F_2 = y^2 + t^w x`
  over `Gamma = Q + Q*omega`, with the boxed residue `Res_F(1) = -4t + R`,
  `v(R) > 1` — infinite individual residues summing to an infinitesimal.

### `07-finite-geometry-of-zeros.tex`

Contributed, and is the sole source of:

- **Noether normalization** over `R_n`, and with it the **finite surjective
  projections** of irreducible monad zero sets and the generically reduced
  finite-fibre statement (exactly `r = [Frac(A):Frac(B)]` distinct reduced
  preimages off one hypersurface). The base has only the
  prepared-hypersurface fibre corollary and no normalization;
- parameterized preparation and division on one fixed ordinary domain, via
  the contour operators `R_0`, `D_0`;
- the **Koszul conjugacy** `D = U d U^{-1}`, `U = 1 + delta h`, and with it
  the **vanishing of all higher homology of the Hahn Koszul complex** — a
  statement the base's argument does not produce;
- the **base-change theorem** stating that enlarging the value group changes
  neither the multiplication matrices nor the root set. The base proves the
  corresponding workspace invariance differently; the article states both
  and compares the proofs rather than duplicating one;
- the contour-expansion residue functional `Lambda_F`, its collision-stable
  perfect pairing, and the constant residue frame `S = (I+C)^{-1/2}` with
  `S^T G_F S = G_0`;
- the **length-five collision** example `F_1 = x^2 - y^3 - s`,
  `F_2 = xy - u`, with multiplication matrices, the collision equation
  `3125 u^6 - 108 s^5 = 0`, the projected-discriminant artifact
  `u^2 (3125u^6 - 108s^5)`, the three scale regimes, and the Gram
  determinant identically one;
- the nonpolynomial, non-grid-support corollary with
  `T = {2 - 1/m} u {sqrt 2, 3}`;
- the **predecessor assessment that governs the merged novelty section**:
  Cluckers–Lipshitz–Robinson on multivariable preparation and division for
  nonstandard analytic structures, and Cluckers–Lipshitz on analytic
  coefficient families with a common radius and arbitrary well-ordered Hahn
  supports including their Nullstellensatz, named as close and substantial
  antecedents, with novelty for those general ideas disclaimed.

### `08-corona-obstruction-spectral-fibres.tex`

Contributed, and is the sole source of, everything in §§14–17 — the whole
positive theory of the fixed-polydisk ring, summarized in the bullets
above. In detail it is the sole source of:

- the **uniform Banach structure**: `H(D)` is complete and multiplicatively
  normed, with `||F||_H = sup over D^# of |F(a)|_v` and the supremum
  attained at an ordinary point of `D`, plus the distance lemma giving
  `inf over A in I of ||1 - A||_H = 1` for every proper ideal;
- the **cardinal-function divisor** `h = sin(pi/(1-z))` with simple zeros
  `a_n = 1 - 1/n` and `h'(a_n) = pi n^2 (-1)^n`, the unrestricted ordinary
  interpolation lemma on the same disk, and the resulting quotient
  `H_Gamma(D)/(h) ≅ B_Gamma` — the last credited to the global-divisors
  report, not claimed as new;
- the **two-orders lemma** and the exact unit criterion in `B_Gamma`
  (all coordinates nonzero *and* the leading-valuation set finite), with
  the explicit support certificate for the inverse, the failure of
  inverse-closedness in `l-infinity(N,K)`, and the matrix corollary;
- the **exact Bézout criterion** modulo `h`, together with its invariance
  under every ordered value-group extension;
- the **normed corona counterexample** with its sharp constants and the
  case split on `q = v(eps)` below or at least `2`, the local Bézout
  sections on ordinary neighbourhoods, nonprincipality by a
  leading-coefficient argument, the observation that every *finite* set of
  centres is solvable via `V_J`, and the explicit statement that this
  contradicts neither Carleson nor Hahn-meromorphic Fredholm theory;
- the **support-controlled divided difference** on the whole fixed disk,
  and with it the geometric evaluation ideals, the finite spatial order of
  vanishing `d_a`, the DVR theorem and the `K[[X]]` completion — proved
  without any global Noetherian input;
- the **growth-gauge primes**, their primality proof via ultrafilter
  complements, the dependence on growth *class* rather than normalization,
  the continuum chain with explicit separating witnesses, the contraction
  to one classical free maximal ideal, the distinction between `Q_U` and
  `J_U`, the infinite-dimensional fibre with its explicit non-Noetherian
  ascending chain, the closure collapse with `dist(F, P_0) = e^-2` not
  attained, the base-change failure, and the invisibility of the whole
  chain at every geometric point;
- the **real form** and the **discrete-value-group** discussion;
- the insistence that three valuations — `v` on scalars, `v_H` on
  coefficient families, and the spatial order `d_a` — be kept apart, which
  is what makes local dimension one and an infinite-dimensional global
  fibre compatible rather than contradictory.

### Deduplication

The two ring-theoretic halves overlap in statement but are theorems about
two different rings, one proved strictly larger than the other, so the
merge states both. The deformation halves were straightforward duplication
and are handled once: the article states the deformation theorem over each
ring, gives the two distinct proofs, proves that the two residue
functionals agree where both are defined, and refers the rest of the
deformation package — stated at its strongest hypotheses, together with the
second stability certificate — to the companion report on finite
deformations. The article's own distinctive contribution to that package is
that it survives the **removal of the common-radius hypothesis**, which is
exactly what Example 3.10 and the faithful-flatness theorem are for.

The third source overlaps the first two only in its foundations, and those
are not restated: the Hahn–Neumann support lemma, the definition of strong
summability, positive-support operator inversion, and the strong
summability of Taylor evaluation on `H_Gamma(U)` are already §2 and §3.2 of
the article, so §§14–17 cite them and add only the valuation estimate
`v(F(a)) >= v_H(F)` that §3.2 does not record. Its DVR theorem is *not* a
duplicate of the regularity statements over `A_n` and `R_n`: it is the same
statement about a fourth ring, proved by a different route, and
Convention 1.1 (ring discipline) forbids transferring any of them. Its
interpolation quotient is credited to the global-divisors report rather
than merged in as new.

## What is not proved

The article carries a full section on this (Section 18.2), preserving each
source's own non-claims. In summary:

- Multivariable Hahn–Weierstrass theory and non-Archimedean Nullstellensatz
  results have substantial published predecessors and are **not** claimed
  here as new general ideas. The coefficient ring and its support
  restrictions must be compared, not just theorem titles. No claim that
  either ring lies outside every broader analytic-structure framework.
- No named published conjecture is claimed solved; no exhaustive priority
  certification is asserted; the search was targeted, made 21 September
  2026. This is a proposed original synthesis, not a certified first
  theorem in multivariable non-Archimedean analysis.
- No proper-class polynomial ring or proper-class sum is used. Every ring
  theorem concerns a fixed set-sized `Gamma`; the passage to the full class
  is made by explicit base change, one finite cluster at a time.
- The support bounds are support bounds, not real norm estimates, and not a
  claim that successive approximations converge in the surreal fine
  topology. Strong summability remains the definition of the series.
- The Hahn residue is **defined** by its strongly summable series, not by a
  putative surcomplex contour integral; supplying such a contour is a
  separate task. The ordinary cycle used over `R_n` is an ordinary cycle and
  is not treated as a fine-continuous object in `SC^n`.
- The finite-projection statements are algebraic (finite module, finite
  fibres). No properness, compactness or path lifting in the fine topology.
  The hypersurface fibre statement does not assert that roots can be
  globally labelled by single-valued analytic functions through a branch
  locus.
- The Nullstellensatz gives existence of a witness, not a complexity bound.
  The normal-form recursion is effective only relative to available ordinary
  division maps and an effective presentation of the support; no finite-time
  enumeration algorithm is claimed for every set-theoretically possible Hahn
  input, though the finite-dependence statement at a specified coefficient
  is unconditional.
- The linear splitting and the Koszul contraction are choices; no
  uniqueness, no norm bound, no continuity is asserted for either.
- The Koszul conjugacy is stated for a complex with homology only in degree
  zero; with homology in several degrees a positive perturbation can produce
  a nontrivial differential on the homology space.
- Conservation protects total *length*; it neither requires nor implies that
  the number of distinct points stays constant. The constant residue frame
  identifies bilinear spaces, not algebras, and does not erase the
  nonreduced structure of a collision; the simple-root residue formula is
  invalid at a multiple point.
- No Noether normalization or finite-projection theorem is claimed for
  `A_n`, and no analytic–formal comparison is claimed for `R_n`.
- The relative version over a positive-dimensional ordinary parameter space
  (normal forms as modules over the coherent parameter algebra) is
  deliberately **not** claimed.
- The attainment of both valuation bounds in the Hensel–Rouché theorem,
  including the second-order bound, is proved in the companion
  finite-deformations report and is not re-proved here. That report also
  carries the complementary discriminant-threshold certificate, which
  declines root matching entirely; the article records which certificate is
  sharper for which purpose rather than averaging them.
- For the fixed-polydisk material: whether the ring is **Jacobson** is not
  settled either way, and **no classification of its abstract maximal
  ideals** is claimed — `J_U` is one explicit nongeometric maximal ideal
  built from one chosen ultrafilter. The growth-gauge primes are not
  claimed to exhaust the fibre over `m_U`, and the bounded-valuation
  obstruction of the corona pair is not one of the faster-than-polynomial
  gauge conditions; relating bounded support cuts to the remaining primes
  of that fibre is left open.
- Nothing in §§14–17 transfers to `R_n`, `A_n` or `F_n`, whose packages
  stand as proved, and nothing there refutes the finite-isolated-zero
  deformation theorem of the companion report: `h` has infinitely many
  ordinary zeros, so that hypothesis is simply absent. The §1.2 correction
  concerns this report's own former overview sentence and is not a
  criticism of that report.
- The corona obstruction is **not** asserted to contradict Carleson's
  corona theorem or Hahn-meromorphic Fredholm results: the scalar field,
  the absolute value and the function class all differ, and every nonzero
  ordinary complex constant has valuation norm one here.
- The prime-spectrum half assumes a nonprincipal ultrafilter on the
  positive integers — available in ZFC, not constructible, and not
  exhibited. The Bézout criterion, the corona counterexample and the DVR
  results are free of that input.
- The discrete-value-group discussion is a statement about one particular
  pair over one particular group, not a general theorem that bounded
  valuations suffice for solvability.
- The classical inputs of §§14–17 are conceded, not claimed: the
  Hahn–Mal'cev–Neumann support lemma and positive-support inversion,
  ordinary discrete interpolation, ordinary free maximal ideals, and
  growth-rate prime constructions (Henriksen; Kang–Toan). Merely producing
  an infinite-dimensional global function ring would not justify a novelty
  claim, and none is made on that basis.
- The symbolic checks accompanying the source manuscripts validate the
  displayed formulas only. They do not implement arbitrary Hahn fields and
  are not machine verification of the Noetherian, flatness, residue,
  conservation or stability proofs. None of the proofs has been formally
  verified, and no proof-assistant certification is claimed or supplied
  for any statement in this report; no Lean files ship with any source.
- **The third source's recorded check count is deliberately not quoted as
  evidence anywhere.** Its delivered checks are finite consistency checks
  (exponent arithmetic, cardinal-function identities, polynomial divided
  differences, a rational grid of valuation inequalities, finite
  positive-support inverses, finite gauge witnesses); they compute no
  infinite Hahn series, construct no ultrafilter, verify no infinite prime
  chain, prove no completeness, establish no primality at arbitrary real
  rates, and establish no novelty, and several sub-results are recorded in
  the delivered output as "written proof only". An audit found that the
  valuation-inequality routine asserts, inside the branch `q < 2`, the
  condition `q < 2` itself, so a large share of the recorded cases test
  nothing; the delivered layout audit has no generating script at all; and
  the recorded verification file is rewritten in place by the script that
  produces it, so it is not an independent record. Page-count and
  text-boundary audits are typesetting checks, not mathematical
  verification.
- Not established: a global sheaf theory on surcomplex domains, Cartan's
  theorems for such domains, or an extension of ordinary contour integration
  to arbitrary fine-topological paths. The article does not settle the
  supplied manuscripts' separate questions about essential singularities,
  resurgent sectorial summation, or transcendental all-scale atlases. Two
  further questions are recorded as open in §18.3: a support-theoretic
  criterion for a general finite row to be unimodular in the fixed-polydisk
  ring (the pointwise minimum of leading valuations is provably not
  sufficient data), and a replacement function algebra with a valid corona
  principle — enlarging the scalar field alone is ruled out.

## Build

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

A standard TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. The bibliography is embedded; there is no BibTeX
step and no external figure asset. Last build: 73 pages, 0 errors, 0 LaTeX
warnings, 0 undefined references, 0 undefined citations, 0 multiply-defined
labels, 0 duplicate destinations, 0 overfull boxes.

## Notation review — 22 September 2026

The notation convention now defines the standard-part topology on all finite
tuples and explicitly identifies its restriction to the zero monad as
indiscrete. The scalar reduction map and the algebraic results are unchanged;
the pullback topology is distinguished from intrinsic valuation and full
surreal fine topology.

The fixed-disk corona example is also traced explicitly into the common-domain
germ ring: its leading coefficient is nonzero at the origin, so one common
shrinking makes `F` invertible and the formerly proper ideal becomes the
whole germ ring. This illustrates why the fixed-disk obstruction does not
transfer to germs.
