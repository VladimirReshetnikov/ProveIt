# Infinitesimal Analytic Geometry over the Surcomplex Numbers

**Radius-Free Germs, a Nullstellensatz, and Finite Maps**

One merged research article, `article.tex` (51 pages compiled), built from
two source manuscripts that prove the *ring* theory of infinitesimal
surcomplex analytic geometry rather than only its deformation theory.

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

## Which archives it came from, and what each contributed

Both sources are in `sources/`.

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

## What is not proved

The article carries a full section on this (Section 14.2), preserving each
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
- The symbolic checks accompanying the source manuscripts validate the
  displayed formulas only. They do not implement arbitrary Hahn fields and
  are not machine verification of the Noetherian, flatness, residue,
  conservation or stability proofs. None of the proofs has been formally
  verified.
- Not established: a global sheaf theory on surcomplex domains, Cartan's
  theorems for such domains, or an extension of ordinary contour integration
  to arbitrary fine-topological paths. The article does not settle the
  supplied manuscripts' separate questions about essential singularities,
  resurgent sectorial summation, or transcendental all-scale atlases.

## Build

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

A standard TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. The bibliography is embedded; there is no BibTeX
step and no external figure asset. Last build: 51 pages, 0 errors, 0
undefined references, 0 duplicate destinations, 0 overfull boxes.
