# Surcomplex Polynomial Algebra

**Root Geometry, Newton Profiles, Multiscale Stability, and Residue Duality**

- `article.tex` — the merged, standalone LaTeX source (internal bibliography, no external `.bib`, no images).
- `article.pdf` — the typeset article, 61 pages.

This report was merged from three archived manuscripts; the manuscripts themselves are not shipped here, and what each one contributed is recorded below.

Build with, from this directory:

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

Last build: 61 pages, 0 errors, 0 undefined references, 0 duplicate hyperref destinations, 0 overfull boxes.

## What the report is

One merged research article on finite-degree polynomial algebra over the
surcomplex class field **SC** = **No**[i], worked inside set-sized
algebraically closed Hahn workspaces *K* = **C**((t^Γ)) with t^γ = ω^(−γ), and
keeping two geometries deliberately apart throughout: the surreal-valued
modulus (ordered disks) and the natural Hahn valuation (valuation balls of
arbitrary ordered-group rank). 78 numbered environments; every `\label` is
prefixed `polynomial:`.

Contents, in order: foundations and support calculus; finite polynomial
algebra, CRT/Hermite jets, resultants and discriminants; ordered root geometry
(root bounds, Gauss–Lucas, weighted incomplete polynomials, Jensen disks, a
sharp Schoenberg second-moment inequality with its equality case);
real-closed-field transfer (order-circle Rouché, Hermite signature counting);
exact root loci under coefficient uncertainty in both geometries; the
initial-polynomial identity and all ball/shell/residue-direction root counts;
Newton profiles over an arbitrary ordered exponent group; image balls, finite
flat maps, branch values and ramification; exact Rolle counts, branch
polynomials, the finite root-cluster tree and two discriminant layer formulas;
support-controlled coprime Hensel factorization and its fixed-domain parameter
form; three perturbation theorems with three different hypotheses; universal
residue duality and the trace identity; Nullstellensatz and finite local
multiplicity; degree-controlled complete intersections, multivariate
Bézoutians and the Jacobian trace formula; a comparison with the supplied
coherent contour residue in a delimited subclass; and a consolidated scope
section.

## Which archives it came from, and what each contributed

The three sources share a main title and a spine — all three prove the finite
polynomial algebra over SC and the FTA there, a surcomplex Gauss–Lucas
theorem, a Rouché theorem in each geometry, root counting from one initial
polynomial, support-controlled coprime Hensel factorization, parameter factor
lifting without repeated domain shrinking, a root-matching stability theorem,
a collision-stable perfect residue pairing with the trace identity, and a
surcomplex Nullstellensatz for finite data. Duplication is high on that spine
and low on the tails; the spine is stated once.

### `13-newton-profiles-order-geometry.tex` — the base

*Order Geometry, Newton Profiles, and Scale-Resolved Stability.* The largest
of the three (2423 lines, 47 environments) and the source of the backbone:

- the initial-polynomial identity and all residue-direction root counts;
- Newton's root-valuation rule over an arbitrary ordered exponent group;
- exact image balls with the two distinct mapping degrees d₋ ≠ d₊;
- the *r*-th derivative critical count (a ball with *k* ≥ 1 roots contains
  exactly *k − r* roots of P^(r));
- the residual critical polynomial and the tree-allocation accounting;
- the **optimal ε/n valuation-Hölder matching** of perturbed root multisets,
  with the exponent proved optimal uniformly, plus the ε/(n−r) derivative
  corollary;
- the **second-order Newton error term** in the stability theorem;
- the **surcomplex Jensen disk theorem**;
- the **sharp Schoenberg second-moment inequality** with the differentiating
  compression, an algebraic Schur inequality, and the collinearity equality
  case;
- the polynomials-versus-Hahn-coherent-entire-data comparison.

### `12-factorization-root-geometry.tex`

*Factorization, Root Geometry, Multiscale Stability, and Residue Duality.*
Carried over into the merge:

- **exact root loci under coefficient uncertainty** in both geometries, with
  the sum-of-magnitudes vs. minimum-of-valuations contrast and the explicit
  phase construction (no sibling has an uncertainty-locus section);
- the named threshold *T(P)* = max_i(d_i + δ_i) with the full
  cluster-preservation conclusion, and its two-sided calibration:
  *T(P)* ≤ *v*(Disc *P*), the collision exactly at threshold, and the explicit
  quartic with *T(P)* = 7 < *D* = 10;
- the telescoping **cluster (level) formula** for *v*(Disc *P*);
- the **universal residue pairing** over an arbitrary commutative ring, with
  the explicit dual basis b^i and no discriminant denominator, and the
  universal trace identity Tr(m_h) = λ_P(P′h) via the Euler derivative
  identity;
- finite polynomial maps: flatness and constant fiber length, the branch-value
  polynomial Disc_z(P − Y), the ramification sums *n* − 1 and 2*n* − 2, and
  the surjectivity/injectivity classification;
- Zariski's lemma and the **class-safe Nullstellensatz for finite data**, with
  the explicit warning that SC[z] does not license Zorn on a proper class, and
  the non-Noetherian witness that m_K is not finitely generated over O_K;
- the ordinary-circle sampling counterexample for order-modulus Rouché;
- the rescaling bookkeeping for using the threshold theorem at infinite
  scales.

### `14-valuative-root-trees.tex`

*Ordered Geometry, Valuative Root Trees, and Residue Duality.* The only one of
the three that leaves one variable. Carried over into the merge:

- **Hermite's signature criterion** over surreal real closed fields, with the
  interval count (sig T₁ + sig T_q)/2;
- the **weighted incomplete-polynomial converse** to Gauss–Lucas (the union of
  root sets is exactly the surreal convex hull);
- the **nearest-neighbour identity** max_{P′(w)=0} v(w − r_i) = δ_i;
- the branch polynomial W_C at a node of the root-cluster tree, and the
  **tree form** of *v*(Disc *P*);
- the escape example z + tz² (a global root invisible in a finite monad);
- the whole several-variable package: finite free normal forms for
  F_i = x_i^{d_i} + E_i with total degree E_i < d_i over an **arbitrary
  commutative ring**; the coefficient-independent perfect Bézoutian pairing
  with Gram determinant ±1; the Bézoutian kernel and **Jacobian trace formula
  through collisions**; Euler–Jacobi vanishing and the local idempotent
  version; support propagation permitting **negative** supports; global
  polynomial families over one fixed ordinary parameter domain; and the
  identification Λ_F = λ_F of the supplied coherent contour residue in a
  delimited polynomial subclass, with the six-dimensional worked example.

### Items stated once instead of three times

The threshold theorem is the clearest case: one source's *T(P)* =
max_i(σ_i + δ_i) with σ_i = v(P′(α_i)) is literally another's *τ(P)* =
max_i(d_i + δ_i) with d_i = v(P′(r_i)) — the same theorem in different
letters. It appears once, as Theorem 13.3, with the union of the three
conclusion lists. Gauss–Lucas, both Rouché theorems, Hensel factorization, the
CRT, the Nullstellensatz and the residue pairing likewise appear once each.
The ε/n Hölder theorem is **not** merged into the threshold theorem: it needs
no root-separation hypothesis at all and returns a much weaker bound, so the
two have different hypotheses and both are kept, with the difference stated
explicitly.

## Notation and ring discipline

One symbol per concept, fixed in §1.3 with the synonyms recorded once and then
never used again: F_Γ/K_Γ (not R_Γ); `st` for the standard part (not `red`;
the induced topology is the **standard-part topology**, not the "residue",
"reduction" or "shadow" topology); B_≥/B_> for valuation balls and D/D̄ for
order disks; ρ for the scale; w_{a,ρ}(P) and I_{a,ρ}(P) (not g_P(a,γ), not
"reduction polynomial"); α_i for roots; d_ij, d_i, δ_i, T(P); E and ε for a
perturbation and its precision.

§1.4 fixes the coefficient rings and every theorem names its own. The report
uses exactly three: K (and O_K) for all univariate root/ball/precision
statements; the **fixed ordinary domain** ring H_Γ(U) = O(U)((t^Γ)), with its
nonnegative- and positive-support subrings, for the three parameter theorems
and the coherent-families discussion; and an arbitrary commutative ring for
the universal duality theorems. C[z]((t^Γ)) appears only as a counterexample
ring. **No theorem here is stated over a radius-free ring C{z}((t^Γ)) or a
formal-coefficient ring C[[z]]((t^Γ))**, and no theorem was moved between
rings.

## What is not proved

The consolidated status statement and the full per-theorem non-claim list are in
§18.1–18.3 of the article. In summary:

- This is a research exposition. It claims no first occurrence in the
  literature, certifies no priority, and resolves no named published
  conjecture. Several central statements are classical over real-closed
  fields, valued fields, or arbitrary commutative rings and are identified as
  such. Nothing has been refereed or machine-checked; the symbolic checks in
  the source archives validate displayed finite examples, not the general
  proofs, and certify nothing about arbitrary Hahn supports, arbitrary-rank
  groups, transfinite summability, class-set foundations, or quantifier
  elimination. No theorem is declared new merely because "surcomplex" is in
  its title.
- **Strong summability is not a limit.** The support lemma does not say the
  partial sums converge in the fine surreal topology, and does not say that
  *k*ρ eventually exceeds every positive value-group element — false in higher
  rank. Neither false cofinality claim is ever substituted for the lemma. "Only
  finitely many dependencies at an exponent" does not mean "only finitely many
  exponents below it."
- **No contours.** Nothing here asserts a contour representation of any
  residue. λ_P and λ_F are defined by finite polynomial division. The only
  place a contour functional appears is the Λ_F = λ_F comparison, which holds
  only under *both* the lower-total-degree and the positive-support
  hypotheses, over the fixed-domain ring, and which does not settle the
  general analytic case. The order-circle Rouché theorem is a transfer
  theorem, not an integral along a fine-continuous surreal circle, and is not
  the same statement as the leading-coefficient Rouché theorem on ordinary
  thickened domains in the supplied analysis manuscript.
- **Two disagreements in the wider manuscript set are recorded, not
  averaged**, in §17: whether an arbitrary isolated complete intersection's
  perturbation residue has a contour representation (proved unconditionally in
  one manuscript, assumed conditionally on an unrefereed companion in a
  second, and explicitly declined and listed as an open problem in a third —
  the resolution prints the proof in the companion contours report *with* the
  declining manuscript's scope discussion alongside), and whether
  roots-of-unity quadrature recovers the Hahn contour integral (compatible:
  the positive theorem must be stated *with* its decay hypothesis, and the
  negative example kept alongside as proof that the hypothesis cannot be
  dropped).
- **Transfer is a scheme**, one sentence per fixed finite degree bound; it
  transfers no quantification over functions, sequences, arbitrary subsets or
  the integers as a definable set, and makes no proper class into a first-order
  model.
- Gauss–Lucas is proved without compactness or a separation theorem, and
  describes nothing about how critical points distribute among infinitesimal
  clusters. Jensen's theorem concerns F-valued disks, not ordinary pictures
  obtained by discarding infinitesimals. Hermite's signature form is not the
  nondegenerate residue pairing.
- The exact Rolle count needs an *occupied* ball (m = 0 is not permitted) and
  residue characteristic zero. The derivative-of-initial-polynomial lemma
  needs a nonconstant initial polynomial.
- The stability theorem asserts nothing about equality of roots, of their
  ordinary moduli, or of every Hahn coefficient of the pairwise differences;
  the tree corollary preserves the *allocated* critical directions, not every
  individual critical multiplicity. The sharp-collision example proves
  strictness in its family only; the discriminant threshold is shown not to be
  optimal.
- The universal residue pairing is the polynomial core of the supplied
  one-variable duality, not a new general duality theorem; the univariate
  trace identity is not a proof of the general multivariable Jacobian
  comparison.
- The degree hypothesis on the complete-intersection family is a genuine
  restriction, not a disguised assertion about all isolated complete
  intersections; positive Hahn support alone does not preserve global degree
  or the total root count over SC.
- Finite algebraic operations on arbitrary Hahn inputs are well defined but
  not automatically effective; Noetherianity of the supplied analytic
  coefficient rings is not asserted, and already O_K has the non-finitely
  generated ideal m_K.
- O(t^k) always means a formal Hahn series supported in exponents ≥ k, never a
  fine-topological or numerical asymptotic estimate obtained by varying t.
