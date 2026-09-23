# Vector and Tensor Fields over the Surreal Numbers

**Admissible calculus in every dimension, three-dimensional vector calculus, and Minkowski fields**

A merged research report dated 22 September 2026. It is built from three
manuscripts written independently on that day against repository pin `d22a5b3`,
and was merged after placement commit `5fe7f8d`. Prepared for Vladimir
Reshetnikov. It is an AI-assisted research draft. It has not been refereed, and
none of it has a Lean formalization.

```
article.tex                    the report, standalone LaTeX with an internal bibliography
article.pdf                    the compiled report, 89 pages
README.md                      this guide
02-minkowski-SOURCE_AUDIT.md   source 02's repository and literature audit, as delivered
code/  01-vector-tensor-fields-n-verify.py              (source 01)
       01-vector-tensor-fields-n-Makefile               (source 01; see "Build and reproduce")
       02-minkowski-check_identities.py                 (source 02)
       02-minkowski-Makefile                            (source 02; see "Build and reproduce")
       03-three-dimensional-fields-verify_examples.py   (source 03)
data/  01-vector-tensor-fields-n-verification.txt       (source 01)
       02-minkowski-requirements.txt,
       02-minkowski-verification_log.txt,
       02-minkowski-verification_results.json           (source 02)
       03-three-dimensional-fields-verification_results.txt  (source 03)
```

The files in `code/` and `data/` and the source audit are byte-identical to the
delivered ones. The three manuscripts themselves are not shipped.

Every `\label` in `article.tex` carries the prefix `vtf:`. Material from source
02 carries `vtf:mink:` and material from source 03 carries `vtf:3d:`, wherever
it is placed. The report has 222 labels. All 73 labels of the base manuscript
(source 01) are kept as `vtf:<original>`, so none is lost; 78 labels carry
`vtf:mink:` and 48 carry `vtf:3d:`. The
[formalization ledger](../../FORMALIZATION.md) maps no `vtf:` label.

## Three sources, one report

| | Manuscript (as delivered) | Pin | Placed in |
|---|---|---|---|
| **01** | *Vector and Tensor Fields over the Surreal Numbers: admissible calculus, differential geometry, and multiscale field equations*, an n-dimensional framework (31 pp.) | `d22a5b3` | The base: Part I (Sections 1–20), the synthesis (Section 41), the notation ledger and the first part of the audit. Files prefixed `01-vector-tensor-fields-n-`. |
| **02** | *Surreal-Valued Fields on Minkowski Space: Lorentz geometry, tensor calculus, and causal Hahn dynamics* (37 pp.) | `d22a5b3` | Part III (Sections 29–40) and Appendix B. In Part I it supplies Theorem 19.1 (with 03), Section 19.2, the cohomology theorem 12.1 (with 03), the distribution section 19.3 and several remarks. Files prefixed `02-minkowski-`. |
| **03** | *Three-Dimensional Surreal Vector and Tensor Fields: support-controlled differential geometry, integral theorems, and multiscale continuum equations* (33 pp.) | `d22a5b3` | Part II (Sections 21–28). In Part I it supplies Theorems 4.2, 4.3, 12.1 (with 02), 12.4 and 16.2, Propositions 5.1 and 18.1, and Section 13.1. Files prefixed `03-three-dimensional-fields-`. |

Source numbers are local to this directory. The page counts are those given in
the delivered READMEs.

**Why one report.** All three manuscripts build the same layered theory, in the
same order. The first layer is finite algebra over a set-sized real-closed
surreal subfield `K = R((t^Γ))`. The second is Hahn series of ordinary smooth
tensor fields on real manifolds. The third is Taylor prolongation or scale
charts to genuine surreal-coordinate neighbourhoods. Source 01 is the base
because it is the most general: every finite dimension, every nondegenerate
signature, and intrinsic derivatives of the prolongation. Source 03 adds the
three-dimensional material (dot and cross products, integral theorems,
continuum equations). Source 02 adds the Lorentzian material (Lorentz
transformations, the Lorentzian Hodge operator, Maxwell and scalar fields,
stress–energy, causal solution operators). Each part keeps its own hypotheses.

**Printed once.** The following appear in two or three sources and are printed
once, with the other sources named at that point; Appendix C.2 lists them all:
the workspace, valuation, standard part and Neumann support lemma (Section 2);
finite tensor algebra and bounded-frame valuation invariance (Section 3); the
common-domain algebra, the sheaf obstruction and the example `x²+ε²` (Section 4);
Taylor–Hahn prolongation (Theorem 5.2); Lie, Cartan and covariant calculus
(Sections 7–8); regular-metric inverse, Levi–Civita connection, curvature and
Bianchi identities (Sections 8–9); the Hodge star and codifferential
(Section 10); coefficientwise Stokes, the radial Poincaré lemma and
polynomial-simplex integration (Section 11); the Hahn cohomology theorem
(Theorem 12.1); the Hodge decomposition for a real metric (Corollary 12.3);
standard-part reduction (Theorem 13.1); the infinite-frequency obstruction
(Theorem 19.1); the scalar-derivation and scale-connection calculus
(Section 18).

**Kept twice, because hypotheses or proofs differ.** Nonlinear lifting
(Theorem 16.1, source 01, recursion) and quadratic lifting (Theorem 16.2,
source 03, tree expansion, with extra valuation estimates). The Poynting balance
with material constants (Proposition 28.1, source 03) and the covariant stress
balance in vacuum units (Proposition 35.1, source 02). The scalar action of
Section 17 (source 01) and the first-order Lagrangian calculus of Section 37
(source 02).

**Attached to general statements after re-reading the proofs.** Four results
from the three-dimensional source are printed in every dimension: the
regular-metric Hodge theorem (Theorem 12.4), the cohomology theorem
(Theorem 12.1), the linear scale-chart formulas (Section 6.1) and the jet
distribution (Section 19.3). Their statements and proofs use no property of
dimension three. The Hodge theorem keeps its hypothesis that the leading metric
is positive definite. The infinite-frequency theorem is stated on an interval,
as in source 02; the remark after it notes that the proof works on any real
open domain. Nothing Lorentzian was attached to a general statement. The
Lorentzian sign formulas (`δ = *d*`, `*² = (−1)^{p(4−p)+3}`) and the
three-dimensional ones (`δ_g = (−1)^k *d*`) were checked against the general
formulas of Section 10 (Remark 10.1).

**Renamed to avoid collisions** (in the added material; Section 1.5 and
Appendix A state the conventions):
- source 02's monomial `ε^γ` is `t^γ`; `ε` always means a chosen infinitesimal `t^η`;
- the Minkowski metric `η_{μν}` and its form `q_η` appear in Part III only;
- `SO⁺(1,3;K)` is `𝒢`; source 02's tensor valuation `ν` is `v_V`;
- source 02's `ord_Γ` and source 03's field valuation `v(F)` are `v_H`;
- source 02's exponent sets `Δ` are `S_Q` and `S_r`; its exponent `δ` is `θ`;
  its angular current `M` is `𝓜`, and its fluid expansion `θ` is `ϑ`;
- the Berarducci–Mantova derivation is `∂_BM`; the character derivations are `𝒟_χ`;
- source 03's alternating symbol `ε_{ijk}` is `ϵ_{ijk}`;
- source 03's permittivity and permeability are `κ_E, κ_B`, its Lamé constants
  `λ_L, μ_L`, and its metric density `J` is `μ_g`;
- "regular Hahn metric" (source 03) is "regular Riemannian metric". Source 01's
  "regular metric" allows any signature.

Source 01's action `½|dφ|² + V` and source 02's Lagrangian `½∂φ·∂φ − V` use
opposite signs for the potential. Remark 17.1 records the translation.

## What the report claims

Numbers refer to the built `article.pdf`.

**Part I, every finite dimension.**
1. *Prolongation (Theorem 5.2).* A smooth Hahn field `Σ f_γ t^γ` on a real open
   set has a canonical Taylor–Hahn realization on the finite halo in `K^n`. It is
   strongly summable and an injective algebra homomorphism. Its values are
   intrinsically `C^∞`. Coefficient derivatives become intrinsic derivatives,
   and prolongation commutes with composition. Analyticity is not required.
   Proposition 5.5 lifts coordinate diffeomorphisms with positive-support
   corrections.
2. *Hahn vector spaces (Theorems 4.2, 4.3).* Real multilinear operations extend
   by convolution. A positive-order perturbation `L_0 + P` of a real isomorphism
   is invertible by a strong Neumann series, with support in `T + ⟨S⟩` and no
   operator-norm smallness condition.
3. *Geometry (Sections 7–10).* Admissible metrics have unique Levi–Civita
   connections (Theorem 8.1). Proposition 9.1 gives the Bianchi identities, and
   there is a first-order metric response with an exact remainder. The Hodge
   star satisfies `*² = (−1)^{k(n−k)+q}` in every signature.
4. *Integration and cohomology.* Hahn Stokes (Theorem 11.1) and positivity
   (Proposition 11.2). The radial Poincaré lemma preserves support
   (Theorem 11.3). A real cochain complex has Hahn cohomology
   `H((t^Γ))` (Theorem 12.1). Compact de Rham base change holds as a graded
   algebra (Theorem 12.2). The Hodge decomposition holds for a real metric
   (Corollary 12.3) and for a regular Riemannian Hahn metric (Theorem 12.4).
5. *Reduction (Theorem 13.1, Proposition 13.2).* Standard part commutes with the
   geometry of a metric whose standard part is nondegenerate, and gives a
   quantitative support threshold.
6. *Existence by positive-support recursion.* Near-real flows (Theorem 15.1).
   Nonlinear lifting from an invertible real linearization (Theorem 16.1) and
   exact quadratic lifting with `v_H(u) = v_H(f)` (Theorem 16.2).
7. *Scalar derivations (Section 18).* Spatial and scalar derivatives are
   different; Proposition 18.1 gives the curvature of a scale connection.
8. *Boundaries (Section 19).* There is no coherent solution of `u' = i t^{−θ}u`
   or of `P_0u + cu = 0` with `v(c) < 0` (Theorem 19.1). A formal solution for
   every real time need not exist at a surreal time (Section 19.2). Products of
   distributions stay undefined (Section 19.3).

**Part II, three dimensions.** Finite vector identities over any real-closed
field (Theorem 22.1). The leading valuation of a cross product detects
infinitesimal independence (Proposition 22.3). Vector differential identities
hold at arbitrary rank (Theorem 23.1). Other results: metric curl and the
curved `curl curl` identity; conformal infinitesimal curvature; the anisotropic
metric `diag(1,t²,t⁴)`, for which raising an index does not commute with
standard part; radial potentials (Proposition 25.1); a monopole with flux `4πq`
at every radius and no global vector potential; an explicit Helmholtz
decomposition on `T³`; a unique positive-support stationary incompressible flow
for infinitesimal forcing on `T³` (Corollary 26.1); modified identities for a
scale connection (Corollary 27.1); and continuum applications (Maxwell with
material constants and Proposition 28.1, Cauchy stress, isotropic elasticity,
a Beltrami field, a worked three-scale field).

**Part III, Minkowski space.** Reverse Cauchy–Schwarz and explicit rest boosts
over `K` (Proposition 30.1). Boosts `B(λ)` of arbitrary scale are defined
without a rapidity. The bounded Lorentz group splits over `SO⁺(1,3;R)`, with
kernel `exp` of the infinitesimal Lorentz algebra (Theorem 32.1). Component
valuations are invariant under bounded frames (Proposition 32.2), and an
infinite boost breaks this (Example 32.3). A near-null vector keeps its causal
type beyond its null depth (Theorem 32.4). Other results: the Lorentzian Hodge
operator and self-dual fields; Maxwell equations in tensor, three-vector and
form language; the stress balance (Proposition 35.1); pointwise dominant energy
(Theorem 35.2); the Rainich identity and null stress. The energy has exactly
twice the leading field valuation, including null radiation (Theorem 35.3).
Further results: support-preserving Cauchy lifting (Theorem 36.1); the
retarded inverse of a positive-order perturbation (Theorem 36.3); scalar,
fluid and charge identities (Section 37); and a unique positive-order
deformation of a real cubic-wave solution (Theorem 38.1), with the worked
oscillator `y'' + y³ = 0`.

## What the report does not claim

Every limitation stated by any source is kept in the text. Appendix C.5 lists
them source by source: 18 for source 01, 16 for source 02 and 17 for source 03.
In brief:
- **No physics claim.** Part III is mathematics of fields on Minkowski space. It
  is not an assessment in the sense of `physics/surreal-scalars-and-spacetime`
  and respects that report's firewall. No experimentally validated theory, no
  attainable infinite-boost observer, no measurable infinite energy, no
  statement about black-hole interiors or quantum gravity, and no resolution of
  gravitational or hydrodynamic singularities is claimed.
- **No unrestricted analysis on `No^n`.** A bare map into `No^n` is not a smooth
  field, and pointwise invertibility is not an admissible inverse. Neither the
  intrinsic topology nor coefficientwise integration is a theory on all surreal
  subsets. Prolongation is a chosen extension, not a canonical or analytic one.
- **No unrestricted Hodge or existence theorems.** Hodge theory is proved only
  for a real metric and for a regular Riemannian metric. The lifting theorems
  need a specified invertible real linearization or a real Cauchy theory on a
  fixed domain. They give no convergence at a positive real scale, no global
  Einstein, Yang–Mills or Navier–Stokes evolution, and no fine-topology
  well-posedness.
- **No priority claim.** Several results restate material already in the
  collection for real coefficients, among them coefficientwise Stokes, the
  radial Poincaré lemma, Hahn cohomology, polynomial Stokes and the
  finite-partition obstruction (`surcomplex/contours-and-stokes`). No
  exhaustive novelty search was made.
- **No machine verification beyond the finite checks.** No Lean source, no Lean
  build, and no refereeing. The finite programs check identities, not the
  infinite-support theorems.

**Corrected or updated source statements** (Appendix C.4). Source 01's "current
documentation" is now pinned. Source 01's Hahn Stokes, Poincaré, cohomology and
polynomial-Stokes developments are now related to `contours-and-stokes`, which
had their complex-coefficient versions at the pin. Source 01's "a different
metric requires a separate argument" now points to Theorem 12.4. Two of source
02's future directions are re-scoped as partly answered inside the report.
Source 02's audit found no "Minkowski tensor" material at the pin; the
collection now has this report. Source 03's remark on large rotation angles now
points to `surreal/euclidean-three-space`. All program and record paths use the
prefixed names.

**Open directions** (Section 41.1, with status):
1. Larger function classes with oscillatory phases and boundary-layer charts.
   Open.
2. Hodge theory for genuinely surreal leading metrics. Partly answered: the
   regular Riemannian case is Theorem 12.4. Open: indefinite regular metrics
   and metrics with degenerate standard part.
3. Scale charts around rank-changing limits. Open.
4. Gauge-fixed nonlinear systems and a variable Lorentzian metric. Partly
   answered: the regular metric geometry of Sections 8–13, Corollary 26.1 and
   Theorem 38.1. Open: gauge, causal propagation and Einstein evolution.
5. A locally coherent sheaf theory. Partly answered: the sheaf of Section 4.
   Open: global criteria for evolution.
6. Computation and formalization. Open.

## Relation to the neighbouring reports

- `surcomplex/contours-and-stokes` has the complex-coefficient Hahn de Rham
  complex, with `contours:thm:hahnstokes`, `contours:prop:poincare`,
  `contours:thm:cohomology`, `contours:thm:polstokes`,
  `contours:thm:deformedstokes` and `contours:prop:mesh`. Theorems 11.1, 11.3
  and 12.1 and Proposition 5.1 are their real-coefficient restatements.
- `physics/surreal-scalars-and-spacetime`: its `phys:prop:frame` is the
  bounded-frame invariance of Section 3 and Proposition 32.2. Its
  `phys:thm:reduction` is the Lorentzian four-dimensional case of Theorem 13.1.
  This report makes no claim in that report's physics tiers.
- `surcomplex/analysis` has the coherent one-variable calculus whose method
  Section 5 extends. `foundations-and-computation/foundations` has the
  discreteness theorem `found:thm:discrete` used in Section 5.1.
- `surquaternions/surquaternions`: the cross product is the vector part of the
  pure-quaternion product, and that report has the spin description of
  `SO(3,F)`. Its `squat:thm:nooscillation` concerns the scalar derivation; it is
  not Theorem 19.1.
- `surreal/euclidean-three-space` (same batch) treats rotations, quaternions and
  finite-angle trigonometry in `No³`. `surcomplex/trigonometry` treats the unit
  circle, which Part III uses only through its rational parametrization.
- `surcomplex/spectral-theory` and `surcomplex/infinite-dimensional-hahn-spectral-theory`
  cover the spectral theory that Part II uses only pointwise.
  `surreal/hahn-valued-measures-and-probability` has general Hahn-valued
  measures; Proposition 11.2 concerns only smooth densities.
  `surcomplex/differential-equations` has the phase obstruction for the scalar
  derivation.
- The repository's Lean Hahn layer (`Neumann.lean`, `NeumannWords.lean`,
  `MvEvaluation.lean`, `MvComposition.lean`) proves the scalar-level support
  inputs. No field-level theorem here has a Lean counterpart.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python code/01-vector-tensor-fields-n-verify.py
python code/02-minkowski-check_identities.py
python code/03-three-dimensional-fields-verify_examples.py
```

The build gives 89 pages. It has zero errors and zero LaTeX or package
warnings. There are no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations, and no overfull or underfull boxes. The
programs need Python 3.10 or later and SymPy (`data/02-minkowski-requirements.txt`
pins 1.14.0). They use exact symbolic and rational arithmetic, and each prints
its results.

Run the programs on a copy of this directory.
`02-minkowski-check_identities.py` writes `verification_results.json` next to
itself, that is, into `code/`. The recorded results are:
- source 01: 7 check groups, 5,533 exact assertions, in
  `data/01-vector-tensor-fields-n-verification.txt`;
- source 02: 42 named checks, in `data/02-minkowski-verification_log.txt` and
  `…_results.json`;
- source 03: 11 check groups, in
  `data/03-three-dimensional-fields-verification_results.txt`.

For this merge all three were rerun on a copy with Python 3.14.4 and SymPy
1.14.0, and every check passed. The outputs match the records except for line
endings and the Python version that programs 01 and 03 print (the records used
3.13.5).

The two Makefiles are shipped as delivered. They refer to the delivered layouts
(`code/verify.py`, `verification/check_identities.py`,
`article/surreal_minkowski.tex`), so they do not work from this directory. Use
the commands above instead. `02-minkowski-SOURCE_AUDIT.md` also names the
delivered paths.
