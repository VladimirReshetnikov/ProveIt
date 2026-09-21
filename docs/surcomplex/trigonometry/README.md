# Trigonometry on the Surcomplex Plane

**Canonical Phases, Arbitrary-Scale Geometry, and Infinitesimal Degeneration**
September 21, 2026 — `article.tex` / `article.pdf`, 58 pages, 81 numbered results.

## What this report is

One merged research article on the trigonometry of the surcomplex class field
`SC = No[i]`. Its organizing theorem is that every surcomplex direction has a
**finite** surreal angle: `cis : (O_R, +) → (T(No), ·)` is surjective with kernel
exactly `2πZ`, so `O_R/2πZ ≅ T(No) ≅ T(R) × (m_R, +)`, and the whole of plane,
spherical and hyperbolic triangle geometry is therefore available at arbitrary
surreal length scale without ever choosing a value for `sin ω`.

From that theorem the article develops, in order: the Hahn-summation construction
of canonical sine and cosine on finite angles and its normalization; the unit
circle, its branch conventions and its projective half-angle chart; inverse
functions on their full surreal domains and the angular metric; the angle-sum,
cosine, sine, tangent, half-angle, Heron, incircle, Euler, angle-bisector,
cevian, Ceva, inscribed-angle and Ptolemy theorems; the exact valuation
dictionary between sides, angles and area, with a quadratic triangle-inequality
defect formula and two flat-triangle theorems; line–circle intersection,
tangency, the cosine fold, a rank-two collision-stable intersection algebra, a
coupled four-point angular collision, and three separate root-stability
certificates; the canonical complex extension to the strip of arguments with
finite real part and arbitrary surreal imaginary part, where sine is surjective
with completely determined fibres; the algebraization of trigonometric
polynomials and support-controlled cluster lifting; finite Fourier inversion,
Parseval and a surcomplex Fejér–Riesz factorization; spherical and hyperbolic
trigonometry; coherent arc length and sector area; and the classification of all
global phase extensions, with the canonical Ehrlich–Kaplan normalization placed
inside that classification and two coherence obstructions.

## Which archives it came from

Three independently written manuscripts of 21 September 2026, all kept in
`sources/`:

| file | title |
|---|---|
| `16-finite-radians-angular-phenomena.tex` | *Trigonometry on the Surcomplex Plane: Finite Radians, Arbitrary-Scale Geometry, and Infinitesimal Angular Phenomena* |
| `17-canonical-phases-degeneration.tex` | *Surcomplex Trigonometry: Canonical Phases, Arbitrary-Scale Triangles, and Infinitesimal Degeneration* |
| `18-canonical-angles-oscillation.tex` | *Trigonometry on the Surcomplex Plane: Canonical Angles, Infinite Triangles, Infinitesimal Contact, and Hahn-Analytic Oscillation* |

All three are drafts of one article — two even share a title — and all three
prove the finite-angle/canonical-phase theorem, the polar decomposition, the
half-angle parametrization, the inverse functions, the angle sum and the full
triangle laws, triangle existence, Heron and the half-angle formulas, Ptolemy,
trigonometric Ceva, the valuation forms of the triangle laws, a quadratic defect
formula for degeneration, Fejér–Riesz, finite Fourier inversion and Parseval,
and the classification of global phase extensions with unavoidable infinite
periods. **Each of those appears once in the merged article.** No mathematical
disagreement was found between the three.

### What each contributed

**18 — the base.** The largest and most completely fibred of the three; its
versions of the shared core are the ones printed. Uniquely its own: Euler's
incentre–circumcentre identity and the cevian/angle-bisector theorem; the SSS
existence theorem with the explicit Heron factorization; circle length and
sector area at every radius, with the negative result that inscribed polygon
perimeters do not fine-converge and have no least upper bound; exact cluster
multiplicity with a coefficient-support bound, proved by a finite Sylvester map
and transfinite recursion over `S*`; the algebraization of trigonometric
polynomials with the sharp `2n` root bound; the complete fibres of strip sine
with the exact coincidence condition `w = ±1`; the two-square lemma over a real
closed field; hyperbolic geometry in the full surreal Poincaré disk with the
`No`-valued disk metric; and the no-go theorem that no bounded common-domain
Hahn-analytic function represents an infinite-frequency sine.

**17.** Spherical trigonometry, which appears nowhere else in the set; the chord
and inscribed-angle theorems with their exact factorization; line–circle
intersection with explicit intersection points and Jacobian; the rank-two
intersection algebra `A_d = SC[W]/(W² − d)` with its collision-stable residue
pairing, two-simple-residue formula and dual-number degeneration; the sharp
conditioned inversion of cosine with second-order term and remainder bound
`v(R) ≥ 3σ − 5κ`; the exact triangle-inequality defect formula with no
comparability assumption; the relative flatness threshold `δ ≺ bc/B` together
with the `Δ` and `R` equivalents; the internal-bisector length; the angle→triangle
reconstruction at arbitrary scale; the canonical global normalization
`Sin x = sin(fin x)` attributed to Ehrlich–Kaplan, with `ker Exp = 2πi·Oz` and the
period class `2πOz`; and the fine-topology degeneracy proposition.

**16.** The cosine fold including its purely imaginary roots at negative
parameter; the sharp `σ > 2κ` angular root-stability bound with **both**
valuation estimates and a separate sharpness proposition showing the threshold
cannot be weakened and that both exponents are attained; the standalone
simple-residue-root (Hensel-type) lemma using the polynomial intermediate-value
property with an infinitesimal test radius; the coupled four-point angular
collision algebra `B_{s,u}`; the normalization proposition for the finite
trigonometric pair; the projective `P¹(No)` tangent parametrization with its
homogeneous group law; the `Δ ≤ s²/(3√3)` area inequality; the quadrance/spread
and triple-spread identities; the Dirichlet and Fejér kernel identities with the
warning that they are not an approximation theorem; the uniqueness normalization
for the Fejér–Riesz factor (`Q` with no zero in `|u| < 1` and `Q(0) > 0`); and the
explicit negative-window analysis of the degree-two polynomial that is positive
at every ordinary angle.

Both 17 and 18 carry hyperbolic laws. Only 18's Poincaré-disk version is stated;
17's Lorentz-hyperboloid proof is recorded as a remark and not restated.

## Conflicts and how they were resolved

- **Coefficient rings.** Four rings circulate in this set under nearly identical
  notation. Section 1.3 fixes them as (R1) fixed-domain, (R2) common-domain germ,
  (R3) radius-free, (R4) formal, and every coherence statement names its ring.
  Only (R1)–(R2) carry theorems here; (R3) and (R4) carry none.
- **Canonical vs. free global phase.** 17 asserts a canonical global
  normalization; 16 and 18 decline to derive canonicity from the local axioms and
  prove infinite periods are unavoidable. Both are printed: the canonical choice
  is an extra structural input (the initial integer part), and its period class
  `2πOz` is exactly the unavoidable-infinite-period phenomenon.
- **Three stability certificates.** Section 9.6 states explicitly which of the
  three is sharper for which purpose before proving them.
- **Branch conventions.** The actual-interval cut and the standard-part-pinned
  unwrapped branch are stated once, side by side, and declared not to be the same
  function; angle classes are used thereafter.
- **Stronger versions kept.** Ptolemy is stated as the general inequality with
  the cyclic equality case (not equality alone); the root bound is the bijective
  with-multiplicity version; strip sine is stated with complete fibres; the
  Fejér–Riesz factor carries the uniqueness normalization.

## Notation

One symbol per concept, fixed in §1.2: `T(No)` for the unit circle, `cis` for the
finite phase (`E` reserved for the strip exponential), `O_R`/`m_R` for finite
elements and infinitesimals, `d(α)` for the angle defect, `∠(u,v)` for the angular
metric, `α,β,γ` for interior angles, and `h, ε, τ, δ` for the four small
parameters the sources overload. The map to `C` is the **standard part** and the
topology it induces the **standard-part topology**; the sources' synonyms
(reduction, shadow, residue) are noted once and not reused. The genuinely
different **fine** topology keeps its own name. All labels are prefixed
`trigonometry:`.

## What is not proved

Collected in §18.4 of the article, one entry per source non-claim. In outline:
no general transfer of infinite families of inequalities, and no uniqueness from
a differential equation rather than the Taylor rule; no inference of global
monotonicity from the sign of a fine derivative; asymptotic equivalences concern
a single infinitesimal and are not sequence limits; the endpoint derivative of
inverse sine does not exist as a surreal-valued derivative, and no derivation on
`No` is being chosen; the side–side–angle ambiguity remains; quadrances and
spreads forget orientation; no directed Menelaus/Ceva; cyclic order is not
defined by fine-continuous motion; angular error must not be inferred from cosine
error alone; equal least side valuation is attained twice but not thrice; the
flatness denominator `bc/(b+c)` is essential; the branch-matching conditions
`e ≺ τ` and `σ > 2κ` cannot be relaxed; the dimension four of `B_{s,u}` is a total
multiplicity, not a per-root claim; the cluster support bound belongs to factor
coefficients, not to individual roots, with no reality conclusion for a multiple
zero, and is a coefficient recursion rather than Newton convergence; the
derivative root count invokes no extreme-value theorem; the finite Fourier
identities establish no infinite-series convergence or completeness, and the
Dirichlet/Fejér kernels are not an approximation theorem; Fejér–Riesz is a
real-closed-field extension of a classical result, with no multivariable
single-square claim; the positivity counterexample does not contradict sign
lifting; the coefficientwise arc-length functional is not a Riemann integral and
asserts no fine-continuous path; the spherical and hyperbolic sections give
metric identities, not a global geometric or measure-theoretic foundation; the
global normalization is the established Ehrlich–Kaplan construction and is not
claimed as new; the extension classification is not a classification of solutions
of a differential equation and does not settle the Ehrlich–Kaplan robustness
questions; the two coherence obstructions are restrictions on uniform analytic
descriptions over ring (R1) only; and no proper-class sum, infinite polygon,
full-class Riemann integral, priority claim, or resolution of a named published
conjecture is asserted anywhere. The literature search was targeted rather than
exhaustive, nothing is formally verified, and the accompanying symbolic checks
(67, 43 and 68 in the three source editions) validate displayed examples rather
than machine-checking the general proofs.

## Build

```
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

Requires a LaTeX distribution with the AMS packages, Latin Modern, geometry,
microtype, hyperref, cleveref, fancyhdr, booktabs, longtable, array, enumitem and
xcolor. The bibliography is embedded in a `thebibliography` environment; no BibTeX
or Biber run is needed. The current build produces 58 pages with 0 errors, 0
undefined references, 0 undefined citations, 0 duplicate PDF destinations and 0
overfull or underfull boxes.
