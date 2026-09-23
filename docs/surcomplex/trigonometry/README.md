# Trigonometry on the Surcomplex Plane

**Canonical Phases, Arbitrary-Scale Geometry, and Infinitesimal Degeneration**
Merged research report of 21 September 2026, extended 22 September 2026, built
from six manuscripts written independently on those two days. AI-assisted
drafts; not refereed; not formally verified.

```
article.tex      the report, standalone LaTeX with an internal bibliography
article.pdf      the compiled report, 96 pages
README.md        this guide
21-period-arithmetic-source_audit.md                          (source 21, its delivered audit)
code/            16-finite-radians-angular-phenomena.py      (source 16)
                 17-canonical-phases-degeneration.py         (source 17)
                 18-canonical-angles-oscillation.py          (source 18)
                 19-rotation-group-verify.py                 (source 19)
                 19-rotation-group-build.sh, .ps1            (source 19, see "Build")
                 20-exponential-kernels-verify.py            (source 20)
                 20-exponential-kernels-build.sh             (source 20, see "Build")
                 21-period-arithmetic-verify_examples.py     (source 21)
                 21-period-arithmetic-Makefile               (source 21, see "Build")
data/            16-finite-radians-angular-phenomena-requirements.txt,
                 -source_provenance.txt, -verification_report.txt   (source 16)
                 17-canonical-phases-degeneration-requirements.txt,
                 -verification_report.txt                     (source 17)
                 18-canonical-angles-oscillation-requirements.txt,
                 -verification_report.txt                     (source 18)
                 19-rotation-group-requirements.txt,
                 19-rotation-group-verification_results.json  (source 19)
                 20-exponential-kernels-verification_results.json (source 20)
                 21-period-arithmetic-verification.json       (source 21)
```

Every label in `article.tex` carries the prefix `trigonometry:`. The material
of source 19 carries the sub-prefix `trigonometry:rot:`, that of sources 20 and
21 the sub-prefix `trigonometry:per:`. **No pre-existing label was renamed or
removed**: the report had 221 labels before source 19 was merged, 279 after it,
and has 349 after sources 20 and 21; all 279 are still present. Every existing
theorem, equation and section number is unchanged except the concluding
section, which moved from 18 to 19 with source 19 and from 19 to 20 with sources
20 and 21 (its non-claims subsection is now 20.4). The
[formalization ledger](../../FORMALIZATION.md) maps some `trigonometry:` labels
(for example `trigonometry:prop:lift`, `trigonometry:thm:cayley`,
`trigonometry:thm:fourier`) to Lean declarations; no `trigonometry:rot:` or
`trigonometry:per:` label has a mapping. The ledger's line-number index of this
report predates both merges and needs regenerating.

## Six sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **16** | *Trigonometry on the Surcomplex Plane: Finite Radians, Arbitrary-Scale Geometry, and Infinitesimal Angular Phenomena* (21 Sep) | none recorded | see below; files prefixed `16-finite-radians-angular-phenomena-` |
| **17** | *Surcomplex Trigonometry: Canonical Phases, Arbitrary-Scale Triangles, and Infinitesimal Degeneration* (21 Sep) | none recorded | see below; files prefixed `17-canonical-phases-degeneration-` |
| **18** | *Trigonometry on the Surcomplex Plane: Canonical Angles, Infinite Triangles, Infinitesimal Contact, and Hahn-Analytic Oscillation* (21 Sep) | none recorded | the base text of Sections 1–17; files prefixed `18-canonical-angles-oscillation-` |
| **19** | *Rotations of the Surreal Plane: The Norm-One Torus, Infinitesimal Angles, and Topology at Every Scale* (22 Sep) | `dcf86662b574` | Section 18; files prefixed `19-rotation-group-` |
| **20** | *Exponential Kernels and Arithmetic Rigidity in the Surcomplex Field: Minimal Multiplier Rings, Nonsplit Periods, and the Limits of Canonical Extension* (22 Sep; 28 pp.) | `465a54b479a1` | Section 19, with 21 (below); files prefixed `20-exponential-kernels-` |
| **21** | *Period Arithmetic and Noncanonical Surcomplex Exponentials: Profinite Defects, Minimal Multiplier Rings, and a Partial Answer to an Ehrlich–Kaplan Question* (22 Sep; 25 pp.) | `465a54b479a1` | the base text of Section 19; files prefixed `21-period-arithmetic-` |

The source manuscripts themselves are not shipped; their code and data are,
under the prefixes above. Sources 16–18 were written from three user-supplied
manuscripts (surcomplex analysis, finite zero geometry, finite intersections;
`data/16-finite-radians-angular-phenomena-source_provenance.txt` records their
titles and checksums) and record no repository commit. Source 19 was written
against commit `dcf86662b574`, at which `article.tex` stood exactly as before
this merge; it inspected the root and documentation READMEs, this directory's
README and the opening of the article. Sources 20 and 21 were written against
commit `465a54b479a1ee842cbf7db1689a7d2f6bfe25e1`, at which this directory stood
exactly as before their merge; source 20 audited the root and documentation
READMEs, this README and the article's Section 17, source 21 the repository
tree, the same READMEs, this article and the automorphism report's README
(its audit is shipped as `21-period-arithmetic-source_audit.md`).

**Sources 16–18.** All three are drafts of one article — two share a title —
and all three prove the finite-angle/canonical-phase theorem, the polar
decomposition, the half-angle parametrization, the inverse functions, the angle
sum and the full triangle laws, triangle existence, Heron and the half-angle
formulas, Ptolemy, trigonometric Ceva, the valuation forms of the triangle laws,
a quadratic defect formula for degeneration, Fejér–Riesz, finite Fourier
inversion and Parseval, and the classification of global phase extensions with
unavoidable infinite periods. Each of those appears once. No mathematical
disagreement was found between the three.

- **18, the base.** The largest and most completely fibred; its versions of the
  shared core are the ones printed. Uniquely its own: Euler's
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
- **17.** Spherical trigonometry; the chord and inscribed-angle theorems with
  their exact factorization; line–circle intersection with explicit points and
  Jacobian; the rank-two intersection algebra `A_d = SC[W]/(W² − d)` with its
  collision-stable residue pairing, two-simple-residue formula and dual-number
  degeneration; the sharp conditioned inversion of cosine with second-order term
  and remainder bound `v(R) ≥ 3σ − 5κ`; the exact triangle-inequality defect
  formula with no comparability assumption; the relative flatness threshold
  `δ ≺ bc/B` with the `Δ` and `R` equivalents; the internal-bisector length; the
  angle→triangle reconstruction at arbitrary scale; the canonical global
  normalization `Sin x = sin(fin x)` attributed to Ehrlich–Kaplan, with
  `ker Exp = 2πi·Oz` and period class `2πOz`; and the fine-topology degeneracy
  proposition.
- **16.** The cosine fold including its purely imaginary roots at negative
  parameter; the sharp `σ > 2κ` angular root-stability bound with both valuation
  estimates and a separate sharpness proposition; the simple-residue-root
  (Hensel-type) lemma; the coupled four-point angular collision algebra
  `B_{s,u}`; the normalization proposition for the finite trigonometric pair; the
  projective `P¹(No)` tangent parametrization with its homogeneous group law; the
  `Δ ≤ s²/(3√3)` area inequality; the quadrance/spread and triple-spread
  identities; the Dirichlet and Fejér kernel identities with the warning that
  they are not an approximation theorem; the uniqueness normalization of the
  Fejér–Riesz factor; and the negative-window analysis of the degree-two
  polynomial that is positive at every ordinary angle.

Both 17 and 18 carry hyperbolic laws. Only 18's Poincaré-disk version is
stated; 17's Lorentz-hyperboloid proof is recorded as Remark 15.4.

**Source 19.** Organizes the finite-angle theory around the rotation group
`SO(2,No)`. Its structure theorem `SO(2,No) ≅ T(No) ≅ O_R/2πZ ≅ T(R) × (m_R,+)`
is Proposition 4.1 with Theorem 4.2, already here; everything it adds is Section
18 (below).

**Printed once (source 19 with sources 16–18).** The table in Section 18.1
lists each shared result and where it is printed: the matrix identification (Proposition
4.1); the structure theorem, logarithmic linearization and finite-angle
uniformization (Theorem 4.2, proved in both by the same conjugation argument);
infinitesimal exp/log and formal evaluation (equations (4.1)–(4.2), Lemmas 2.2
and 2.6); principal angles and branch conventions (Corollary 4.3, Remark 4.4);
the rational chart and homogeneous law (Theorem 4.5); angular distance and
chord (Theorem 5.4); roots and absence of infinitesimal torsion (Corollary
4.3); valuations of `sin`, `1 − cos` (Proposition 3.3); displacement at any
radius (Corollary 5.5); small-set discreteness and nets (Proposition 2.4); the
canonical global phase with kernel `2πOz` (Definition 17.1, Theorem 17.2,
Corollary 17.3); all phase extensions, explicit ones with any value at `ω`, and
unavoidable infinite periods (Theorem 17.4, Example 17.5, Theorem 17.6); the
local law of phases and the normalization of the finite pair (Theorem 3.1,
equation (17.6), Proposition 3.4). Each place carries a one-line credit.

**Kept twice, as different proofs.** The count of `n`-th roots: Corollary 4.3
(degree bound for `Xⁿ − u` and the kernel of `cis`) and Remark 18.4 (source
19's route through uniqueness of the split factors alone).

**Renamed to avoid collisions** (in source 19's material only). Its `O, m` →
`O_R, m_R`; its infinitesimal `Exp, Log` → `Exp_m, Log_m` (`Exp` here is the
global Ehrlich–Kaplan exponential); `H_0, H_χ, 𝒥` → `Φ, Ψ_χ, Π`; `d_ang` → `∠`;
its coefficient `a_ω(p)` → the `ℓ(p)` of Example 17.5; its infinitesimal angle
`ℓ(u)` → `ℓ_m(u)`; its monad `U` → `T_m` (`U` is used for Chebyshev
polynomials and for `E(iz)`); its matrix `R(a,b)` → `Rot(a,b)` (`R` is a
circumradius); its generator `J` → sans-serif `J` (`J` is an interval in ring
(R1)); its conjugation `κ` → `c` (`κ = v(f'(a))` in Theorem 9.7); its `δ, p_2,
E, α, F_λ, S_r` → `d, sq, e₁₂, ϖ, Ξ_a, 𝒮_ρ`. Its homogeneous chart `[s:t] ↦
C(t/s)` with law `[sp−tq : sq+tp]` is converted to this article's `[p:q] ↦
C(p/q)` with law (4.9); the two laws agree. Its bibliography key for
Berarducci–Mantova's *Transseries as germs of surreal functions* is `BMgerms`
here, since `BM` already denotes their *Surreal numbers, derivations and
transseries*. All conversions are stated once, in Section 18.1.

**Sources 20 and 21.** Two independent manuscripts on one spine: from the
character classification (Theorem 17.4) and unavoidable infinite periods
(Theorem 17.6), both cited and not reproved, they study the arithmetic of the
periods of the global phases and show that a surcomplex exponential with the
canonical strip values can have kernel-multiplier ring exactly `Z`. Source 21
is the base text of Section 19, because it proves more under weaker hypotheses:
its set-sized theorem is in ZFC on a fixed continuum-sized field (`No(ε₀)`,
`R((t^Q))`), it fixes an arbitrary ordinary character and profinite defect, and
it keeps the standard part of the phase at every argument. Source 20's own
set-sized examples live on unspecified large fragments `No(λ)` obtained by
reflecting a global-choice construction on `No`. Section 19.1 has the full
table; in short:

- *Printed once, both credited:* the character coordinates (19.2), phases and
  exponentials (19.5), the kernel dictionary (19.3), the local law (19.6), the
  splitting criterion (19.10: source 21's conditions (1)–(3), source 20's (2),
  (4), (5)), the multiplier ring and integer-part criterion (19.19, 19.20), the
  initial ring `Z` that is not an integer part (19.33), the shift automorphisms
  (19.43) and the failure of equivariance (19.44).
- *Kept as different theorems:* source 21's avoidance construction fixes the
  ordinary character and perturbs the infinitesimal one (19.26, 19.28); source
  20's relative construction prescribes the ordinary character on a set-sized
  subspace and keeps every value in the ordinary circle (19.31, 19.32), which its
  reflection theorem needs. Source 20's direct proof of non-equivariance under
  one shift is Remark 19.46. Both profinite examples are kept (Example 19.16).
- *Source 21 only:* the profinite defect (19.9) and its realization (19.14), the
  counts on `R((t^Q))` (19.15), cofinal divisible periods on `No` (19.17), the
  free action and the shadow formula (19.44, 19.47).
- *Source 20 only:* `Hom(I, Z)` (19.11), the non-initial multiplier ring
  (Example 19.22), reflection (19.36), the sentence `RingKer` (19.38), three
  structures (19.39), definable `Z` and an omitted type (19.41).
- *Stated by neither, obtained by combining them (Corollary 19.40):* source 20's
  sentence separates source 21's `No(ε₀)` example from the canonical
  exponential, and source 21's defects give three pairwise nonisomorphic
  exponentials on `No(ε₀)[i]` in ZFC.

**Credits the sources owe.** The shifts `Sh_c` (source 21's `T_c`, source 20's
`σ_a`) are the fixed-shift flows `saut:thm:shiftflow` (Theorem 5.2) of
[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/), with
`δ = 1`, `λ = [·]₀` and the flow parameter's sign reversed; source 21 credits
them and Kaplan–Krapp–Serra §4, source 20 does not. The residue map, the maximal
divisible subgroup, and the splitting and `Hom(·, Z)` facts are classical
`Z`-group theory (Jeřábek); source 21 says so, source 20 does not cite it.

**Conventions and renamings** (Section 19.1). Angles stay in radians; both
sources use turns, so periods are divided by `2π` once: the normalized period
group `I(Ψ) = {a : Ψ(2πa) = 1}` (source 20's `D`, source 21's `I_Φ`). Their
purely infinite part `P` is `Π`; source 21's arbitrary phase `Φ` and canonical
`Φ₀` are `Ψ` and `Φ` (`Φ` keeps its meaning here); source 21's character pair
`(h, L)` is `(ψ, 𝓛)` (`h` and `L` are taken); source 20's `T = R/Z` is written
`R/Z` (`T(F)` is the circle) and its `M(E)` is `Z_E`; source 21's maximal
divisible subgroup `D_Φ` is `I^div` and its defect `δ_Φ` is `pd_Ψ`, the
*profinite defect* (`δ` is a side gap and "defect" already names two other
things); its `K_Γ = R((t^Γ))` is `F_Γ`, since `K_Γ` is `C((t^Γ))` here and in the
collection's notation guide; the shifts are `Sh_c` (`T_n` is Chebyshev, `σ` a
threshold), and their exponent map is `[g]₀`, since `ℓ(p)` is Example 17.5's
coefficient of `ω`. Global choice is named at each statement that uses it;
everything about a set-sized field is ZFC.

## What the report claims

Numbers refer to the built `article.pdf`.

**Finite angles (sources 16–18).** Canonical sine and cosine on finite surreal
arguments by Taylor lifting (Theorem 3.1, Proposition 3.4); the unit circle
`T(No) = SO(2,No)` (Proposition 4.1); **Theorem 4.2**: `cis : (O_R, +) → T(No)`
is onto with kernel exactly `2πZ`, and `T(No) ≅ T(R) × (m_R, +)` canonically;
representatives, roots and torsion (Corollary 4.3); the projective half-angle
chart `P¹(No) → T(No)` (Theorem 4.5); inverse functions on full surreal domains
(Theorem 5.1); angular and chordal distance with equal valuations (Theorem 5.4).

**Geometry at every scale.** Angle sum and triangle laws (Theorems 6.1–6.2),
SSS existence (6.4), Heron and the radii (6.5), Euler (6.6); cevians, Ceva,
inscribed angles, Ptolemy (Section 7); the valuation dictionary, defect
formula and flatness thresholds (Theorems 8.1–8.4); intersections, tangency,
the cosine fold, the collision-stable residue pairing and the three stability
certificates (Section 9, certificates compared in 9.5, Theorems 9.7 and 9.9).

**Complex and analytic.** The canonical strip exponential and strip sine with
complete fibres (Theorems 10.1, 10.4); the `2n` root bound (Theorem 11.1);
cluster multiplicity (Theorem 12.1); finite Fourier inversion, Parseval and
Fejér–Riesz (Theorems 13.1, 13.2, 13.4); spherical and hyperbolic laws
(Theorems 14.1, 15.2); coherent arc length (Theorem 16.1) and the failure of
fine convergence of perimeters (Proposition 16.2); the canonical global phase
(Theorem 17.2), the classification of all extensions (Theorem 17.4),
unavoidable infinite periods (Theorem 17.6) and the two coherence obstructions
over ring (R1) (Theorems 17.7, 17.8).

**The rotation group (source 19, Section 18).**
1. **Isometry rigidity, Theorem 18.2**: a distance-preserving map of `F²`
   fixing `0`, `F` real closed, is linear and orthogonal; `O(2,F) ≅ T(F) ⋊ {1,c}`.
2. The chart's exceptional cases, `C(t)+1 = 2(1+it)/(1+t²)` (18.6), the
   point-versus-variety caveat (Remark 18.3), and `ℓ_m(C(t)) = 2 arctan t` for
   infinitesimal `t` (18.7).
3. **Torsion ≅ Q/Z and every finite subgroup is `μ_n`** (Corollary 18.5);
   divisibility, no finite quotients (Corollary 18.6); algebraic square roots
   and no multiplicative square-root section; the double-angle map and
   `Spin(2)`; finite subgroups of `O(2,No)` conjugate to standard dihedral
   groups (Proposition 18.7).
4. **Theorem 18.8**: each layer `T_m^{≥γ}/T_m^{>γ} ≅ (R,+)`; the displacement
   valuation `v(z) + v(ε)` (18.12) with Example 18.9; exact error propagation
   (18.13); Hahn products of summable families (18.14); surreal exponents of a
   rotation on a restricted domain (18.15).
5. Free transitive action on each circle; **polynomial invariants
   `F[X,Y]^{SO(2)} = F[X²+Y²]`** (Proposition 18.10).
6. The norm-one torus: split over `F[i]`, anisotropic over `F`,
   `so(2,F) = F·J`, no algebraic additive exponential (Proposition 18.11), the
   invariant differential and `C*ϖ = 2dt/(1+t²)` (18.20).
7. **Theorem 18.12**: algebraic endomorphisms `≅ Z`, automorphisms `±1`;
   irreducible algebraic representations have ordinary integer weights; the
   nonalgebraic fine-continuous automorphisms `Ξ_a` (18.23) and a
   non-semisimple fine-continuous representation (18.24).
8. Fine topology: set-indexed Cauchy nets are eventually constant; **the fine
   circle is totally separated without isolated points (Proposition 18.13)**;
   **Theorem 18.14**: `T(No)_fine ≅ T(R)_discrete × (m_R)_fine`; set-generated
   subgroups are closed, discrete and not dense (Corollary 18.15); strong sums
   are not fine limits.
9. The standard-part topology (a non-`T₀` group topology whose Kolmogorov
   quotient is the usual circle); semialgebraic path connectedness over a fixed
   real closed set field, proved; `π₁^sa ≅ Z` (18.27), **imported** from
   Delfs–Knebusch and Baro–Otero.
10. Local flows `Rot_a` on `D_a = a⁻¹O_R` (18.28); Example 18.16, a solution of
    `f' = if`, `f(0) = 1` other than `cis`.
11. Three exact representations for computation; a comparison table with the
    classical circle (Section 18.13).

**Period arithmetic (sources 20 and 21, Section 19).** For a phase `Ψ` on `F`
(`No`, `No(λ)`, `R((t^Q))`, or a truncation-closed continuum-sized field):
1. **Theorem 19.3**: `Ψ ↦ I(Ψ)` is a bijection onto the additive integer parts
   of `F`, with exact sequence `0 → Z → I → Π_F → 0`; division with remainder
   (19.4); phases correspond to exponentials with the strip and modulus laws,
   with `ker E = 2πi·I` (19.5); the common local law and fine derivatives (19.6).
2. **Profinite defect** `pd_Ψ : Π_F → Ẑ/Z`, whose kernel is the set of principal
   parts of the maximal divisible subgroup (19.9); split ⇔ zero defect ⇔ unique
   additive retraction ⇔ a `Q`-linear lift of the ordinary character (19.10);
   split ⇔ a nonzero homomorphism to `Z` (19.11). **Every linear defect is
   realized (19.14)**, using only a choice between sets; on `R((t^Q))` there are
   exactly `2^(2^ℵ₀)` reduced and `2^(2^ℵ₀)` split period groups (19.15, ZFC).
3. **Theorem 19.17**: on `No` every phase has cofinally large periods all of
   whose rational multiples are periods; no phase on `No` has a reduced period
   group (19.18).
4. **Criterion 19.20**: the multiplier ring is an integer part ⇔ the normalized
   periods form a ring ⇔ the binary kernel condition; with initiality, ⇔ the
   canonical exponential. A kernel whose multiplier ring is not initial
   (Example 19.22).
5. **Minimal multiplier rings**: for every ordinary character, an
   infinitesimal character with multiplier ring `Z`, in ZFC on `R((t^Q))` and
   `No(ε₀)` (19.26) and with global choice on `No` (19.28), together with any
   prescribed defect and a fixed standard-part phase (19.29); source 20's
   relative version extending a prescribed set-sized character (19.31) and a
   nonsplit example (19.32).
6. **Theorem 19.33**: exponentials on `No(ε₀)[i]` (ZFC) and `No[i]` (global
   choice) with the canonical strip values, modulus, conjugation and local
   Taylor law, differing from `Exp` by an infinitesimal unit-circle factor, whose
   kernel-multiplier ring is `Z`: initial, not an integer part. **This is a
   partial negative answer to one sufficiency possibility in the first
   robustness question of Ehrlich–Kaplan §11.1**; the question stays open
   (Section 19.8).
7. Reflection to arbitrarily large fragments `No(λ)`, `cf λ = ω` (19.36); the
   parameter-free sentence `RingKer`, true for `Exp` and false whenever
   `Z_E = Z` (19.38); three nonisomorphic exponentials on such fragments (19.39)
   and, by combining the sources, on `No(ε₀)[i]` in ZFC (19.40); definable `Z`
   and an omitted type (19.41).
8. The shifts `Sh_c` (19.43) act freely on all phases on `R((t^Q))` and `No`, so
   no phase is natural for the valued-field structure alone (19.44, 19.45); the
   shadow of the translated canonical phase (19.47).

## What the report does not claim

No non-claim of any source was dropped. The article states each at its point of
use and collects them in Section 20.4 (items 1–23 for sources 16–18, item 24
with sub-items (a)–(s) for source 19, item 25 with sub-items (a)–(k) for sources
20 and 21, item 26 global).

**Across the report.** The proofs have **not** been refereed and have **not**
been formalized in Lean. The symbolic checks validate finite identities and
selected Taylor coefficients, not the general proofs. The literature search was
targeted, not exhaustive; no priority claim and no resolution of a named
published problem is made. Section 19 refutes one sufficiency possibility in the
first Ehrlich–Kaplan robustness question and leaves that question, and their
second one, open.

**Sources 16–18.** No general transfer of infinite families of inequalities, and
no uniqueness from a differential equation rather than the Taylor rule; no
inference of global monotonicity from the sign of a fine derivative; asymptotic
equivalences concern a single infinitesimal and are not sequence limits; the
endpoint derivative of inverse sine does not exist as a surreal-valued
derivative, and no derivation on `No` is chosen; the side–side–angle ambiguity
remains; quadrances and spreads forget orientation; no directed Menelaus/Ceva;
cyclic order is not defined by fine-continuous motion; angular error must not be
inferred from cosine error alone; the least side valuation is attained at least
twice, which does not make all three equal; the flatness denominator
`bc/(b+c)` is essential; the branch-matching conditions `e ≺ τ` and `σ > 2κ`
cannot be relaxed; the dimension four of `B_{s,u}` is a total multiplicity; the
cluster support bound belongs to factor coefficients, not roots, with no reality
conclusion for a multiple zero and no Newton-convergence claim; the derivative
root count uses no extreme-value theorem; the finite Fourier identities give no
infinite-series convergence or completeness, and the Dirichlet/Fejér kernels are
not an approximation theorem; Fejér–Riesz is a real-closed-field extension of a
classical result, with no multivariable single-square claim; the positivity
counterexample does not contradict sign lifting; the coefficientwise
arc-length functional is not a Riemann integral and asserts no fine-continuous
path; the spherical and hyperbolic sections are metric identities, not a global
foundation; the global normalization is the established Ehrlich–Kaplan
construction, not new; the extension classification is not a classification of
solutions of a differential equation and does not settle the Ehrlich–Kaplan
robustness questions; the coherence obstructions are statements over ring (R1)
only; no proper-class sum, infinite polygon or full-class Riemann integral.

**Source 19.** An exposition organized around the group, not a priority claim
or a formalization; the finite-angle splitting is not presented as new.
"Rotation" is the algebraic isometry; bounded entries do not make the group
set-sized or compact; all statements are class-group statements with no
proper-class Hahn sum. `m_R` is not a `No`-vector space. Norm preservation alone
does not force linearity; the semidirect products are algebraic, not about
components. The rational chart is a parametrization of points, not an
isomorphism of varieties. Evaluation is asserted for real or complex
coefficients only; strong sums are not fine limits. `No/2πZ` is not the
finite-angle model compatible with the finite phase — source 19 does **not**
assert that an unrelated abstract isomorphism `No/2πZ ≅ T(No)` is impossible.
Torsion means ordinary finite order; the square-root branch is not
multiplicative; the dihedral conjugacy does not make matrices real. The graded
theorem is a filtration, not a direct sum; Hahn products give no value to
infinitely many identical turns. The invariants are polynomial only. The
algebraic group is applied at surreal points, not over `No` as a set-sized
field; the exponential series is not summable at infinite argument; the
invariant form defines no full-class contour integral. No Fourier convergence,
no Haar measure on the full class, no classification of abstract
representations or automorphisms. Surreal exponents are an analytic scaling on
a restricted domain. Small-set discreteness is special to the full class and
does not forbid class-indexed nets approaching zero; there is no ordinary real
Lie-group interpretation. The two uses of `st` must not be conflated; `π₁^sa` is
imported; the sequence `2πZ → O_R → T(No)` is not a universal-covering claim. A
local rotation equation with `Ψ(0) = 1` does not choose a global normalization,
and mean-value or initial-value uniqueness needs further hypotheses. No
finite-string representation of all surreals, no decidable equality of effective
names. No novel global sine, no resolution of an Ehrlich–Kaplan robustness
question, no global mean-value theorem. No exhaustive repository or literature
search; the other manuscripts of the collection are unrefereed drafts.

**Sources 20 and 21.** Theorem 19.33 is a partial negative answer to one
sufficiency possibility: no classification of the conditions that would
suffice, no claim that Ehrlich and Kaplan conjectured initiality to suffice, and
nothing on their second question (exponentials from different initial
embeddings); the first-order separation is in the broader class of all
exponentials with the strip and modulus laws. The finite-angle theory, the
canonical phase, Theorems 17.4 and 17.6 and the local law are prerequisites;
the canonical integer-part exponential is published; `Z`-group residues and
divisible subgroups are classical; the shifts are a prior type, re-proved, not
asserted to preserve `exp`, the omega map or simplicity, and the naturality
obstruction concerns only the weaker valued-field data and is compatible with
the canonical construction; no failure of invariance under exponential-field
automorphisms is asserted. The criterion is an exact reduction, not a
classification of multiplier rings; intermediate rings and orbits under the
full valued automorphism group are not classified. No claim that distinct
noncanonical exponentials of source 21 are isomorphic or not to each other
(their non-isomorphism with `Exp` is the merge's Corollary 19.40); the split and
nonsplit minimal examples are nonisomorphic, with no claim about their
first-order theories. Reflection gives unboundedly many fragments, not every
one, and no computable least `λ`; no large-cardinal strength is hidden. Failure
of saturation concerns the expansion, and `Z_E = Z` does not axiomatize
standardness; no tameness, decidability, o-minimality or elementary-equivalence
claims, no finite names or computable oracles. `E' = E` is the fine derivative,
not the Berarducci–Mantova derivation; strong sums are not fine limits.
`No(ε₀)` is not asserted to be a full Hahn field; `Ẑ/Z` is an abstract group;
the counts on `R((t^Q))` are of embedded groups and use no continuum
hypothesis. Both are AI-assisted and unrefereed, not Lean-verified; neither
built nor modified the repository; their Lean routes are proposals; their finite
checks do not reach the transfinite arguments; novelty rests on targeted
audits, and failure to find a prior statement is not proof of priority.

## Stale statements corrected

- Source 19 lists "exact displacement at infinite radii" among the connections
  it adds, and presents torsion, small-set discreteness and the extension
  classification as its own development. At its pin `dcf86662b574` this article
  already contained all of them (Corollary 5.5 with equation (5.13), Corollary
  4.3, Proposition 2.4, Theorems 17.4 and 17.6), unchanged since. They are
  printed once, credited to both (Section 18.1).
- Source 19 names the exact class-group splitting as a next formal target. Its
  list of inspected files does not include the formalization ledger, which
  already at its pin — and now — records Lean proofs of the analysis report's
  infinitesimal exp/log group isomorphism, the purely imaginary logarithm of a
  unit, and surjectivity of the finite phase with kernel `2πZ`, and of the
  affine and projective circle charts. The splitting of Theorem 4.2 itself and
  its fine version (Theorem 18.14) remain unmapped. Stated in Section 18.12.
- Source 19 calls higher-dimensional orthogonal groups a natural extension. The
  collection now contains `docs/surreal/euclidean-three-space`, placed in the
  same batch, which treats `SO(3,No)`.
- This README previously said 58 pages and 81 numbered results (now 73 and 97),
  pointed to "Section 9.6" for the three certificates (it is 9.5) and to "§18.4"
  for the non-claims (now 19.4), and listed the source `.tex` files as if they
  were present; they are not shipped.
- Cross-references in the PDF named every numbered result "theorem" regardless
  of its kind (for example "theorem 2.2" for Lemma 2.2). Alias counters now give
  each its own name; no number changed.

- Section 17 said that the character classification does not answer the
  Ehrlich–Kaplan robustness questions, and the non-claims (item 21, now in
  Section 20.4) repeated it. That stays true of Theorem 17.4 by itself; the text
  now records what sources 20 and 21 add and that the questions remain open.
  The title page's count of manuscripts (four) and this README's page count (73)
  were updated.
- Source 20 credits this report for the finite phase, the classification and
  the infinite periods, correctly, but not the automorphism report for its shift
  automorphisms (they are `saut:thm:shiftflow`), nor the `Z`-group literature;
  both credits are added in Section 19.1.
- Source 21 reports that the strip map printed on p. 33 of arXiv v3 of
  Ehrlich–Kaplan has sine and cosine interchanged. That page was checked for
  this merge and reads so (Remark 19.34); nothing depends on it.

## Relation to the neighbouring reports

**[analysis](../analysis/)** proves the finite polar decomposition and the
infinitesimal exp/log isomorphism (`e:prop-polar`, `e:prop-infexp`), which the
ledger maps to Lean on the actual surcomplex field; Theorem 4.2 here is the
same finite-angle statement, with the canonical splitting and the rotation-group
consequences of Section 18.

**[euclidean-three-space](../../surreal/euclidean-three-space/)** (placed with
source 19, not yet merged) develops rotations of `No³`, `SO(3,No)` and
quaternions, citing this report for finite angles. Its rotations are
noncommutative, where Section 18's plane case is abelian.

**[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/)** studies
field automorphisms of `No[i]`. It cites Theorem 4.5 here
(`trigonometry:thm:cayley`) for its Cayley map and contrasts rotations, which
preserve every modulus, with field automorphisms. The automorphisms `Ξ_a` of
Section 18.8 are group automorphisms of the unit circle, not field
automorphisms. Its fixed-shift flows `T_s` (Theorem 5.2,
`saut:thm:shiftflow`) are, with `δ = 1`, `λ = [·]₀` and `s = −c`, the shifts
`Sh_c` of Section 19.10, which act freely on all phases.

**[analysis](../analysis/)**'s one-parameter family of global exponentials
(`e:thm-twisted`) is a slice of the character family of Theorem 17.4, whose
period arithmetic Section 19 studies. The
**[differential-equations](../differential-equations/)** and
**[surquaternions](../../surquaternions/surquaternions/)** reports mention the
Ehrlich–Kaplan robustness questions as not settled; that remains true, with the
partial answer of Section 19.8.

## What was run

On Python 3.14.4 with SymPy 1.14.0, each script on a copy outside this
directory:

- `code/16-finite-radians-angular-phenomena.py --output …`: 67 checks passed;
  identical to `data/16-…-verification_report.txt` apart from line endings.
- `code/17-canonical-phases-degeneration.py`: 43 checks passed; identical to
  `data/17-…-verification_report.txt` apart from line endings.
- `code/18-canonical-angles-oscillation.py --report …`: 68 checks passed;
  identical to `data/18-…-verification_report.txt` apart from the recorded
  Python version (3.13.5 there) and line endings.
- `code/19-rotation-group-verify.py`: all 41 finite symbolic checks passed;
  output identical to `data/19-rotation-group-verification_results.json` apart
  from line endings.
- `code/20-exponential-kernels-verify.py --output r20.json`: "PASS: 47939 exact
  finite checks"; identical to `data/20-…-verification_results.json` apart
  from the `generated_utc` timestamp and line endings.
- `code/21-period-arithmetic-verify_examples.py`: `"status": "PASS"`, with 128
  CRT moduli, 645 compatibility pairs, 58,081 additivity pairs, 15 displayed
  assertions, 1,575 translation coefficients, 24 witnesses and 20 shadow
  checks; its `verification.json` is identical to
  `data/21-…-verification.json` apart from line endings.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`: 96 pages,
  no errors, no undefined references or citations, no multiply defined labels,
  no duplicate PDF destinations, no overfull or underfull boxes, no LaTeX or
  package warnings.

A clean compile and passing finite checks prove nothing about the infinite
arguments.

## Build and reproduce

A LaTeX distribution with the AMS packages, Latin Modern, geometry, microtype,
booktabs, longtable, array, enumitem, aliascnt, xcolor, fancyhdr, hyperref and
cleveref. The bibliography is embedded; no BibTeX or Biber run is needed.

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
latexmk -c
```

**Run the programs on a copy, never in this directory.** Each writes next to
its own file unless told otherwise: 16 and 17 both write
`verification_report.txt` beside the script (so run in one directory the second
overwrites the first; 16 accepts `--output PATH`), 18 writes only with
`--report PATH`, 19 writes `verification_results.json` beside the script, 20
writes `verification_results.json` in the current directory unless given
`--output PATH`, and 21 always writes `verification.json` beside the script.
16–19 need SymPy (`data/*-requirements.txt`, SymPy 1.14.0); 20 and 21 need only
the Python standard library (3.10 or later). For example:

```
mkdir -p /tmp/trig && cp code/*.py /tmp/trig/ && cd /tmp/trig
python 16-finite-radians-angular-phenomena.py --output r16.txt   # compare with data/16-…-verification_report.txt
python 17-canonical-phases-degeneration.py                      # writes verification_report.txt; compare with data/17-…
python 18-canonical-angles-oscillation.py --report r18.txt       # compare with data/18-…
python 19-rotation-group-verify.py                              # writes verification_results.json; compare with data/19-…
python 20-exponential-kernels-verify.py --output r20.json        # compare with data/20-… (timestamp differs)
python 21-period-arithmetic-verify_examples.py                  # writes verification.json; compare with data/21-…
```

`code/19-rotation-group-build.sh` and `.ps1` are source 19's delivered build
scripts; they build its original `surreal_rotation_group.tex`, which is not
shipped, and do not build this report. They are kept only as delivered.
Likewise `code/20-exponential-kernels-build.sh` compiles source 20's unshipped
`surcomplex_exponential_kernels.tex`, copies the result over a PDF of that name
and rewrites `verification_results.json`, and `code/21-period-arithmetic-Makefile`
runs an unprefixed `verify_examples.py` and `latexmk article.tex` in the current
directory; neither builds this report as intended, and neither should be run
here.

## Notation review — 22 September 2026

The asymptotic conventions now use the defined complex infinitesimal ideal
`m_C`, require a nonzero denominator, and explicitly apply to both surreal
and surcomplex arguments. These are algebraic size relations, with no
sequential-limit interpretation.
