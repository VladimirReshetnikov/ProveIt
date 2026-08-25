import IntegerPoints.IwaniecMozzochiSection11Conclusion

/-!
# Iwaniec--Mozzochi (12.4): the exact (11.7) specialization

The Fourier integral in (10.2) is literally the incomplete Bessel integral
of Section 11 with

```text
  f(xi) = chi (xi / H) * sigma (ell / (2 * gamma * c * N * xi)),
  a     = ell^2 / (4 * gamma * c^2),
  b     = k / c,
  X     = H.
```

This module records that equality and the exact consequence of (11.7) for a
fixed pair of cutoffs and every translation of the second cutoff.  Equation
(11.7) chooses its constant before the weight `f`; hence it really does give
one pointwise stationary-phase constant for all translations once their
support and derivative bounds share one constant.

That pointwise estimate is not equation (12.4).  After applying it to
`I(k - kappa, ell)`, Section 12 still has to

* replace the stationary amplitudes at `k - kappa` by those at `k`;
* make the second-order square-root phase expansion and sum its errors;
* combine the result with (10.2) and the nonstationary truncation (10.6);
* separate both smooth factors by Mellin inversion with common witnesses; and
* assemble the resulting comparable ranges into the 72 blocks of (12.4).

For the Section 13 application every constant in those operations must be
chosen before `s ∈ [0,3]`.  The downstream
`IwaniecMozzochiEq124PostStationaryBridge` module therefore names the
post-stationary implication explicitly.  It is an honest residual, not a
claim that (11.7) alone proves the translation-uniform form of (12.4).
-/

namespace LeanProofs.IntegerPoints

/-- The smooth factor in `fourierI`, viewed as the weight of the incomplete
Bessel integral (11.1). -/
noncomputable def section12BesselWeight
    (chi sigma : Real → Real) (gamma c H N ell xi : Real) : Real :=
  chi (xi / H) * sigma (ell / (2 * gamma * c * N * xi))

/-- The reciprocal-phase coefficient `a` when `fourierI` is written as an
incomplete Bessel integral. -/
noncomputable def section12BesselA (gamma c ell : Real) : Real :=
  ell ^ 2 / (4 * gamma * c ^ 2)

/-- The linear-phase coefficient `b` when `fourierI` is written as an
incomplete Bessel integral. -/
noncomputable def section12BesselB (c k : Real) : Real :=
  k / c

/-- The stationary main term obtained by substituting the Section 12
parameters into (11.7). -/
noncomputable def section12Eq117MainTerm
    (chi sigma : Real → Real) (gamma c H N k ell : Real) : Complex :=
  (2 * Complex.I * (section12BesselA gamma c ell : Complex)) ^
      (-(1 : Complex) / 2) *
    e (-2 * Real.sqrt
      (section12BesselA gamma c ell * section12BesselB c k)) *
    (section12BesselWeight chi sigma gamma c H N ell
      (Real.sqrt (section12BesselA gamma c ell / section12BesselB c k)) :
        Complex)

/-- The scale multiplying the absolute constant in the specialized (11.7)
remainder estimate. -/
noncomputable def section12Eq117ErrorScale
    (gamma c H k ell : Real) : Real :=
  ((section12BesselB c k) ^ (-(3 : Real) / 2) +
      (section12BesselA gamma c ell) ^ (-(1 : Real) / 2) *
        (section12BesselB c k) ^ (-(2 : Real))) *
    H ^ (-(2 : Real))

/-- The Fourier integral of (10.2) is exactly the incomplete Bessel integral
to which (11.7) applies.  No positivity hypothesis is needed for this
algebraic identity. -/
theorem fourierI_eq_section12_incompleteBessel
    (chi sigma : Real → Real) (gamma c H N k ell : Real) :
    fourierI chi sigma gamma c H N k ell =
      incompleteBessel (section12BesselWeight chi sigma gamma c H N ell)
        (section12BesselA gamma c ell) (section12BesselB c k) := by
  unfold fourierI incompleteBessel section12BesselWeight
    section12BesselA section12BesselB
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun xi => by
    have hamplitude :
        xi ^ (-(3 : Real) / 2) * chi (xi / H) *
            sigma (ell / (2 * gamma * c * N * xi)) =
          xi ^ (-(3 : Real) / 2) *
            (chi (xi / H) * sigma (ell / (2 * gamma * c * N * xi))) := by
      ring
    have hphase :
        -(ell ^ 2) / (4 * gamma * c ^ 2 * xi) - xi * k / c =
          -(ell ^ 2 / (4 * gamma * c ^ 2)) / xi - (k / c) * xi := by
      ring
    change
      ((xi ^ (-(3 : Real) / 2) * chi (xi / H) *
          sigma (ell / (2 * gamma * c * N * xi)) : Real) : Complex) *
          e (-(ell ^ 2) / (4 * gamma * c ^ 2 * xi) - xi * k / c) =
        ((xi ^ (-(3 : Real) / 2) *
            (chi (xi / H) * sigma (ell / (2 * gamma * c * N * xi))) : Real) :
            Complex) *
          e (-(ell ^ 2 / (4 * gamma * c ^ 2)) / xi - (k / c) * xi)
    rw [hamplitude, hphase]

/-- The dyadic cutoff alone places every nonzero specialized Bessel weight in
the deliberately relaxed support interval `[H/4, 4H]` required below.  The
second cutoff can only shrink that support. -/
theorem section12BesselWeight_support_of_dyadicPartition
    {chi sigma : Real → Real} (hchi : IsDyadicPartition chi)
    {gamma c H N ell xi : Real} (hH : 0 < H)
    (hweight : section12BesselWeight chi sigma gamma c H N ell xi ≠ 0) :
    (1 / 4 : Real) * H ≤ xi ∧ xi ≤ H / (1 / 4 : Real) := by
  have hchiNonzero : chi (xi / H) ≠ 0 := by
    intro hzero
    apply hweight
    simp [section12BesselWeight, hzero]
  have hlowerRatio : 1 < xi / H := by
    by_contra hnot
    exact hchiNonzero (hchi.2.2.2.2 _ (le_of_not_gt hnot))
  have hupperRatio : xi / H < 4 := by
    by_contra hnot
    exact hchiNonzero (hchi.2.1 _ (le_of_not_gt hnot))
  have hlower : H < xi := by
    have := (lt_div_iff₀ hH).mp hlowerRatio
    simpa using this
  have hupper : xi < 4 * H := by
    exact (div_lt_iff₀ hH).mp hupperRatio
  constructor
  · calc
      (1 / 4 : Real) * H ≤ H := by nlinarith
      _ ≤ xi := hlower.le
  · calc
      xi ≤ 4 * H := hupper.le
      _ = H / (1 / 4 : Real) := by ring

/-- Uniform smoothness and the scale-normalized second- and third-derivative
bounds needed to apply (11.7) simultaneously to all translated Section 12
weights.

For fixed smooth compactly supported `chi,rho` this is the cutoff-calculus
input: translation does not change derivative sup norms, and on the overlap
of the two supports the ratio `ell / (2*gamma*c*N*H)` stays in a fixed compact
range.  It is kept separate from the later Section 12 summation argument. -/
def Section12Eq117RegularityFor (chi rho : Real → Real) : Prop :=
  ∃ D : Real, 0 < D ∧
    ∀ s gamma c H N ell : Real,
      0 ≤ s → s ≤ 3 → 0 < gamma → 0 < c →
      0 < H → 0 < N → 0 < ell →
        IsSmoothCompactPos
            (section12BesselWeight chi (fun u => rho (u - s))
              gamma c H N ell) ∧
          (∀ xi : Real,
            |iteratedDeriv 2
                (section12BesselWeight chi (fun u => rho (u - s))
                  gamma c H N ell) xi| ≤
              D * H ^ (-(2 : Real))) ∧
          (∀ xi : Real,
            |iteratedDeriv 3
                (section12BesselWeight chi (fun u => rho (u - s))
                  gamma c H N ell) xi| ≤
              D * H ^ (-(3 : Real)))

/-- The exact translation-uniform pointwise stationary-phase estimate that
(11.7) contributes to Section 12.  This deliberately stops before summing in
`k,ell,a,c` or performing Mellin separation. -/
def UniformShiftEq117StationaryFor (chi rho : Real → Real) : Prop :=
  ∃ Q : Real,
    ∀ s gamma c H N k ell : Real,
      0 ≤ s → s ≤ 3 → 0 < gamma → 0 < c →
      0 < H → 0 < N → 0 < k → 0 < ell →
        norm (fourierI chi (fun u => rho (u - s)) gamma c H N k ell -
          section12Eq117MainTerm chi (fun u => rho (u - s))
            gamma c H N k ell) ≤
          Q * section12Eq117ErrorScale gamma c H k ell

/-- Equation (11.7), together with one uniform cutoff-regularity constant,
gives the complete pointwise stationary-phase input uniformly in
`s in [0,3]`. -/
theorem uniformShiftEq117StationaryFor_of_eq117
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (h117 : iwaniecMozzochi_eq117)
    (hregularity : Section12Eq117RegularityFor chi rho) :
    UniformShiftEq117StationaryFor chi rho := by
  obtain ⟨D, hD, hregularity⟩ := hregularity
  obtain ⟨Q, hQ⟩ := h117 (1 / 4 : Real) D (by norm_num) (by norm_num) hD
  refine ⟨Q, ?_⟩
  intro s gamma c H N k ell hsZero hsThree hgamma hc hH hN hk hell
  obtain ⟨hweightSmooth, hderivTwo, hderivThree⟩ :=
    hregularity s gamma c H N ell hsZero hsThree hgamma hc hH hN hell
  have ha : 0 < section12BesselA gamma c ell := by
    unfold section12BesselA
    positivity
  have hb : 0 < section12BesselB c k := by
    unfold section12BesselB
    positivity
  rw [fourierI_eq_section12_incompleteBessel]
  unfold section12Eq117MainTerm section12Eq117ErrorScale
  exact hQ _ _ _ H hweightSmooth ha hb hH
    (fun xi hxi =>
      section12BesselWeight_support_of_dyadicPartition hchi hH hxi)
    hderivTwo hderivThree

/-- The completed Section 11 development supplies the pointwise Section 12
input unconditionally once the translated weights have one regularity
constant. -/
theorem uniformShiftEq117StationaryFor_of_regular
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hregularity : Section12Eq117RegularityFor chi rho) :
    UniformShiftEq117StationaryFor chi rho :=
  uniformShiftEq117StationaryFor_of_eq117 hchi
    iwaniecMozzochi_eq117_holds hregularity

end LeanProofs.IntegerPoints
