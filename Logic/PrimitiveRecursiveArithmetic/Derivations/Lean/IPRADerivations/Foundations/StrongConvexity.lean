import IPRADerivations.Core.IntOrder

/-!
# Quantitative uniqueness from strong convexity

Packet `foundations/ipra_finite_use_framework_2026-11-15_v2`,
`sections/09_compactness.tex`, the strong-convexity inequality preceding
`cor:strong-minimizer`.

Objective values and their common lower bound are signed rational numerators
over a common positive denominator `D`. The convexity coefficient is `m/M`,
the distance is `a/b`, and the residual tolerance is `eta/D`. Clearing
denominators in the source midpoint inequality gives

`2 M b² F(mid) + 2 D m a² ≤ M b² (F(left) + F(right))`.

The theorem derives `D m a² ≤ M b² eta` from this inequality, the lower
bound at the midpoint, and the two residual bounds. A supplied rational
error schedule `M eta t² ≤ D m s²` then gives `t a ≤ s b`, namely
`distance ≤ s/t`. Both the signs of the objective and the denominators of
the coefficient, distance and tolerance are retained. These are finite
quantitative uniqueness lemmas; construction of a regular minimizer name
also needs the packet's domain, midpoint and approximation certificates.
-/

namespace LeanProofs.IPRA.Foundations.StrongConvexity

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A natural slack for the integer inequality `u ≤ v`. -/
private def slack (u v : ZT n) : PTm n :=
  monus (v.pos + u.neg) (u.pos + v.neg)

/-- The midpoint argument, for any natural denominator-clearing weight. -/
theorem penalty_bound (lower midpoint left right : ZT n) (weight penalty eta : PTm n)
    (hLower : Γ ⊢[PRAAx] zle lower midpoint)
    (hLeft : Γ ⊢[PRAAx] zle left (lower + ZT.ofNat eta))
    (hRight : Γ ⊢[PRAAx] zle right (lower + ZT.ofNat eta))
    (hConvex : Γ ⊢[PRAAx] zle
      (ZT.ofNat (two * weight) * midpoint + ZT.ofNat (two * penalty))
      (ZT.ofNat weight * (left + right))) :
    Γ ⊢[PRAAx] le penalty (weight * eta) := by
  have h0 := zle_toZ hLower
  have h1 := zle_toZ hLeft
  have h2 := zle_toZ hRight
  have h3 := zle_toZ hConvex
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at h1 h2 h3
  have doubled : Γ ⊢[PRAAx] le (two * penalty) (two * (weight * eta)) := by
    refine le_of_eq_add (d :=
      slack (ZT.ofNat (two * weight) * midpoint + ZT.ofNat (two * penalty))
        (ZT.ofNat weight * (left + right)) +
      weight * (slack left (lower + ZT.ofNat eta) + slack right (lower + ZT.ofNat eta)) +
      two * weight * slack lower midpoint) ?_
    apply deriveNat
    ipra_simps
    dsimp only [slack]
    linear_combination -h3 - 𝔞(weight) * h1 - 𝔞(weight) * h2 - 2 * 𝔞(weight) * h0
  exact mul_le_cancel doubled

/-- Arbitrary rational coefficient, distance and objective denominators. -/
theorem rational_squared_bound (lower midpoint left right : ZT n)
    (D m M a b eta : PTm n)
    (hLower : Γ ⊢[PRAAx] zle lower midpoint)
    (hLeft : Γ ⊢[PRAAx] zle left (lower + ZT.ofNat eta))
    (hRight : Γ ⊢[PRAAx] zle right (lower + ZT.ofNat eta))
    (hConvex : Γ ⊢[PRAAx] zle
      (ZT.ofNat (two * (M * b * b)) * midpoint + ZT.ofNat (two * (D * m * a * a)))
      (ZT.ofNat (M * b * b) * (left + right))) :
    Γ ⊢[PRAAx] le (D * m * a * a) (M * b * b * eta) :=
  penalty_bound lower midpoint left right _ _ _ hLower hLeft hRight hConvex

private alias cancel_positive := Common.mul_cancel_le

/-- The explicit error schedule turns the squared bound into a rational
distance estimate. The target radius `s/t` may be zero. -/
theorem distance_budget {D m M a b eta s t : PTm n}
    (hD : Γ ⊢[PRAAx] le one D) (hm : Γ ⊢[PRAAx] le one m)
    (hSquared : Γ ⊢[PRAAx] le (D * m * a * a) (M * b * b * eta))
    (hSchedule : Γ ⊢[PRAAx] le (M * eta * t * t) (D * m * s * s)) :
    Γ ⊢[PRAAx] le (t * a) (s * b) := by
  have first := mul_le_mul_right (t * t) hSquared
  have second := mul_le_mul_right (b * b) hSchedule
  have joined : Γ ⊢[PRAAx]
      le ((D * m) * ((t * a) * (t * a))) ((D * m) * ((s * b) * (s * b))) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (le_trans first (le_congr (by ipra_ring) (.eqRefl _) second))
  have positive : Γ ⊢[PRAAx] le one (D * m) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hD hm)
  exact nat_sqrt_mono (cancel_positive positive joined)

/-- The source quantitative uniqueness lemma, with an explicit rational
distance budget and signed objective values. -/
theorem rational_diameter (lower midpoint left right : ZT n)
    (D m M a b eta s t : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hm : Γ ⊢[PRAAx] le one m)
    (hLower : Γ ⊢[PRAAx] zle lower midpoint)
    (hLeft : Γ ⊢[PRAAx] zle left (lower + ZT.ofNat eta))
    (hRight : Γ ⊢[PRAAx] zle right (lower + ZT.ofNat eta))
    (hConvex : Γ ⊢[PRAAx] zle
      (ZT.ofNat (two * (M * b * b)) * midpoint + ZT.ofNat (two * (D * m * a * a)))
      (ZT.ofNat (M * b * b) * (left + right)))
    (hSchedule : Γ ⊢[PRAAx] le (M * eta * t * t) (D * m * s * s)) :
    Γ ⊢[PRAAx] le (t * a) (s * b) :=
  distance_budget hD hm
    (rational_squared_bound lower midpoint left right D m M a b eta hLower hLeft hRight hConvex)
    hSchedule

/-- Two exact minimizers have zero distance numerator. Positivity of the
convexity coefficient is used in the object theory when cancelling `D*m`. -/
theorem exact_minimizers (lower midpoint left right : ZT n) (D m M a b : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hm : Γ ⊢[PRAAx] le one m)
    (hLower : Γ ⊢[PRAAx] zle lower midpoint)
    (hLeft : Γ ⊢[PRAAx] zle left lower) (hRight : Γ ⊢[PRAAx] zle right lower)
    (hConvex : Γ ⊢[PRAAx] zle
      (ZT.ofNat (two * (M * b * b)) * midpoint + ZT.ofNat (two * (D * m * a * a)))
      (ZT.ofNat (M * b * b) * (left + right))) :
    Γ ⊢[PRAAx] a ≐ zero := by
  have left0 : Γ ⊢[PRAAx] zle left (lower + ZT.ofNat zero) := by
    apply zle_of_toZ (slack left lower)
    simpa [slack] using zle_toZ hLeft
  have right0 : Γ ⊢[PRAAx] zle right (lower + ZT.ofNat zero) := by
    apply zle_of_toZ (slack right lower)
    simpa [slack] using zle_toZ hRight
  have squared := rational_squared_bound lower midpoint left right D m M a b zero
    hLower left0 right0 hConvex
  have scaled : Γ ⊢[PRAAx] le ((D * m) * (a * a)) ((D * m) * (zero * zero)) :=
    le_congr (by ipra_ring) (by ipra_ring) squared
  have positive : Γ ⊢[PRAAx] le one (D * m) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hD hm)
  exact le_antisymm (nat_sqrt_mono (cancel_positive positive scaled)) (zero_le _)

/-- Slots `0,…,7` are the positive/negative parts of the lower bound,
midpoint and two endpoint values; `8,…,13` are `D,m,M,a,b,eta`. -/
def squaredFormula : Fm PTm 14 :=
  let lower : ZT 14 := ⟨var 0, var 1⟩
  let midpoint : ZT 14 := ⟨var 2, var 3⟩
  let left : ZT 14 := ⟨var 4, var 5⟩
  let right : ZT 14 := ⟨var 6, var 7⟩
  zle lower midpoint ⟶
  zle left (lower + ZT.ofNat (var 13)) ⟶
  zle right (lower + ZT.ofNat (var 13)) ⟶
  zle
    (ZT.ofNat (two * (var 10 * var 12 * var 12)) * midpoint +
      ZT.ofNat (two * (var 8 * var 9 * var 11 * var 11)))
    (ZT.ofNat (var 10 * var 12 * var 12) * (left + right)) ⟶
    le (var 8 * var 9 * var 11 * var 11) (var 10 * var 12 * var 12 * var 13)

/-- The full signed, denominator-cleared midpoint estimate, with no external
values or arithmetical proof obligations. -/
theorem rational_squared_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14 squaredFormula := by
  refine closeUniv 14 (.impI (.impI (.impI (.impI ?_))))
  exact rational_squared_bound ⟨var 0, var 1⟩ ⟨var 2, var 3⟩ ⟨var 4, var 5⟩ ⟨var 6, var 7⟩
    (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))

/-- The same slots as `squaredFormula`, with `s,t` in slots `14,15`.
All denominators, and the numerator of the convexity coefficient, are
explicitly positive for the rational interpretation. -/
def diameterFormula : Fm PTm 16 :=
  let lower : ZT 16 := ⟨var 0, var 1⟩
  let midpoint : ZT 16 := ⟨var 2, var 3⟩
  let left : ZT 16 := ⟨var 4, var 5⟩
  let right : ZT 16 := ⟨var 6, var 7⟩
  le one (var 8) ⟶ le one (var 9) ⟶ le one (var 10) ⟶
  le one (var 12) ⟶ le one (var 15) ⟶
  zle lower midpoint ⟶
  zle left (lower + ZT.ofNat (var 13)) ⟶
  zle right (lower + ZT.ofNat (var 13)) ⟶
  zle
    (ZT.ofNat (two * (var 10 * var 12 * var 12)) * midpoint +
      ZT.ofNat (two * (var 8 * var 9 * var 11 * var 11)))
    (ZT.ofNat (var 10 * var 12 * var 12) * (left + right)) ⟶
  le (var 10 * var 13 * var 15 * var 15) (var 8 * var 9 * var 14 * var 14) ⟶
    le (var 15 * var 11) (var 14 * var 12)

theorem rational_diameter_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16 diameterFormula := by
  refine closeUniv 16 (.impI (.impI (.impI (.impI (.impI
    (.impI (.impI (.impI (.impI (.impI ?_))))))))))
  exact rational_diameter ⟨var 0, var 1⟩ ⟨var 2, var 3⟩ ⟨var 4, var 5⟩ ⟨var 6, var 7⟩
    (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))

#print axioms penalty_bound
#print axioms distance_budget
#print axioms exact_minimizers
#print axioms rational_squared_closed
#print axioms rational_diameter_closed

end LeanProofs.IPRA.Foundations.StrongConvexity
