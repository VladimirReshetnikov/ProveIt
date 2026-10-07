import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankRationalDecay
import OAI.Combinatorics.Progressions.Polynomial.AllocatedSeparatedCongruencePolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

omit [∀ j, Fintype (I j)] in

theorem allocatedCongruenceForecastRankConstant_dimension
    (hm : 0 < m) (D : ℕ)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D) :
    ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) := by
  apply modularForecastRankConstant_dimension
  rw [Fintype.card_sigma]
  exact (allocatedCongruenceRankOutput_sum_card_le hm inactive).trans hD

theorem allocatedCongruence_rational_order_bounds
    (hm : 0 < m) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m C)
    (R : ℕ) (hbad : (∏ p : P, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block P A C p.val) ≤ R)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ)
    (origin : ∀ p : P, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (T : ℕ) (hT : 0 < T) :
    letI : DecidableEq P := Classical.decEq _
    letI : NeZero (∏ p : P, p.val ^ A p.val) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
    let law := crtPrimePowerPolynomialLaw
      (V := LayerSamplerLongVariables inactive G B) (fun p : P => p.val) (fun p : P => A p.val)
    let Y := crtPrimePowerIntegerPolynomialOutput (fun p : P => p.val)
      (fun p : P => A p.val) (fun p : P => e p.val)
      (primePower_crt_coprime (fun p : P => p.val) (fun p : P => A p.val)
        (fun p => hp p.val p.property) Subtype.val_injective)
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) origin
    let cap := ((R * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m C * modularRankChargeFactor m)
    let S := Finset.univ.filter
      (fun χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
        ZMod (∏ p : P, p.val ^ A p.val)) ℂ => orderOf χ ≤ T)
    (∀ z, rationalOutputDensity law Y (∏ p : P, p.val ^ A p.val) z ≤ 1 + cap) ∧
    S.card ≤ T ^ (Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 1) ∧
    (∑ χ ∈ S, ‖finiteImageCharacteristic law
      (fun x j => (Y x j : ZMod (∏ p : P, p.val ^ A p.val))) χ‖) ≤
        (T : ℝ) ^ (Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 1) ∧
    ∀ z, ‖(rationalOutputDensity law Y (∏ p : P, p.val ^ A p.val) z : ℂ) -
      ∑ χ ∈ S, finiteImageCharacteristic law
        (fun x j => (Y x j : ZMod (∏ p : P, p.val ^ A p.val))) χ * star (χ z)‖ ≤ cap / T := by
  let : DecidableEq P := Classical.decEq _
  let : NeZero (∏ p : P, p.val ^ A p.val) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  have hcap : 0 ≤ ((R * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m C * modularRankChargeFactor m) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact rationalOutputDensity_order_bounds _ _ _ hcap hP
    (allocatedCongruence_crt_rational_decay_of_bad_product inactive noise r projection spatial kernel block
      hm P A e hp C hC R hbad base v origin) T hT

theorem allocatedCongruence_rational_inactive_bounds
    (hm : 0 < m) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m C)
    (R : ℕ) (hbad : (∏ p : P, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block P A C p.val) ≤ R)
    {U Z : Type*} [Fintype U] (inactiveLaw : FiniteProbabilityWeights U) (gridPoint : U → Z)
    (base : X → ℤ) (v : U → LayerSamplerVariables G I n B → ℤ)
    (origin : U → ∀ p : P, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (gridVolume : ℝ) (hV : 0 ≤ gridVolume) (T : ℕ) (hT : 0 < T)
    (z : Z) (β : Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : P, p.val ^ A p.val)) :
    letI : DecidableEq P := Classical.decEq _
    letI : NeZero (∏ p : P, p.val ^ A p.val) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
    let active := fun _ : U => crtPrimePowerPolynomialLaw
      (V := LayerSamplerLongVariables inactive G B) (fun p : P => p.val) (fun p : P => A p.val)
    let Y := fun u => crtPrimePowerIntegerPolynomialOutput (fun p : P => p.val)
      (fun p : P => A p.val) (fun p : P => e p.val)
      (primePower_crt_coprime (fun p : P => p.val) (fun p : P => A p.val)
        (fun p => hp p.val p.property) Subtype.val_injective)
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) (v u))
      (origin u)
    let cap := ((R * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m C * modularRankChargeFactor m)
    let S := Finset.univ.filter
      (fun χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
        ZMod (∏ p : P, p.val ^ A p.val)) ℂ => orderOf χ ≤ T)
    rationalInactiveForecast inactiveLaw active gridPoint Y
      (∏ p : P, p.val ^ A p.val) gridVolume z β ≤
      gridVolume * inactiveLaw.fiberMean gridPoint z (fun _ => 1) * (1 + cap) ∧
    ‖(rationalInactiveForecast inactiveLaw active gridPoint Y
        (∏ p : P, p.val ^ A p.val) gridVolume z β : ℂ) -
      (gridVolume : ℂ) * inactiveLaw.complexMean (fun u => if gridPoint u = z then
        ∑ χ ∈ S, finiteImageCharacteristic (active u)
          (fun x j => (Y u x j : ZMod (∏ p : P, p.val ^ A p.val))) χ * star (χ β) else 0)‖ ≤
      gridVolume * inactiveLaw.fiberMean gridPoint z (fun _ => 1) * (cap / T) := by
  let : DecidableEq P := Classical.decEq _
  let : NeZero (∏ p : P, p.val ^ A p.val) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  have hcap : 0 ≤ ((R * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m C * modularRankChargeFactor m) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hdecay (u : U) := allocatedCongruence_crt_rational_decay_of_bad_product
    inactive noise r projection spatial kernel block hm P A e hp C hC R hbad base (v u) (origin u)
  exact ⟨rationalInactiveForecast_cap inactiveLaw _ gridPoint _ _ hV hcap hP hdecay z β,
    rationalInactiveForecast_order_truncation inactiveLaw _ gridPoint _ _
      hV hcap hP hdecay T hT z β⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

local instance forecastModulusNeZero (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩

noncomputable def allocatedForecastPolynomial
    (inactive : LayerSamplerAxis I n → Prop)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : Sigma (AllocatedCongruenceRankOutput X E inactive)) :
    MvPolynomial (LayerSamplerLongVariables inactive G B ⊕
      (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ :=
  allocatedSeparatedCongruencePolynomial inactive o.1 base noise r (projection o.1) o.2

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

theorem allocatedForecastPolynomial_crt_decay_of_bad_product
    (hm : 0 < m) (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (C : ℝ) (hC : 0 ≤ C) (Rbad : ℕ)
    (hbad : (∏ p : Pr, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block Pr A C p.val) ≤ Rbad)
    (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : Pr, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq Pr := Classical.decEq _
    ‖finiteImageCharacteristic
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val)
        (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective) origin)
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial inactive base noise r projection) raw
        (∏ p : Pr, p.val ^ A p.val) t j : ZMod (∏ p : Pr, p.val ^ A p.val))) χ‖ ≤
      ((Rbad * ∏ p : Pr, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  let : DecidableEq Pr := Classical.decEq _
  have heq := crtPolynomialInputLaw_integerLong_characteristic_of_output
    (fun p : Pr => p.val) (fun p : Pr => A p.val) (fun p : Pr => e p.val)
    (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p => hp p.val p.property) Subtype.val_injective) origin
    (allocatedForecastPolynomial inactive base noise r projection) raw
    (crtPrimePowerIntegerPolynomialOutput (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p : Pr => e p.val)
      (primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p => hp p.val p.property) Subtype.val_injective)
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
        (samplerFrozenRaw (layerSamplerDegree I n) raw)) origin)
    (fun x j => by
      simpa only [crtPrimePowerIntegerPolynomialOutput, prescribedCRTPolynomialInput,
        allocatedForecastPolynomial] using
        (allocatedSeparatedCongruencePolynomial_eval inactive j.1 base noise r (projection j.1)
          j.2 _ raw).symm) χ
  rw [heq]
  exact allocatedCongruence_crt_rational_decay_of_bad_product
    inactive noise r projection spatial kernel block hm Pr A e hp C hC Rbad hbad base
    (samplerFrozenRaw (layerSamplerDegree I n) raw) origin χ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

noncomputable def allocatedCongruenceDeepBadDepth
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ)
    (stride : ℕ) (p : ℕ) : ℕ :=
  largestTestedBadDepth A
    (prescribedDeepBad (fun p => 2 * stride.factorization p)
      (allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C)) p
    (allocatedCongruenceIntegerSelectedCoefficients inactive noise r projection spatial kernel block)

theorem allocatedCongruence_bad_product_le_of_deep
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ)
    (hp : ∀ p ∈ P, p.Prime) {stride : ℕ} (hstride : 0 < stride) {R : ℕ}
    (hdeep : (∏ p : P, p.val ^ allocatedCongruenceDeepBadDepth
      inactive noise r projection spatial kernel block P A C stride p.val) ≤ R) :
    (∏ p : P, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block P A C p.val) ≤ stride ^ 2 * R := by
  let bad := allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C
  let x := allocatedCongruenceIntegerSelectedCoefficients inactive noise r projection spatial kernel block
  have hd : (∏ p ∈ P, p ^ largestTestedBadDepth A
      (prescribedDeepBad (fun p => 2 * stride.factorization p) bad) p x) ≤ R := by
    rw [Finset.prod_subtype P (fun _ => Iff.rfl)
      (fun p => p ^ largestTestedBadDepth A
        (prescribedDeepBad (fun p => 2 * stride.factorization p) bad) p x)]
    exact hdeep
  rw [← Finset.prod_subtype P (fun _ => Iff.rfl)
    (fun p => p ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block P A C p)]
  exact (largestBadPrimeProduct_le_stride_sq P A bad hp hstride x).trans
    (Nat.mul_le_mul_left (stride ^ 2) hd)

theorem allocatedCongruence_rational_order_bounds_of_deep_bad_product
    (hm : 0 < m) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m C)
    (stride : ℕ) (hstride : 0 < stride) (R : ℕ)
    (hdeep : (∏ p : P, p.val ^ allocatedCongruenceDeepBadDepth
      inactive noise r projection spatial kernel block P A C stride p.val) ≤ R)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ)
    (origin : ∀ p : P, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (T : ℕ) (hT : 0 < T) :
    letI : DecidableEq P := Classical.decEq _
    letI : NeZero (∏ p : P, p.val ^ A p.val) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
    let law := crtPrimePowerPolynomialLaw
      (V := LayerSamplerLongVariables inactive G B) (fun p : P => p.val) (fun p : P => A p.val)
    let Y := crtPrimePowerIntegerPolynomialOutput (fun p : P => p.val)
      (fun p : P => A p.val) (fun p : P => e p.val)
      (primePower_crt_coprime (fun p : P => p.val) (fun p : P => A p.val)
        (fun p => hp p.val p.property) Subtype.val_injective)
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) origin
    let cap := (((stride ^ 2 * R) * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m C * modularRankChargeFactor m)
    let S := Finset.univ.filter
      (fun χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
        ZMod (∏ p : P, p.val ^ A p.val)) ℂ => orderOf χ ≤ T)
    (∀ z, rationalOutputDensity law Y (∏ p : P, p.val ^ A p.val) z ≤ 1 + cap) ∧
    S.card ≤ T ^ (Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 1) ∧
    (∑ χ ∈ S, ‖finiteImageCharacteristic law
      (fun x j => (Y x j : ZMod (∏ p : P, p.val ^ A p.val))) χ‖) ≤
        (T : ℝ) ^ (Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 1) ∧
    ∀ z, ‖(rationalOutputDensity law Y (∏ p : P, p.val ^ A p.val) z : ℂ) -
      ∑ χ ∈ S, finiteImageCharacteristic law
        (fun x j => (Y x j : ZMod (∏ p : P, p.val ^ A p.val))) χ * star (χ z)‖ ≤ cap / T := by
  have hbad := allocatedCongruence_bad_product_le_of_deep
    inactive noise r projection spatial kernel block P A C hp hstride hdeep
  exact allocatedCongruence_rational_order_bounds
    inactive noise r projection spatial kernel block hm P A e hp C hC hP
    (stride ^ 2 * R) hbad base v origin T hT

theorem allocatedCongruence_rational_inactive_bounds_of_deep_bad_product
    (hm : 0 < m) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m C)
    (stride : ℕ) (hstride : 0 < stride) (R : ℕ)
    (hdeep : (∏ p : P, p.val ^ allocatedCongruenceDeepBadDepth
      inactive noise r projection spatial kernel block P A C stride p.val) ≤ R)
    {U Z : Type*} [Fintype U] (inactiveLaw : FiniteProbabilityWeights U) (gridPoint : U → Z)
    (base : X → ℤ) (v : U → LayerSamplerVariables G I n B → ℤ)
    (origin : U → ∀ p : P, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (gridVolume : ℝ) (hV : 0 ≤ gridVolume) (T : ℕ) (hT : 0 < T)
    (z : Z) (β : Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : P, p.val ^ A p.val)) :
    letI : DecidableEq P := Classical.decEq _
    letI : NeZero (∏ p : P, p.val ^ A p.val) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
    let active := fun _ : U => crtPrimePowerPolynomialLaw
      (V := LayerSamplerLongVariables inactive G B) (fun p : P => p.val) (fun p : P => A p.val)
    let Y := fun u => crtPrimePowerIntegerPolynomialOutput (fun p : P => p.val)
      (fun p : P => A p.val) (fun p : P => e p.val)
      (primePower_crt_coprime (fun p : P => p.val) (fun p : P => A p.val)
        (fun p => hp p.val p.property) Subtype.val_injective)
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) (v u))
      (origin u)
    let cap := (((stride ^ 2 * R) * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m C * modularRankChargeFactor m)
    let S := Finset.univ.filter
      (fun χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
        ZMod (∏ p : P, p.val ^ A p.val)) ℂ => orderOf χ ≤ T)
    rationalInactiveForecast inactiveLaw active gridPoint Y
      (∏ p : P, p.val ^ A p.val) gridVolume z β ≤
      gridVolume * inactiveLaw.fiberMean gridPoint z (fun _ => 1) * (1 + cap) ∧
    ‖(rationalInactiveForecast inactiveLaw active gridPoint Y
        (∏ p : P, p.val ^ A p.val) gridVolume z β : ℂ) -
      (gridVolume : ℂ) * inactiveLaw.complexMean (fun u => if gridPoint u = z then
        ∑ χ ∈ S, finiteImageCharacteristic (active u)
          (fun x j => (Y u x j : ZMod (∏ p : P, p.val ^ A p.val))) χ * star (χ β) else 0)‖ ≤
      gridVolume * inactiveLaw.fiberMean gridPoint z (fun _ => 1) * (cap / T) := by
  have hbad := allocatedCongruence_bad_product_le_of_deep
    inactive noise r projection spatial kernel block P A C hp hstride hdeep
  exact allocatedCongruence_rational_inactive_bounds
    inactive noise r projection spatial kernel block hm P A e hp C hC hP
    (stride ^ 2 * R) hbad inactiveLaw gridPoint base v origin gridVolume hV T hT z β

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

local instance forecastProductModulusNeZero (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩

theorem allocatedForecastPolynomial_rational_density_eq_crt
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod (∏ p : Pr, p.val ^ A p.val)) :
    letI : DecidableEq Pr := Classical.decEq _
    let hq := primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p => hp p.val p.property) Subtype.val_injective
    rationalOutputDensity
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val) hq origin)
      (integerLongPolynomialOutput (allocatedForecastPolynomial inactive base noise r projection) raw
        (∏ p : Pr, p.val ^ A p.val)) (∏ p : Pr, p.val ^ A p.val) β =
    rationalOutputDensity
      (crtPrimePowerPolynomialLaw (V := LayerSamplerLongVariables inactive G B)
        (fun p : Pr => p.val) (fun p : Pr => A p.val))
      (crtPrimePowerIntegerPolynomialOutput (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val) hq
        (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
          (samplerFrozenRaw (layerSamplerDegree I n) raw)) origin)
      (∏ p : Pr, p.val ^ A p.val) β := by
  let : DecidableEq Pr := Classical.decEq _
  intro hq
  apply Complex.ofReal_injective
  rw [rationalOutputDensity_fourier, rationalOutputDensity_fourier]
  apply Finset.sum_congr rfl
  intro χ _
  congr 1
  exact crtPolynomialInputLaw_integerLong_characteristic_of_output
    (fun p : Pr => p.val) (fun p : Pr => A p.val) (fun p : Pr => e p.val) hq origin
    (allocatedForecastPolynomial inactive base noise r projection) raw
    (crtPrimePowerIntegerPolynomialOutput (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p : Pr => e p.val) hq
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
        (samplerFrozenRaw (layerSamplerDegree I n) raw)) origin)
    (fun x j => by
      simpa only [crtPrimePowerIntegerPolynomialOutput, prescribedCRTPolynomialInput,
        allocatedForecastPolynomial] using
        (allocatedSeparatedCongruencePolynomial_eval inactive j.1 base noise r (projection j.1)
          j.2 _ raw).symm) χ

theorem allocatedForecastPolynomial_rational_density_product
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ Pr, p.Prime) (base : X → ℤ)
    (origin : ∀ p : Pr, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod (∏ p : Pr, p.val ^ A p.val)) :
    letI : DecidableEq Pr := Classical.decEq _
    let hq := primePower_crt_coprime (fun p : Pr => p.val) (fun p : Pr => A p.val)
      (fun p => hp p.val p.property) Subtype.val_injective
    rationalOutputDensity
      (crtPolynomialInputLaw (fun p : Pr => p.val) (fun p : Pr => A p.val)
        (fun p : Pr => e p.val) hq origin)
      (integerLongPolynomialOutput (allocatedForecastPolynomial inactive base noise r projection) raw
        (∏ p : Pr, p.val ^ A p.val)) (∏ p : Pr, p.val ^ A p.val) β =
      ∏ p : Pr, rationalOutputDensity
        (FiniteProbabilityWeights.uniform (LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val)))
        (localPrimePowerIntegerPolynomialOutput p.val (A p.val) (e p.val)
          (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
            (samplerFrozenRaw (layerSamplerDegree I n) raw)) (origin p)) (p.val ^ A p.val)
        (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun p : Pr => p.val ^ A p.val)
          (Finset.mem_univ p)) (ZMod (p.val ^ A p.val)) (β j)) := by
  let : DecidableEq Pr := Classical.decEq _
  intro hq
  apply (allocatedForecastPolynomial_rational_density_eq_crt inactive noise r projection
    Pr A e hp base origin raw β).trans
  have h := crt_integer_polynomial_rational_density_product
      (fun p : Pr => p.val) (fun p : Pr => A p.val) (fun p : Pr => e p.val) hq
      (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j)
        (samplerFrozenRaw (layerSamplerDegree I n) raw)) origin β
  convert h using 1 <;> congr 1
  funext p
  congr 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem samplerSeparated_eval₂_raw_congr
    {D G R : Type*} {B : D → Type*} [CommRing R]
    (inactive : D → Prop) (h : D → ℕ)
    (poly : MvPolynomial (SamplerTupleIndex G B h) ℤ)
    (long : SamplerLongVariables inactive G B h → R)
    (v w : PrincipalTupleIndex B h × Option Empty → R)
    (hvw : ∀ j : PrincipalTupleIndex B h, inactive j.1 → v (j, none) = w (j, none)) :
    MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long v)
        (rename (samplerSeparatedVariable inactive h) poly) =
      MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long w)
        (rename (samplerSeparatedVariable inactive h) poly) := by
  simp only [eval₂_rename]
  congr 1
  funext k
  cases k with
  | inl g => rfl
  | inr j =>
    by_cases hj : inactive j.1
    · simpa only [Function.comp_apply, samplerSeparatedVariable_inactive inactive h _ _ _ hj,
        Sum.elim_inr] using hvw j hj
    · simp only [Function.comp_apply, samplerSeparatedVariable_active inactive h _ _ _ hj,
        Sum.elim_inl]

namespace VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedForecastPolynomial_eval₂_raw_congr
    (inactive : LayerSamplerAxis I n → Prop)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    {R : Type*} [CommRing R]
    (long : LayerSamplerLongVariables inactive G B → R)
    (v w : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → R)
    (hvw : ∀ j : PrincipalTupleIndex B (layerSamplerDegree I n),
      inactive j.1 → v (j, none) = w (j, none))
    (o : Sigma (AllocatedCongruenceRankOutput X E inactive)) :
    MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long v)
        (allocatedForecastPolynomial inactive base noise deck projection o) =
      MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long w)
        (allocatedForecastPolynomial inactive base noise deck projection o) :=
  samplerSeparated_eval₂_raw_congr inactive (layerSamplerDegree I n)
    (allocatedUnconditionedCongruenceIntegerPolynomial inactive o.1 base noise deck
      (projection o.1) o.2) long v w hvw

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides

noncomputable def allocatedShortPrincipalRaw (u : ShortTuple)
    (k : PrincipalTupleIndex B degree × Option Empty) : ℤ :=
  if hk : short k.1.1 then (u ⟨⟨k.1.1, hk⟩, k.1.2⟩ k.2 : ℤ) else 0

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedShortPrincipalRaw_restrict
    (v : PrincipalIntegerTuples B degree Empty sides)
    (j : PrincipalTupleIndex B degree) (hj : short j.1) :
    allocatedShortPrincipalRaw B U basis S (principalAxisRestrict short v) (j, none) =
      (v j none : ℤ) := by
  simp only [allocatedShortPrincipalRaw, hj, dite_true, principalAxisRestrict]

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedForecastPolynomial_short_raw
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (long : LayerSamplerLongVariables short G B → ZMod q)
    (v : PrincipalIntegerTuples B degree Empty sides)
    (o : Sigma (AllocatedCongruenceRankOutput X E short)) :
    MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim long (fun k => ((v k.1 k.2 : ℤ) : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim long (fun k => (allocatedShortPrincipalRaw B U basis S
          (principalAxisRestrict short v) k : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) := by
  apply allocatedForecastPolynomial_eval₂_raw_congr
  intro j hj
  rw [allocatedShortPrincipalRaw_restrict B U basis S v j hj]

end VectorPolynomial
end Erdos3

end

end OAI
