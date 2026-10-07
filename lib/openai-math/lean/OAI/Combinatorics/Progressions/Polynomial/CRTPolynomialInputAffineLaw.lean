import OAI.Combinatorics.Progressions.Estimates.FiniteImageProducts
import OAI.Combinatorics.Progressions.Estimates.InactiveFiberProductComparison
import OAI.Combinatorics.Progressions.Lattices.MixedSmoothUniformBadPrimeProduct

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtPrimePowerIntegerPolynomialOutput {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) : ℤ :=
  eval (fun v => ((crtInput (fun l => p l ^ A l) hq
    (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v) v).val : ℤ))
      (F j.1 j.2)

omit [Fintype V] in

theorem crtPrimePowerIntegerPolynomialOutput_reduce {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) [NeZero (∏ l, p l ^ A l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) :
    (crtPrimePowerIntegerPolynomialOutput p A e hq F r x j : ZMod (∏ l, p l ^ A l)) =
      crtPrimePowerPolynomialMap p A e hq F r x j.1 j.2 := by
  unfold crtPrimePowerIntegerPolynomialOutput crtPrimePowerPolynomialMap
  change (Int.castRingHom (ZMod (∏ l, p l ^ A l))) (eval₂ (RingHom.id ℤ) _ _) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]
  congr 1
  funext v
  simp only [Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]

def taggedPolynomialOutputCurry {s : ℕ} (J : Fin s → Type*) (N : ℕ) :
    (Sigma J → ZMod N) ≃+ (∀ j, J j → ZMod N) :=
  { Equiv.piCurry (fun _ (_ : J _) => ZMod N) with map_add' := fun _ _ => rfl }

section RankBounds

variable {s : ℕ} (hs : 0 < s) {J : Fin s → Type*} [∀ j, Fintype (J j)]
  (p A b e : L → ℕ) [∀ l, NeZero (p l)]
  (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
  (C : ℝ) (hC : 0 ≤ C)
  (F : ∀ j, J j → MvPolynomial V ℤ)
  (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
  (hrank : ∀ (l : L) (B : ℕ), b l < B → B ≤ A l → ∀ (j : Fin s)
    (row : J j → ZMod (p l ^ B)), (∃ i, IsUnit (row i)) →
    integerPolynomialRankProbability (p l) B j.val (F j) row ≤ (p l : ℝ) ^ (-C * B))
  (r : ∀ l, V → ZMod (p l ^ A l))

include hs hp hinj hC hF hrank

theorem crt_integer_polynomial_rational_characteristic_decay
    (χ : AddChar (Sigma J → ZMod (∏ l, p l ^ A l)) ℂ) :
    ‖finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A)
      (fun x j => (crtPrimePowerIntegerPolynomialOutput p A e
        (primePower_crt_coprime p A hp hinj) F r x j : ZMod (∏ l, p l ^ A l))) χ‖ ≤
      crtPolynomialCharge p b e s C * (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  let E := taggedPolynomialOutputCurry J (∏ l, p l ^ A l)
  let ψ := characterPullback E.symm.toAddMonoidHom χ
  have ho : orderOf ψ = orderOf χ :=
    characterPullback_order E.symm.toAddMonoidHom E.symm.surjective χ
  have h := crt_integer_polynomial_characteristic_decay hs p A b e hp hinj C hC F hF hrank r ψ
  rw [ho] at h
  simp_rw [crtPrimePowerIntegerPolynomialOutput_reduce]
  exact h

theorem crt_integer_polynomial_rational_order_bounds
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (T : ℕ) (hT : 0 < T) :
    letI : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    let law := crtPrimePowerPolynomialLaw (V := V) p A
    let Y := crtPrimePowerIntegerPolynomialOutput p A e (primePower_crt_coprime p A hp hinj) F r
    let cap := crtPolynomialCharge p b e s C
    let S := Finset.univ.filter
      (fun χ : AddChar (Sigma J → ZMod (∏ l, p l ^ A l)) ℂ => orderOf χ ≤ T)
    (∀ z, rationalOutputDensity law Y (∏ l, p l ^ A l) z ≤ 1 + cap) ∧
    S.card ≤ T ^ (Fintype.card (Sigma J) + 1) ∧
    (∑ χ ∈ S, ‖finiteImageCharacteristic law
      (fun x j => (Y x j : ZMod (∏ l, p l ^ A l))) χ‖) ≤
        (T : ℝ) ^ (Fintype.card (Sigma J) + 1) ∧
    ∀ z, ‖(rationalOutputDensity law Y (∏ l, p l ^ A l) z : ℂ) -
      ∑ χ ∈ S, finiteImageCharacteristic law
        (fun x j => (Y x j : ZMod (∏ l, p l ^ A l))) χ * star (χ z)‖ ≤ cap / T := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  exact rationalOutputDensity_order_bounds _ _ _
    (Real.rpow_nonneg (Finset.prod_nonneg (fun l _ => Nat.cast_nonneg _)) _) hP
    (crt_integer_polynomial_rational_characteristic_decay hs p A b e hp hinj C hC F hF hrank r)
    T hT

end RankBounds

theorem crt_integer_polynomial_rational_inactive_bounds
    {I Z : Type*} [Fintype I]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    {s : ℕ} (hs : 0 < s) {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A b e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : I → ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ i j k, (F i j k).totalDegree ≤ j.val + 1)
    (hrank : ∀ (i : I) (l : L) (B : ℕ), b l < B → B ≤ A l → ∀ (j : Fin s)
      (row : J j → ZMod (p l ^ B)), (∃ k, IsUnit (row k)) →
      integerPolynomialRankProbability (p l) B j.val (F i j) row ≤ (p l : ℝ) ^ (-C * B))
    (r : I → ∀ l, V → ZMod (p l ^ A l))
    (gridVolume : ℝ) (hV : 0 ≤ gridVolume) (T : ℕ) (hT : 0 < T)
    (z : Z) (β : Sigma J → ZMod (∏ l, p l ^ A l)) :
    letI : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    let active := fun _ : I => crtPrimePowerPolynomialLaw (V := V) p A
    let Y := fun i => crtPrimePowerIntegerPolynomialOutput p A e
      (primePower_crt_coprime p A hp hinj) (F i) (r i)
    let cap := crtPolynomialCharge p b e s C
    let S := Finset.univ.filter
      (fun χ : AddChar (Sigma J → ZMod (∏ l, p l ^ A l)) ℂ => orderOf χ ≤ T)
    rationalInactiveForecast inactive active gridPoint Y (∏ l, p l ^ A l) gridVolume z β ≤
      gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (1 + cap) ∧
    ‖(rationalInactiveForecast inactive active gridPoint Y
        (∏ l, p l ^ A l) gridVolume z β : ℂ) -
      (gridVolume : ℂ) * inactive.complexMean (fun i => if gridPoint i = z then
        ∑ χ ∈ S, finiteImageCharacteristic (active i)
          (fun x j => (Y i x j : ZMod (∏ l, p l ^ A l))) χ * star (χ β) else 0)‖ ≤
      gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (cap / T) := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  have hcap : 0 ≤ crtPolynomialCharge p b e s C :=
    Real.rpow_nonneg (Finset.prod_nonneg (fun l _ => Nat.cast_nonneg _)) _
  have hdecay (i : I) := crt_integer_polynomial_rational_characteristic_decay
    hs p A b e hp hinj C hC (F i) (hF i) (hrank i) (r i)
  exact ⟨rationalInactiveForecast_cap inactive _ gridPoint _ _ hV hcap hP hdecay z β,
    rationalInactiveForecast_order_truncation inactive _ gridPoint _ _
      hV hcap hP hdecay T hT z β⟩

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem finiteImageMass_outputEquiv {X Z W : Type*} [Fintype X]
    [DecidableEq Z] [DecidableEq W] (law : FiniteProbabilityWeights X)
    (Y : X → Z) (e : Z ≃ W) (z : Z) :
    finiteImageMass law (fun x => e (Y x)) (e z) = finiteImageMass law Y z := by
  unfold finiteImageMass
  simp only [e.injective.eq_iff]

noncomputable def localPrimePowerIntegerPolynomialOutput
    {V : Type*} {s : ℕ} {J : Fin s → Type*}
    (p A e : ℕ) (F : ∀ j, J j → MvPolynomial V ℤ)
    (r x : V → ZMod (p ^ A)) (j : Sigma J) : ℤ :=
  eval (fun v => ((r v + (p : ZMod (p ^ A)) ^ e * x v).val : ℤ)) (F j.1 j.2)

@[simp] theorem localPrimePowerIntegerPolynomialOutput_reduce
    {V : Type*} {s : ℕ} {J : Fin s → Type*}
    (p A e : ℕ) [NeZero (p ^ A)] (F : ∀ j, J j → MvPolynomial V ℤ)
    (r x : V → ZMod (p ^ A)) (j : Sigma J) :
    (localPrimePowerIntegerPolynomialOutput p A e F r x j : ZMod (p ^ A)) =
      eval₂ (Int.castRingHom (ZMod (p ^ A)))
        (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j.1 j.2) := by
  unfold localPrimePowerIntegerPolynomialOutput
  change (Int.castRingHom (ZMod (p ^ A))) (eval₂ (RingHom.id ℤ) _ _) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]
  congr 1
  funext v
  simp only [Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem crt_integer_polynomial_rational_density_product
    {L V : Type*} [Fintype L] [Fintype V] {s : ℕ}
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (r : ∀ l, V → ZMod (p l ^ A l))
    (z : Sigma J → ZMod (∏ l, p l ^ A l)) :
    let : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    rationalOutputDensity (crtPrimePowerPolynomialLaw (V := V) p A)
      (crtPrimePowerIntegerPolynomialOutput p A e hq F r) (∏ l, p l ^ A l) z =
      ∏ l, rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
        (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) F (r l)) (p l ^ A l)
        (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
          (Finset.mem_univ l)) (ZMod (p l ^ A l)) (z j)) := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  let outputEquiv : (Sigma J → ZMod (∏ l, p l ^ A l)) ≃
      (∀ l, Sigma J → ZMod (p l ^ A l)) :=
    (taggedPolynomialOutputCurry J _).toEquiv |>.trans
      ((taggedOutputCRTEquiv J (fun l => p l ^ A l) hq).toEquiv.trans
        (Equiv.piCongrRight (fun l => (taggedPolynomialOutputCurry J (p l ^ A l)).symm.toEquiv)))
  let localLaw := fun l => FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l))
  let Y := fun (l : L) (x : V → ZMod (p l ^ A l)) (j : Sigma J) =>
    (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) F (r l) x j : ZMod (p l ^ A l))
  let globalY := fun (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) =>
    (crtPrimePowerIntegerPolynomialOutput p A e hq F r x j : ZMod (∏ l, p l ^ A l))
  have heval (x : ∀ l, V → ZMod (p l ^ A l)) :
      outputEquiv (globalY x) = fun l => Y l (x l) := by
    funext l j
    change ZMod.prodEquivPi (fun l => p l ^ A l) hq (globalY x j) l = Y l (x l) j
    dsimp only [globalY, Y]
    rw [crtPrimePowerIntegerPolynomialOutput_reduce,
      localPrimePowerIntegerPolynomialOutput_reduce]
    exact crtInput_integerPolynomial_eval (fun l => p l ^ A l) hq (F j.1 j.2)
      (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v) l
  have hmass : finiteImageMass (FiniteProbabilityWeights.pi localLaw) globalY z =
      ∏ l, finiteImageMass (localLaw l) (Y l) (outputEquiv z l) := by
    rw [← finiteImageMass_outputEquiv _ globalY outputEquiv z]
    simp_rw [heval]
    exact finiteImageMass_pi localLaw Y (outputEquiv z)
  have hcard : Fintype.card (Sigma J → ZMod (∏ l, p l ^ A l)) =
      ∏ l, Fintype.card (Sigma J → ZMod (p l ^ A l)) :=
    (Fintype.card_congr outputEquiv).trans Fintype.card_pi
  change (Fintype.card (Sigma J → ZMod (∏ l, p l ^ A l)) : ℝ) *
      finiteImageMass (FiniteProbabilityWeights.pi localLaw) globalY z = _
  rw [hmass, hcard, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  unfold rationalOutputDensity
  congr 1
  apply congrArg (finiteImageMass (localLaw l) (Y l))
  funext j
  exact ZMod.prodEquivPi_apply (fun l => p l ^ A l) hq (z j) l

theorem crt_integer_polynomial_rational_inactive_density_product
    {L V I Z : Type*} [Fintype L] [Fintype V] [Fintype I] {s : ℕ}
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : I → ∀ j, J j → MvPolynomial V ℤ)
    (r : I → ∀ l, V → ZMod (p l ^ A l))
    (gridVolume : ℝ) (z : Z) (β : Sigma J → ZMod (∏ l, p l ^ A l)) :
    let : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    rationalInactiveForecast inactive (fun _ => crtPrimePowerPolynomialLaw (V := V) p A)
      gridPoint (fun i => crtPrimePowerIntegerPolynomialOutput p A e hq (F i) (r i))
      (∏ l, p l ^ A l) gridVolume z β =
      gridVolume * inactive.fiberMean gridPoint z (fun i =>
        ∏ l, rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
          (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) (F i) (r i l)) (p l ^ A l)
          (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
            (Finset.mem_univ l)) (ZMod (p l ^ A l)) (β j))) := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  unfold rationalInactiveForecast
  congr 1
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  exact crt_integer_polynomial_rational_density_product p A e hq (F i) (r i) β

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def prescribedCRTPolynomialInput
    (p A e : L → ℕ)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) : V → ZMod (∏ l, p l ^ A l) :=
  crtInput (fun l => p l ^ A l) hq
    (fun l v => origin l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)

local instance crtInputModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

noncomputable def crtPolynomialInputLaw
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) :
    FiniteProbabilityWeights (V → ZMod (∏ l, p l ^ A l)) :=
  (crtPrimePowerPolynomialLaw (V := V) p A).fiberLaw
    (prescribedCRTPolynomialInput p A e hq origin)

theorem crtPolynomialInputLaw_complexMean
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (f : (V → ZMod (∏ l, p l ^ A l)) → ℂ) :
    (crtPolynomialInputLaw p A e hq origin).complexMean f =
      (crtPrimePowerPolynomialLaw (V := V) p A).complexMean
        (fun x => f (prescribedCRTPolynomialInput p A e hq origin x)) :=
  FiniteProbabilityWeights.fiberLaw_complexMean _ _ _

theorem crtPolynomialInputLaw_integerLong_characteristic
    {Inactive Out : Type*}
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (poly : Out → MvPolynomial (V ⊕ Inactive) ℤ) (inactive : Inactive → ℤ)
    (χ : AddChar (Out → ZMod (∏ l, p l ^ A l)) ℂ) :
    finiteImageCharacteristic (crtPolynomialInputLaw p A e hq origin)
      (fun t j => (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l) t j :
        ZMod (∏ l, p l ^ A l))) χ =
    finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A)
      (fun x j => (MvPolynomial.eval
        (Sum.elim (fun v => ((prescribedCRTPolynomialInput p A e hq origin x v).val : ℤ))
          inactive) (poly j) : ZMod (∏ l, p l ^ A l))) χ :=
  crtPolynomialInputLaw_complexMean p A e hq origin _

theorem crtPolynomialInputLaw_integerLong_characteristic_of_output
    {Inactive Out : Type*}
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (poly : Out → MvPolynomial (V ⊕ Inactive) ℤ) (inactive : Inactive → ℤ)
    (Y : (∀ l, V → ZMod (p l ^ A l)) → Out → ℤ)
    (hY : ∀ x j, Y x j = MvPolynomial.eval
      (Sum.elim (fun v => ((prescribedCRTPolynomialInput p A e hq origin x v).val : ℤ))
        inactive) (poly j))
    (χ : AddChar (Out → ZMod (∏ l, p l ^ A l)) ℂ) :
    finiteImageCharacteristic (crtPolynomialInputLaw p A e hq origin)
      (fun t j => (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l) t j :
        ZMod (∏ l, p l ^ A l))) χ =
    finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A)
      (fun x j => (Y x j : ZMod (∏ l, p l ^ A l))) χ := by
  rw [crtPolynomialInputLaw_integerLong_characteristic]
  apply congrArg (fun F => finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := V) p A) F χ)
  funext x j
  rw [hY]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem exists_uniform_indexed_positive_product_cutoff
    {L : Type*} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ cutoff : ℕ, 0 < cutoff ∧ ∀ (p : L → ℕ), Function.Injective p →
      ∀ (S : Finset L) (f : L → ℝ),
      (∀ l ∈ S, cutoff < p l) → (∀ l ∈ S, 0 ≤ f l) →
      (∀ l ∈ S, |f l - 1| ≤ 2 / (p l : ℝ) ^ 2) →
      |(∏ l ∈ S, f l) - 1| ≤ δ := by
  obtain ⟨cutoff, hcutoff, htail⟩ :=
    exists_uniform_positive_product_cutoff (by norm_num : (0 : ℝ) ≤ 2) hδ hδ1
  refine ⟨cutoff, hcutoff, ?_⟩
  intro p hp S f hlarge hnonneg herror
  have h := htail (S.image p) (Function.extend p f (fun _ => 1))
    (by rintro q hq; obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq; exact hlarge l hl)
    (by
      rintro q hq
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
      simpa only [hp.extend_apply] using hnonneg l hl)
    (by
      rintro q hq
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
      simpa only [hp.extend_apply] using herror l hl)
  simpa only [Finset.prod_image hp.injOn, hp.extend_apply] using h

theorem retainedPrimePowerModulus_dvd {L : Type*} [Fintype L]
    (p A : L → ℕ) (retained : Finset L) :
    (∏ l : retained, p l.val ^ A l.val) ∣ ∏ l, p l ^ A l := by
  rw [Finset.prod_coe_sort (f := fun l => p l ^ A l)]
  exact Finset.prod_dvd_prod_of_subset retained Finset.univ (fun l => p l ^ A l)
    (Finset.subset_univ _)

theorem crt_integer_polynomial_retained_inactive_density_product
    {L V I Z : Type*} [Fintype L] [Fintype V] [Fintype I] {s : ℕ}
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : I → ∀ j, J j → MvPolynomial V ℤ)
    (r : I → ∀ l, V → ZMod (p l ^ A l))
    (retained : Finset L) (gridVolume : ℝ) (z : Z)
    (β : Sigma J → ZMod (∏ l, p l ^ A l)) :
    letI : DecidableEq retained := Classical.decEq retained
    let p' : retained → ℕ := fun l => p l.val
    let A' : retained → ℕ := fun l => A l.val
    let e' : retained → ℕ := fun l => e l.val
    let hq' : Pairwise (fun l k : retained => (p' l ^ A' l).Coprime (p' k ^ A' k)) :=
      fun _l _k hne => hq (fun heq => hne (Subtype.ext heq))
    letI : NeZero (∏ l : retained, p' l ^ A' l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l.val)))⟩
    rationalInactiveForecast inactive
      (fun _ => crtPrimePowerPolynomialLaw (V := V) p' A') gridPoint
      (fun i => crtPrimePowerIntegerPolynomialOutput p' A' e' hq' (F i) (fun l => r i l.val))
      (∏ l : retained, p' l ^ A' l) gridVolume z
      (fun j => ZMod.castHom (retainedPrimePowerModulus_dvd p A retained)
        (ZMod (∏ l : retained, p' l ^ A' l)) (β j)) =
      gridVolume * inactive.fiberMean gridPoint z (fun i =>
        ∏ l ∈ retained,
          rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
            (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) (F i) (r i l)) (p l ^ A l)
            (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
              (Finset.mem_univ l)) (ZMod (p l ^ A l)) (β j))) := by
  intro p' A' e' hq'
  let : NeZero (∏ l : retained, p' l ^ A' l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l.val)))⟩
  rw [crt_integer_polynomial_rational_inactive_density_product]
  congr 1
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  conv_rhs => rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro l _
  congr 1
  funext j
  exact congrArg (fun h : ZMod (∏ l, p l ^ A l) →+* ZMod (p l.val ^ A l.val) => h (β j))
    (ZMod.castHom_comp (Finset.dvd_prod_of_mem (fun k : retained => p' k ^ A' k)
      (Finset.mem_univ l)) (retainedPrimePowerModulus_dvd p A retained))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtInputAddEquiv (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (∀ l, V → ZMod (q l)) ≃+ (V → ZMod (∏ l, q l)) where
  toFun := crtInput q hq
  invFun x l v := ZMod.prodEquivPi q hq (x v) l
  left_inv x := by
    funext l v
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun k => x k v)) l
  right_inv x := by
    funext v
    exact (ZMod.prodEquivPi q hq).symm_apply_apply (x v)
  map_add' x y := by
    funext v
    exact map_add (ZMod.prodEquivPi q hq).symm (fun l => x l v) (fun l => y l v)

theorem crtPrimePowerPolynomialLaw_eq_uniform (p A : L → ℕ) [∀ l, NeZero (p l)] :
    crtPrimePowerPolynomialLaw (V := V) p A =
      FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l)) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  exact FiniteProbabilityWeights.pi_uniform_weight x

local instance crtAffineModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

noncomputable def prescribedCRTStep (p A e : L → ℕ)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k))) :
    ZMod (∏ l, p l ^ A l) :=
  (ZMod.prodEquivPi (fun l => p l ^ A l) hq).symm
    (fun l => (p l : ZMod (p l ^ A l)) ^ e l)

omit [Fintype V] in
theorem prescribedCRTPolynomialInput_eq_affine (p A e : L → ℕ)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) (x : ∀ l, V → ZMod (p l ^ A l)) :
    prescribedCRTPolynomialInput p A e hq origin x =
      fun v => crtInput (fun l => p l ^ A l) hq origin v +
        prescribedCRTStep p A e hq * crtInput (fun l => p l ^ A l) hq x v := by
  funext v
  change (ZMod.prodEquivPi (fun l => p l ^ A l) hq).symm
    ((fun l => origin l v) + (fun l => (p l : ZMod (p l ^ A l)) ^ e l) * (fun l => x l v)) = _
  rw [map_add, map_mul]
  rfl

theorem crtPolynomialInputLaw_affine_uniform (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) :
    crtPolynomialInputLaw p A e hq origin =
      (FiniteProbabilityWeights.uniform (V → ZMod (∏ l, p l ^ A l))).fiberLaw
        (fun x v => crtInput (fun l => p l ^ A l) hq origin v + prescribedCRTStep p A e hq * x v) := by
  let E := crtInputAddEquiv (V := V) (fun l => p l ^ A l) hq
  let f : (V → ZMod (∏ l, p l ^ A l)) → (V → ZMod (∏ l, p l ^ A l)) :=
    fun x v => crtInput (fun l => p l ^ A l) hq origin v + prescribedCRTStep p A e hq * x v
  have hu := uniform_fiberLaw_surjective_hom E.toAddMonoidHom E.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw E = _ at hu
  rw [crtPolynomialInputLaw, crtPrimePowerPolynomialLaw_eq_uniform]
  have heq : prescribedCRTPolynomialInput p A e hq origin = f ∘ E := by
    funext x
    exact prescribedCRTPolynomialInput_eq_affine p A e hq origin x
  rw [heq, ← FiniteProbabilityWeights.fiberLaw_comp, hu]

end Erdos3

end

end OAI
