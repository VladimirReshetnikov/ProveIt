/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Logic.Function.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import OAI.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools

namespace OAI


namespace Erdos3

open MvPolynomial

variable {σ : Type*}

noncomputable def roundedIntegerPolynomial (P : MvPolynomial σ ℝ) : MvPolynomial σ ℤ :=
  .ofCoeff ((AddMonoidAlgebra.coeff P).mapRange round round_zero)

@[simp] theorem roundedIntegerPolynomial_coeff (P : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (roundedIntegerPolynomial P).coeff a = round (P.coeff a) := rfl

theorem roundedIntegerPolynomial_real_degree (P : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (hP : P ∈ weightedSupportLE w d) :
    MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P) ∈ weightedSupportLE w d := by
  intro a ha
  apply hP
  change a ∈ (MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P)).support at ha
  change a ∈ P.support
  rw [MvPolynomial.mem_support_iff] at ha ⊢
  intro hp
  apply ha
  change (round (P.coeff a) : ℝ) = 0
  rw [hp, round_zero, Int.cast_zero]

theorem roundedIntegerPolynomial_remainder_bound (P : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    |(P - MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P)).coeff a| ≤ 1 / 2 := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_map, roundedIntegerPolynomial_coeff]
  exact abs_sub_round (P.coeff a)

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ R : Type*} {d : ℕ}

def slotPolynomialInput (t : σ → R) (b : Fin d → R) (i : Fin d) : σ ⊕ Fin i.val → R :=
  Sum.elim t (fun j => b (earlierSlot i j))

theorem slotPolynomialInput_update (t : σ → R) (b : Fin d → R) (i : Fin d) (c : R) :
    slotPolynomialInput t (Function.update b i c) i = slotPolynomialInput t b i := by
  funext v
  cases v with
  | inl a => rfl
  | inr j =>
      apply Function.update_of_ne
      intro h
      have hv := congrArg Fin.val h
      have hj := j.isLt
      simp only [earlierSlot] at hv
      omega

noncomputable def slotAddShearEquiv [AddCommGroup R] (i : Fin d)
    (f : (Fin d → R) → R) (hf : ∀ b c, f (Function.update b i c) = f b) :
    (Fin d → R) ≃ (Fin d → R) where
  toFun b := Function.update b i (b i + f b)
  invFun b := Function.update b i (b i - f b)
  left_inv b := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, hf, add_sub_cancel_right]
    · simp only [Function.update_of_ne h]
  right_inv b := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, hf, sub_add_cancel]
    · simp only [Function.update_of_ne h]

noncomputable def polynomialSlotShear [CommRing R] (t : σ → R) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) R) : (Fin d → R) ≃ (Fin d → R) :=
  slotAddShearEquiv i (fun b => MvPolynomial.eval (slotPolynomialInput t b i) Q)
    (fun b c => by rw [slotPolynomialInput_update])

theorem polynomialSlotShear_apply [CommRing R] (t : σ → R) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) R) (b : Fin d → R) :
    polynomialSlotShear t i Q b =
      Function.update b i (b i + MvPolynomial.eval (slotPolynomialInput t b i) Q) := rfl

theorem polynomialSlotShear_cast (t : σ → ℤ) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) ℤ) (b : Fin d → ℤ) :
    (fun j => (polynomialSlotShear t i Q b j : ℝ)) =
      polynomialSlotShear (fun a => (t a : ℝ)) i (MvPolynomial.map (Int.castRingHom ℝ) Q)
        (fun j => (b j : ℝ)) := by
  have hi : (fun a => ((slotPolynomialInput t b i a : ℤ) : ℝ)) =
      slotPolynomialInput (fun a => (t a : ℝ)) (fun j => (b j : ℝ)) i := by
    funext a
    cases a <;> rfl
  have heval := MvPolynomial.map_eval (Int.castRingHom ℝ) (slotPolynomialInput t b i) Q
  change ((MvPolynomial.eval (slotPolynomialInput t b i) Q : ℤ) : ℝ) = _ at heval
  simp only [Function.comp_def, Int.coe_castRingHom] at heval
  rw [hi] at heval
  funext j
  rw [polynomialSlotShear_apply, polynomialSlotShear_apply]
  by_cases h : j = i
  · subst j
    simp only [Function.update_self, Int.cast_add]
    rw [heval]
  · simp only [Function.update_of_ne h]

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem finsupp_weight_add_function (v w : σ → ℕ) (a : σ →₀ ℕ) :
    Finsupp.weight (v + w) a = Finsupp.weight v a + Finsupp.weight w a := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.add_apply, smul_add,
    Finset.sum_add_distrib]

theorem weightedSupportLE_of_weight_le {v w : σ → ℕ} (hvw : ∀ i, v i ≤ w i)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    p ∈ weightedSupportLE v d := by
  intro a ha
  change Finsupp.weight v a ≤ d
  apply le_trans _ (hp ha)
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (a i) (hvw i))

theorem weightedTopPart_preserves_degree (v w : σ → ℕ) (n : ℕ)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    weightedHomogeneousComponent v n p ∈ weightedSupportLE w d := by
  intro a ha
  change a ∈ (weightedHomogeneousComponent v n p).support at ha
  rw [support_weightedHomogeneousComponent] at ha
  exact hp (Finset.mem_filter.mp ha).1

theorem weightedTopPart_remainder_lt (w : σ → ℕ)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    p - weightedHomogeneousComponent w d p ∈ weightedSupportLT w d := by
  intro a ha
  change a ∈ (p - weightedHomogeneousComponent w d p).support at ha
  have hc := MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_sub, coeff_weightedHomogeneousComponent] at hc
  by_cases he : Finsupp.weight w a = d
  · exact (hc (by rw [ite_eq_left he, sub_self])).elim
  · have hpa : p.coeff a ≠ 0 := by simpa only [ite_eq_right he, sub_zero] using hc
    have hle : Finsupp.weight w a ≤ d := hp (MvPolynomial.mem_support_iff.mpr hpa)
    change Finsupp.weight w a < d
    omega

def patchSlotWeight {d : ℕ} (w : Fin d → ℕ) (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim (fun _ => 0) (fun j => w (earlierSlot i j))

def patchParameterWeight {d : ℕ} (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

theorem patchVariableWeight_split {d : ℕ} (w : Fin d → ℕ) (i : Fin d) :
    patchVariableWeight (σ := σ) w i = patchSlotWeight w i + patchParameterWeight i := by
  funext a
  cases a <;> simp [patchVariableWeight, patchSlotWeight, patchParameterWeight]

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

noncomputable def topPart (A : PolynomialSlots σ d w) : PolynomialSlots σ d w where
  center i := weightedHomogeneousComponent (patchSlotWeight w i) (w i) (A.center i)
  degree i := weightedTopPart_preserves_degree _ _ _ (A.degree i)

theorem topPart_homogeneous (A : PolynomialSlots σ d w) (i : Fin d) :
    ((A.topPart).center i).IsWeightedHomogeneous (patchSlotWeight w i) (w i) :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem sub_topPart_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.center i - A.topPart.center i ∈ weightedSupportLT (patchSlotWeight w i) (w i) := by
  apply weightedTopPart_remainder_lt
  apply weightedSupportLE_of_weight_le _ (A.degree i)
  intro a
  cases a <;> simp [patchSlotWeight, patchVariableWeight]

theorem topPart_parameter_exponent_zero (A : PolynomialSlots σ d w) (i : Fin d)
    (a : (σ ⊕ Fin i.val) →₀ ℕ) (ha : (A.topPart.center i).coeff a ≠ 0) (j : σ) :
    a (Sum.inl j) = 0 := by
  have hs : a ∈ (weightedHomogeneousComponent (patchSlotWeight w i) (w i)
      (A.center i)).support := MvPolynomial.mem_support_iff.mpr ha
  rw [support_weightedHomogeneousComponent] at hs
  obtain ⟨hA, htop⟩ := Finset.mem_filter.mp hs
  have hdegree : Finsupp.weight (patchVariableWeight w i) a ≤ w i := A.degree i hA
  rw [patchVariableWeight_split, finsupp_weight_add_function, htop] at hdegree
  have hzero : Finsupp.weight (patchParameterWeight i) a = 0 := by omega
  have hle := Finsupp.le_weight (patchParameterWeight (σ := σ) i)
    (s := Sum.inl j) (by decide : (1 : ℕ) ≠ 0) a
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

theorem topPart_slots_independent (A : PolynomialSlots σ d w) (t u : σ → ℝ) :
    A.topPart.slots t = A.topPart.slots u := by
  apply TriangularSlots.ext
  intro b i
  change aeval (Sum.elim t (fun j => b (earlierSlot i j))) (A.topPart.center i) =
    aeval (Sum.elim u (fun j => b (earlierSlot i j))) (A.topPart.center i)
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def]
  apply MvPolynomial.eval₂_congr
  intro v a hv ha
  cases v with
  | inl j => exact ((Finsupp.mem_support_iff.mp hv)
      (A.topPart_parameter_exponent_zero i a ha j)).elim
  | inr j => rfl

theorem topPart_coeff_bound (A : PolynomialSlots σ d w)
    (hA : ∀ i a, |(A.center i).coeff a| ≤ 1 / 2) (i : Fin d) (a) :
    |(A.topPart.center i).coeff a| ≤ 1 / 2 := by
  change |(weightedHomogeneousComponent (patchSlotWeight w i) (w i)
    (A.center i)).coeff a| ≤ 1 / 2
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact hA i a
  · norm_num

end PolynomialSlots

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ : Type*} {d : ℕ}

noncomputable def slotPrefixLift (k i : Fin d) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) :
    MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  aeval (PolynomialSlots.placementSubstitution id i k) R

theorem slotPrefixLift_degree (w : Fin d → ℕ) (k i : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    slotPrefixLift k i R ∈ weightedSupportLE (patchVariableWeight w i) (w k) :=
  weightedSupportLE_aeval _ _ _
    (PolynomialSlots.placementSubstitution_degree id (fun _ => rfl) i k) hR

theorem slotPrefixLift_eval (k i : Fin d) (hki : k.val ≤ i.val)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (t : σ → ℝ) (b : Fin d → ℝ) :
    aeval (slotPolynomialInput t b i) (slotPrefixLift k i R) =
      aeval (slotPolynomialInput t b k) R := by
  rw [slotPrefixLift, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f R)
  funext v
  cases v with
  | inl a => simp only [PolynomialSlots.placementSubstitution, Sum.elim_inl,
      aeval_X, slotPolynomialInput]
  | inr j =>
      have hj : (id (earlierSlot k j)).val < i.val := lt_of_lt_of_le j.isLt hki
      simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr, dite_eq_left hj,
        aeval_X, slotPolynomialInput]
      rfl

theorem slotPrefixLift_self (k : Fin d) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) :
    slotPrefixLift k k R = R := by
  have hsub : PolynomialSlots.placementSubstitution (σ := σ) id k k = X := by
    funext v
    cases v with
    | inl a => rfl
    | inr j =>
        have hj : (id (earlierSlot k j)).val < k.val := j.isLt
        simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr, dite_eq_left hj]
        rfl
  rw [slotPrefixLift, hsub, MvPolynomial.aeval_X_left_apply]

noncomputable def slotShearSubstitution (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a)) (fun j =>
    X (Sum.inr j) + if earlierSlot i j = k then slotPrefixLift k i R else 0)

theorem slotShearSubstitution_degree (w : Fin d → ℕ) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k))
    (i : Fin d) (v : σ ⊕ Fin i.val) :
    slotShearSubstitution k R i v ∈
      weightedSupportLE (patchVariableWeight w i) (patchVariableWeight w i v) := by
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      change X (Sum.inr j) + (if earlierSlot i j = k then slotPrefixLift k i R else 0) ∈
        weightedSupportLE (patchVariableWeight w i) (w (earlierSlot i j))
      apply (weightedSupportLE _ _).add_mem (weightedSupportLE_X _ (Sum.inr j))
      by_cases h : earlierSlot i j = k
      · rw [ite_eq_left h]
        simpa only [patchVariableWeight, Sum.elim_inr, h] using slotPrefixLift_degree w k i R hR
      · rw [ite_eq_right h]
        exact Submodule.zero_mem _

theorem slotShearSubstitution_before (k i : Fin d) (hik : i.val ≤ k.val)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) : slotShearSubstitution k R i = X := by
  funext v
  cases v with
  | inl a => rfl
  | inr j =>
      have h : earlierSlot i j ≠ k := by
        intro h
        have hv := congrArg Fin.val h
        have hj := j.isLt
        simp only [earlierSlot] at hv
        omega
      simp only [slotShearSubstitution, Sum.elim_inr, ite_eq_right h, add_zero]

theorem slotShearSubstitution_eval (k i : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (t : σ → ℝ) (b : Fin d → ℝ)
    (v : σ ⊕ Fin i.val) :
    aeval (slotPolynomialInput t b i) (slotShearSubstitution k R i v) =
      slotPolynomialInput t (polynomialSlotShear t k R b) i v := by
  cases v with
  | inl a => simp only [slotShearSubstitution, Sum.elim_inl, aeval_X, slotPolynomialInput]
  | inr j =>
      by_cases h : earlierSlot i j = k
      · have hki : k.val ≤ i.val := by
          have hj : (earlierSlot i j).val < i.val := j.isLt
          rw [h] at hj
          exact hj.le
        change aeval (slotPolynomialInput t b i)
          (X (Sum.inr j) + if earlierSlot i j = k then slotPrefixLift k i R else 0) = _
        rw [ite_eq_left h, map_add, aeval_X, slotPrefixLift_eval k i hki]
        simp only [slotPolynomialInput, Sum.elim_inr, polynomialSlotShear_apply,
          h, Function.update_self, MvPolynomial.aeval_eq_eval]
      · simp only [slotShearSubstitution, Sum.elim_inr, ite_eq_right h, add_zero,
          aeval_X, slotPolynomialInput, polynomialSlotShear_apply, Function.update_of_ne h]

end Erdos3


namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shear (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    PolynomialSlots σ d w where
  center i := aeval (slotShearSubstitution k R i) (A.center i) -
    if i = k then slotPrefixLift k i R else 0
  degree i := by
    apply (weightedSupportLE _ _).sub_mem
    · exact weightedSupportLE_aeval _ _ _ (slotShearSubstitution_degree w k R hR i)
        (A.degree i)
    · by_cases h : i = k
      · subst i
        rw [ite_eq_left rfl]
        exact slotPrefixLift_degree w k k R hR
      · rw [ite_eq_right h]
        exact Submodule.zero_mem _

theorem shear_center_before (A : PolynomialSlots σ d w) (k i : Fin d)
    (hik : i.val < k.val) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    (A.shear k R hR).center i = A.center i := by
  have hne : i ≠ k := by intro h; subst i; exact (lt_irrefl _ hik)
  change aeval (slotShearSubstitution k R i) (A.center i) -
    (if i = k then slotPrefixLift k i R else 0) = _
  rw [slotShearSubstitution_before k i hik.le, MvPolynomial.aeval_X_left_apply,
    ite_eq_right hne, sub_zero]

theorem shear_center_self (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    (A.shear k R hR).center k = A.center k - R := by
  change aeval (slotShearSubstitution k R k) (A.center k) -
    (if k = k then slotPrefixLift k k R else 0) = _
  rw [slotShearSubstitution_before k k le_rfl, MvPolynomial.aeval_X_left_apply,
    ite_eq_left rfl, slotPrefixLift_self]

theorem shear_center_eval (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k))
    (t : σ → ℝ) (b : Fin d → ℝ) (i : Fin d) :
    ((A.shear k R hR).slots t).center b i =
      (A.slots t).center (polynomialSlotShear t k R b) i -
        if i = k then MvPolynomial.eval (slotPolynomialInput t b k) R else 0 := by
  change aeval (slotPolynomialInput t b i)
      (aeval (slotShearSubstitution k R i) (A.center i) -
        if i = k then slotPrefixLift k i R else 0) = _
  rw [map_sub, MvPolynomial.comp_aeval_apply]
  have he : (fun v => aeval (slotPolynomialInput t b i) (slotShearSubstitution k R i v)) =
      slotPolynomialInput t (polynomialSlotShear t k R b) i :=
    funext (slotShearSubstitution_eval k i R t b)
  rw [he]
  congr 1
  by_cases h : i = k
  · subst i
    rw [ite_eq_left rfl, ite_eq_left rfl, slotPrefixLift_self, MvPolynomial.aeval_eq_eval]
  · rw [ite_eq_right h, ite_eq_right h, map_zero]

theorem shear_integer_residual (A : PolynomialSlots σ d w) (k : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin k.val) ℤ)
    (hQ : MvPolynomial.map (Int.castRingHom ℝ) Q ∈
      weightedSupportLE (patchVariableWeight w k) (w k))
    (t : σ → ℤ) (b : Fin d → ℤ) :
    ((A.shear k (MvPolynomial.map (Int.castRingHom ℝ) Q) hQ).slots
      (fun a => (t a : ℝ))).residual b =
    (A.slots (fun a => (t a : ℝ))).residual (polynomialSlotShear t k Q b) := by
  funext i
  change (b i : ℝ) - _ = (polynomialSlotShear t k Q b i : ℝ) - _
  rw [shear_center_eval]
  have he := polynomialSlotShear_cast t k Q b
  rw [← he]
  have hi := congrFun he i
  rw [polynomialSlotShear_apply (R := ℝ)] at hi
  by_cases h : i = k
  · subst i
    simp only [Function.update_self, ite_true] at hi ⊢
    linarith
  · simp only [Function.update_of_ne h, ite_eq_right h, sub_zero] at hi ⊢
    rw [hi]

end PolynomialSlots

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R] {d : ℕ}

noncomputable def slotPolynomialLift (i : Fin d) (P : MvPolynomial (σ ⊕ Fin i.val) R) :
    MvPolynomial (σ ⊕ Fin d) R := rename (Sum.map id (earlierSlot i)) P

theorem slotPolynomialLift_degree (v : σ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    {P : MvPolynomial (σ ⊕ Fin i.val) R} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim v (fun j => w (earlierSlot i j))) n) :
    slotPolynomialLift i P ∈ weightedSupportLE (Sum.elim v w) n := by
  apply polynomialHom_preserves_weightedDegree _ _ (rename (Sum.map id (earlierSlot i))) _ hP
  intro a
  rw [rename_X]
  cases a with
  | inl j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl j)
  | inr j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inr (earlierSlot i j))

theorem slotPolynomialLift_lower (v : σ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    {P : MvPolynomial (σ ⊕ Fin i.val) R} {n : ℕ}
    (hP : P ∈ weightedSupportLT (Sum.elim v (fun j => w (earlierSlot i j))) n) :
    slotPolynomialLift i P ∈ weightedSupportLT (Sum.elim v w) n := by
  apply weightedSupportLT_map _ _ (rename (Sum.map id (earlierSlot i))) _ hP
  intro a
  rw [rename_X]
  cases a with
  | inl j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl j)
  | inr j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inr (earlierSlot i j))

theorem slotPolynomialLift_eval (i : Fin d) (P : MvPolynomial (σ ⊕ Fin i.val) R)
    (t : σ → R) (b : Fin d → R) :
    aeval (Sum.elim t b) (slotPolynomialLift i P) = aeval (slotPolynomialInput t b i) P := by
  rw [slotPolynomialLift, MvPolynomial.aeval_rename]
  apply congrArg (fun f => aeval f P)
  funext a
  cases a <;> rfl

namespace PolynomialSlots

variable {w : Fin d → ℕ}

noncomputable def specializeCenter (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    MvPolynomial (Fin i.val) ℝ := aeval (Sum.elim (fun a => C (t a)) X) (A.center i)

theorem specializeCenter_degree (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    A.specializeCenter t i ∈ weightedSupportLE (fun j => w (earlierSlot i j)) (w i) := by
  apply weightedSupportLE_aeval _ _ _ _ (A.degree i)
  intro a
  cases a with
  | inl j => exact weightedSupportLE_C _ 1 (t j)
  | inr j => exact weightedSupportLE_X _ j

theorem specializeCenter_full_degree (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    rename (earlierSlot i) (A.specializeCenter t i) ∈ weightedSupportLE w (w i) := by
  apply polynomialHom_preserves_weightedDegree _ _ (rename (earlierSlot i)) _
    (A.specializeCenter_degree t i)
  intro j
  rw [rename_X]
  exact weightedSupportLE_X w (earlierSlot i j)

theorem topPart_aeval_independent {S : Type*} [CommRing S] [Algebra ℝ S]
    (A : PolynomialSlots σ d w) (i : Fin d) (t u : σ → S) (b : Fin i.val → S) :
    aeval (Sum.elim t b) (A.topPart.center i) =
      aeval (Sum.elim u b) (A.topPart.center i) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def]
  apply MvPolynomial.eval₂_congr
  intro v a hv ha
  cases v with
  | inl j => exact ((Finsupp.mem_support_iff.mp hv)
      (A.topPart_parameter_exponent_zero i a ha j)).elim
  | inr j => rfl

theorem topPart_lift_specialize (A : PolynomialSlots σ d w) (i : Fin d) :
    slotPolynomialLift i (A.topPart.center i) =
      rename Sum.inr (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) := by
  let b : Fin i.val → MvPolynomial (σ ⊕ Fin d) ℝ := fun j => X (Sum.inr (earlierSlot i j))
  have hcomp : (rename (R := ℝ) (Sum.inr : Fin d → σ ⊕ Fin d)).comp
      ((rename (earlierSlot i)).comp (aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X))) =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (σ ⊕ Fin d) ℝ)) b) := by
    apply MvPolynomial.algHom_ext
    intro a
    cases a <;> simp [b]
  have he := congrArg (fun F : MvPolynomial (σ ⊕ Fin i.val) ℝ →ₐ[ℝ]
      MvPolynomial (σ ⊕ Fin d) ℝ => F (A.topPart.center i)) hcomp
  simp only [AlgHom.comp_apply] at he
  have hs : A.topPart.specializeCenter 0 i =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X) (A.topPart.center i) := by
    simp only [specializeCenter, Pi.zero_apply, map_zero]
  rw [hs, he, slotPolynomialLift, MvPolynomial.rename_eq_aeval]
  have hinput : (X : σ ⊕ Fin d → MvPolynomial (σ ⊕ Fin d) ℝ) ∘
      Sum.map id (earlierSlot i) = Sum.elim (fun a => X (Sum.inl a)) b := by
    funext a
    cases a <;> rfl
  rw [hinput]
  exact A.topPart_aeval_independent i _ _ b

end PolynomialSlots

end Erdos3


namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem exists_coefficient_normalized_prefix (A : PolynomialSlots σ d w) (n : ℕ) :
    n ≤ d → ∃ B : PolynomialSlots σ d w,
      (∀ i : Fin d, i.val < n → ∀ a, |(B.center i).coeff a| ≤ 1 / 2) ∧
      ∀ t : σ → ℤ, ∃ e : (Fin d → ℤ) ≃ (Fin d → ℤ),
        ∀ b, (B.slots (fun a => (t a : ℝ))).residual b =
          (A.slots (fun a => (t a : ℝ))).residual (e b) := by
  induction n with
  | zero =>
      intro _
      refine ⟨A, ?_, ?_⟩
      · intro i hi
        exact (Nat.not_lt_zero _ hi).elim
      · intro t
        exact ⟨Equiv.refl _, fun _ => rfl⟩
  | succ n ih =>
      intro hn
      obtain ⟨B, hB, hBA⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let Q := roundedIntegerPolynomial (B.center k)
      have hQ : MvPolynomial.map (Int.castRingHom ℝ) Q ∈
          weightedSupportLE (patchVariableWeight w k) (w k) :=
        roundedIntegerPolynomial_real_degree (B.center k) _ _ (B.degree k)
      refine ⟨B.shear k (MvPolynomial.map (Int.castRingHom ℝ) Q) hQ, ?_, ?_⟩
      · intro i hi a
        by_cases hik : i = k
        · subst i
          rw [shear_center_self]
          exact roundedIntegerPolynomial_remainder_bound (B.center k) a
        · have hine : i.val ≠ n := by
            intro he
            apply hik
            exact Fin.ext he
          have hil : i.val < n := by omega
          rw [shear_center_before B k i hil]
          exact hB i hil a
      · intro t
        obtain ⟨e, he⟩ := hBA t
        refine ⟨(polynomialSlotShear t k Q).trans e, ?_⟩
        intro b
        rw [shear_integer_residual]
        exact he _

theorem exists_coefficient_normalized (A : PolynomialSlots σ d w) :
    ∃ B : PolynomialSlots σ d w,
      (∀ i a, |(B.center i).coeff a| ≤ 1 / 2) ∧
      ∀ t : σ → ℤ, ∃ e : (Fin d → ℤ) ≃ (Fin d → ℤ),
        ∀ b, (B.slots (fun a => (t a : ℝ))).residual b =
          (A.slots (fun a => (t a : ℝ))).residual (e b) := by
  obtain ⟨B, hB, hBA⟩ := A.exists_coefficient_normalized_prefix d le_rfl
  exact ⟨B, fun i => hB i i.isLt, hBA⟩

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem exists_coefficient_normalized (A : PolynomialPatch σ s d) :
    ∃ B : PolynomialPatch σ s d, B.weight = A.weight ∧ B.kernel = A.kernel ∧
      (∀ i a, |(B.form.center i).coeff a| ≤ 1 / 2) ∧
      ∀ t : σ → ℤ, B.value (fun a => (t a : ℝ)) = A.value (fun a => (t a : ℝ)) := by
  obtain ⟨B, hB, hBA⟩ := A.form.exists_coefficient_normalized
  refine ⟨{ A with form := B }, rfl, rfl, hB, ?_⟩
  intro t
  obtain ⟨e, he⟩ := hBA t
  change (∑' b, A.kernel.value ((B.slots (fun a => (t a : ℝ))).residual b)) = _
  simp_rw [he]
  exact e.tsum_eq (fun b => A.kernel.value ((A.form.slots (fun a => (t a : ℝ))).residual b))

end PolynomialPatch

end Erdos3

end OAI
