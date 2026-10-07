/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Estimates.WeightedLoweringTriangular
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearWeightedOrbitCoordinates

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialMass_weightedComponent_le (w : σ → ℕ) (n : ℕ) (P : MvPolynomial σ ℝ) :
    realPolynomialMass (weightedHomogeneousComponent w n P) ≤ realPolynomialMass P := by
  classical
  unfold realPolynomialMass
  rw [support_weightedHomogeneousComponent]
  calc
    _ = ∑ α ∈ P.support.filter (fun α => Finsupp.weight w α = n), |P.coeff α| := by
      apply Finset.sum_congr rfl
      intro α hα
      rw [coeff_weightedHomogeneousComponent, ite_eq_left (Finset.mem_filter.mp hα).2]
    _ ≤ ∑ α ∈ P.support, |P.coeff α| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)

theorem realPolynomialMass_zeroParameterEval_le (P : MvPolynomial (σ ⊕ τ) ℝ) :
    realPolynomialMass (aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial τ ℝ)) X) P) ≤
      realPolynomialMass P := by
  have h := realPolynomialMass_substitution_le P
    (Sum.elim (fun _ : σ => (0 : MvPolynomial τ ℝ)) X) (M := 1) le_rfl (by
      intro a
      cases a with
      | inl i => simpa only [Sum.elim_inl, realPolynomialMass_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      | inr i => simp only [Sum.elim_inr, realPolynomialMass_X, le_refl]) le_rfl
  rw [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
  simpa only [one_pow, mul_one, MvPolynomial.coe_eval₂Hom] using h

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

theorem topPart_specializeCenter_mass_le (A : PolynomialSlots σ d w) (i : Fin d) :
    realPolynomialMass (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) ≤
      realPolynomialMass (A.center i) := by
  apply (realPolynomialMass_rename_le _ _).trans
  have hs : A.topPart.specializeCenter 0 i =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X) (A.topPart.center i) := by
    simp only [specializeCenter, Pi.zero_apply, map_zero]
  rw [hs]
  exact (realPolynomialMass_zeroParameterEval_le _).trans
    (realPolynomialMass_weightedComponent_le _ _ _)

theorem center_mass_le_of_normalized [Fintype σ] (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (hA : ∀ i α, |(A.center i).coeff α| ≤ 1 / 2) (i : Fin d) :
    realPolynomialMass (A.center i) ≤ ((s + 1) * (Fintype.card σ + d + 1) ^ s : ℕ) := by
  have hdegree : (A.center i).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport (patchVariableWeight w i) (by
      intro a
      cases a with
      | inl j => exact le_rfl
      | inr j => exact hpos (earlierSlot i j)) (A.degree i)).trans (hw i)
  have hmass : realPolynomialMass (A.center i) ≤ ((A.center i).support.card : ℝ) := by
    unfold realPolynomialMass
    calc
      _ ≤ ∑ _α ∈ (A.center i).support, (1 : ℝ) :=
        Finset.sum_le_sum (fun α _ => (hA i α).trans (by norm_num))
      _ = _ := by simp
  apply hmass.trans
  have hcard := polynomial_support_card_le (A.center i) hdegree
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  exact_mod_cast hcard.trans (Nat.mul_le_mul_left (s + 1)
    (Nat.pow_le_pow_left (by omega : Fintype.card σ + i.val + 1 ≤ Fintype.card σ + d + 1) s))

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearTransformedSlots (A : PolynomialSlots σ d w)
    (hw : Monotone w) (e : WeightedLoweringAut w ℝ) : TriangularSlots d where
  center x i := x i - aeval (polynomialSubstitutionPoint e.val.toAlgHom x)
    (A.topResidualEquiv (X i))
  lower i x y hxy := by
    have hd := weightedLoweringSubstitution_difference e hw i x y hxy
    have htop :
        aeval (polynomialSubstitutionPoint e.val.toAlgHom x)
            (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) =
        aeval (polynomialSubstitutionPoint e.val.toAlgHom y)
            (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) := by
      rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
      apply congrArg (fun f : Fin i.val → ℝ => aeval f (A.topPart.specializeCenter 0 i))
      funext j
      exact weightedLoweringSubstitution_prefix e hw i x y hxy (earlierSlot i j) j.isLt
    rw [A.topResidualEquiv_X, map_sub, map_sub, aeval_X, aeval_X, htop]
    linarith

theorem shearTransformedSlots_residual (A : PolynomialSlots σ d w)
    (hw : Monotone w) (e : WeightedLoweringAut w ℝ) (b : Fin d → ℤ) :
    (A.shearTransformedSlots hw e).residual b =
      fun i => aeval (polynomialSubstitutionPoint e.val.toAlgHom (fun j => (b j : ℝ)))
        (A.topResidualEquiv (X i)) := by
  funext i
  change (b i : ℝ) - ((b i : ℝ) - _) = _
  ring

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearSummand_eq_residual (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group) (b : Fin d → ℤ) :
    A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g (fun i => (b i : ℝ))) =
      A.kernel.value ((A.form.shearTransformedSlots A.weight_mono
        (polynomialShearRealAutEquiv A.weight s A.weight_le g)⁻¹).residual b) := by
  rw [PolynomialSlots.shearTransformedSlots_residual]
  rfl

theorem shearSummand_unique (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    {b c : Fin d → ℤ}
    (hb : A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g
      (fun i => (b i : ℝ))) ≠ 0)
    (hc : A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g
      (fun i => (c i : ℝ))) ≠ 0) : b = c := by
  rw [A.shearSummand_eq_residual] at hb hc
  exact TriangularSlots.contributing_unique _ A.kernel hb hc

theorem shearOrbitSum_eq_patchValue (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group) :
    polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel g =
      (A.form.shearTransformedSlots A.weight_mono
        (polynomialShearRealAutEquiv A.weight s A.weight_le g)⁻¹).patchValue A.kernel := by
  unfold polynomialShearOrbitSum TriangularSlots.patchValue
  exact tsum_congr (A.shearSummand_eq_residual g)

theorem shearObservable_mem_Icc (A : PolynomialPatch σ s d)
    (x : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) : A.shearObservable x ∈ Set.Icc (0 : ℝ) 1 := by
  refine Quotient.inductionOn x ?_
  intro g
  change polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel g ∈ Set.Icc (0 : ℝ) 1
  rw [A.shearOrbitSum_eq_patchValue]
  exact TriangularSlots.patchValue_mem_Icc _ A.kernel

theorem abs_shearObservable_le_one (A : PolynomialPatch σ s d)
    (x : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) : |A.shearObservable x| ≤ 1 := by
  rw [abs_of_nonneg (A.shearObservable_mem_Icc x).1]
  exact (A.shearObservable_mem_Icc x).2

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open MvPolynomial

variable {σ τ : Type*} {s d : ℕ}

noncomputable def symbolicShearPrefixSubstitution (i : Fin d) :
    τ ⊕ Fin d → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (fun j => if h : j.val < i.val then X (Sum.inr ⟨j.val, h⟩) else 0)

theorem symbolicShearPrefixSubstitution_degree (w : Fin d → ℕ) (i : Fin d)
    (v : τ ⊕ Fin d) :
    symbolicShearPrefixSubstitution i v ∈
      weightedSupportLE (patchVariableWeight w i) (Sum.elim (fun _ : τ => 1) w v) := by
  classical
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr]
      split_ifs with h
      · have hj : earlierSlot i ⟨j.val, h⟩ = j := Fin.ext rfl
        have hx := weightedSupportLE_X (R := ℝ)
          (patchVariableWeight (σ := τ) w i) (Sum.inr ⟨j.val, h⟩)
        change _ ∈ weightedSupportLE _ (w (earlierSlot i ⟨j.val, h⟩)) at hx
        rw [hj] at hx
        exact hx
      · exact Submodule.zero_mem _

namespace PolynomialPatch

variable (A : PolynomialPatch σ s d)
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)

noncomputable def symbolicShearFullCenter (i : Fin d) : MvPolynomial (τ ⊕ Fin d) ℝ :=
  X (Sum.inr i) - f (rename Sum.inr (A.form.topResidualEquiv (X i)))

variable
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n)

include hdegree in
theorem symbolicShearFullCenter_degree (i : Fin d) :
    A.symbolicShearFullCenter f i ∈
      weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) (A.weight i) := by
  apply (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
  apply hdegree
  apply polynomialHom_preserves_weightedDegree A.weight _ (rename Sum.inr) _
    (A.form.topResidualEquiv_degree (weightedSupportLE_X A.weight i))
  intro j
  rw [rename_X]
  exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def symbolicShearForm : PolynomialSlots τ d A.weight where
  center i := aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)
  degree i := weightedSupportLE_aeval _ _ _
    (symbolicShearPrefixSubstitution_degree A.weight i)
    (A.symbolicShearFullCenter_degree f hdegree i)

noncomputable def symbolicShearPatch : PolynomialPatch τ s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.symbolicShearForm f hdegree
  kernel := A.kernel

variable (e : (τ → ℝ) → WeightedLoweringAut A.weight ℝ)
  (hspecialize : ∀ t P, patchParameterSpecialization t (f P) =
    (e t).val (patchParameterSpecialization t P))

include hspecialize in
theorem symbolicShearFullCenter_eval (t : τ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    aeval (Sum.elim t x) (A.symbolicShearFullCenter f i) =
      (A.form.shearTransformedSlots A.weight_mono (e t)).center x i := by
  rw [symbolicShearFullCenter, map_sub, aeval_X]
  change x i - _ = x i - _
  congr 1
  rw [← patchParameterSpecialization_eval, hspecialize]
  have hsp : patchParameterSpecialization t
      (rename Sum.inr (A.form.topResidualEquiv (X i))) = A.form.topResidualEquiv (X i) := by
    rw [patchParameterSpecialization, MvPolynomial.aeval_rename]
    exact MvPolynomial.aeval_X_left_apply _
  rw [hsp]
  exact (polynomialSubstitutionPoint_aeval (e t).val.toAlgHom x
    (A.form.topResidualEquiv (X i))).symm

include hspecialize in
theorem symbolicShearForm_slots (t : τ → ℝ) :
    (A.symbolicShearForm f hdegree).slots t =
      A.form.shearTransformedSlots A.weight_mono (e t) := by
  classical
  apply TriangularSlots.ext
  intro x i
  let y : Fin d → ℝ := fun j => if j.val < i.val then x j else 0
  have hy : ∀ j : Fin d, j < i → y j = x j := by
    intro j hj
    exact ite_eq_left hj
  have heval :
      (fun v => aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (symbolicShearPrefixSubstitution i v)) = Sum.elim t y := by
    funext v
    cases v with
    | inl a => simp [symbolicShearPrefixSubstitution]
    | inr j =>
        dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr, y]
        split_ifs with h
        · exact aeval_X _ _
        · exact map_zero _
  change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
    (aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)) = _
  rw [MvPolynomial.comp_aeval_apply, heval,
    A.symbolicShearFullCenter_eval f e hspecialize]
  exact (A.form.shearTransformedSlots A.weight_mono (e t)).lower i y x hy

include hspecialize in
theorem symbolicShearPatch_value (t : τ → ℝ) :
    (A.symbolicShearPatch f hdegree).value t =
      ∑' b : Fin d → ℤ, A.kernel.value
        (fun i => aeval (polynomialSubstitutionPoint (e t).val.toAlgHom
          (fun j => (b j : ℝ))) (A.form.topResidualEquiv (X i))) := by
  change ((A.symbolicShearForm f hdegree).slots t).patchValue A.kernel = _
  rw [A.symbolicShearForm_slots f hdegree e hspecialize]
  simp only [TriangularSlots.patchValue, PolynomialSlots.shearTransformedSlots_residual]

include hspecialize in
theorem symbolicShearPatch_value_eq_observable
    (g : (τ → ℝ) → (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (he : ∀ t, e t = (polynomialShearRealAutEquiv A.weight s A.weight_le (g t))⁻¹)
    (t : τ → ℝ) :
    (A.symbolicShearPatch f hdegree).value t =
      A.shearObservable (QuotientGroup.mk (g t)) := by
  rw [A.symbolicShearPatch_value f hdegree e hspecialize]
  unfold shearObservable polynomialShearQuotientSum
  change _ = polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel (g t)
  rw [he t]
  rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualEquiv_X_mass (A : PolynomialSlots σ d w)
    {M : ℝ} (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) (i : Fin d) :
    realPolynomialMass (A.topResidualEquiv (X i)) ≤ 1 + M := by
  rw [A.topResidualEquiv_X]
  exact (realPolynomialMass_sub_le _ _).trans
    (by simpa only [realPolynomialMass_X] using
      add_le_add (le_refl (1 : ℝ)) ((A.topPart_specializeCenter_mass_le i).trans (hA i)))

theorem topResidualEquiv_inverse_mass (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    {n : ℕ} {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass (A.topResidualEquiv.symm P) ≤ realPolynomialMass P * (1 + M) ^ (n * d) := by
  apply triangularPolynomialEquiv_inverse_mass w hpos _ A.topResidualShift_degree hM _ hP
  intro i
  rw [map_neg, realPolynomialMass_neg]
  exact (A.topPart_specializeCenter_mass_le i).trans (hA i)

theorem topResidualEquiv_inverse_X_mass (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) (i : Fin d) :
    realPolynomialMass (A.topResidualEquiv.symm (X i)) ≤ (1 + M) ^ (s * d) := by
  have h := A.topResidualEquiv_inverse_mass hpos hM hA (weightedSupportLE_X w i)
  rw [realPolynomialMass_X, one_mul] at h
  exact h.trans (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right d (hw i)))

theorem topResidualEquiv_inverse_eval_bound (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (y : Fin d → ℝ) (hy : ∀ i, |y i| ≤ 1) (i : Fin d) :
    |aeval y (A.topResidualEquiv.symm (X i))| ≤ (1 + M) ^ (s * d) :=
  (mvPolynomial_eval_abs_le_sum_coeff (A.topResidualEquiv.symm (X i)) y hy).trans
    (A.topResidualEquiv_inverse_X_mass hpos s hw hM hA i)

theorem topResidualPoint_preimage_bound (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (x : Fin d → ℝ) (hx : ∀ i, |aeval x (A.topResidualEquiv (X i))| ≤ 1) (i : Fin d) :
    |x i| ≤ (1 + M) ^ (s * d) := by
  have hinv : aeval (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom x)
      (A.topResidualEquiv.symm (X i)) = x i := by
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (A.topResidualEquiv (A.topResidualEquiv.symm (X i))) = x i
    rw [AlgEquiv.apply_symm_apply, aeval_X]
  rw [← hinv]
  exact A.topResidualEquiv_inverse_eval_bound hpos s hw hM hA _ hx i

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearKernel_support_bound (A : PolynomialPatch σ s d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    (x : Fin d → ℝ) (hx : A.shearKernel x ≠ 0) (i : Fin d) :
    |x i| ≤ (1 + M) ^ (s * d) := by
  apply A.form.topResidualPoint_preimage_bound A.weight_pos s A.weight_le hM hA x _ i
  intro j
  have h := A.kernel.support _ hx j
  exact h.trans (by norm_num)

theorem normalized_shearKernel_support_bound [Fintype σ] (A : PolynomialPatch σ s d)
    (hA : ∀ i α, |(A.form.center i).coeff α| ≤ 1 / 2)
    (x : Fin d → ℝ) (hx : A.shearKernel x ≠ 0) (i : Fin d) :
    |x i| ≤ (1 + (((s + 1) * (Fintype.card σ + d + 1) ^ s : ℕ) : ℝ)) ^ (s * d) := by
  apply A.shearKernel_support_bound (by positivity) _ x hx i
  exact A.form.center_mass_le_of_normalized A.weight_pos s A.weight_le hA

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ τ : Type*} {s d : ℕ}

theorem symbolicShearPrefixSubstitution_slot_degree (w : Fin d → ℕ) (i : Fin d)
    (v : τ ⊕ Fin d) :
    symbolicShearPrefixSubstitution i v ∈
      weightedSupportLE (patchSlotWeight w i) (Sum.elim (fun _ : τ => 0) w v) := by
  classical
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr]
      split_ifs with h
      · have hj : earlierSlot i ⟨j.val, h⟩ = j := Fin.ext rfl
        have hx := weightedSupportLE_X (R := ℝ)
          (patchSlotWeight (σ := τ) w i) (Sum.inr ⟨j.val, h⟩)
        change _ ∈ weightedSupportLE _ (w (earlierSlot i ⟨j.val, h⟩)) at hx
        rw [hj] at hx
        exact hx
      · exact Submodule.zero_mem _

namespace PolynomialPatch

variable (A : PolynomialPatch σ s d)

noncomputable def symbolicShearTopCenter (i : Fin d) : MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  aeval (Sum.elim (fun _ : σ => 0) (fun j => X (Sum.inr j))) (A.form.topPart.center i)

theorem symbolicShearTopCenter_eq (i : Fin d) :
    A.symbolicShearTopCenter (τ := τ) i =
      rename Sum.inr (A.form.topPart.specializeCenter 0 i) := by
  unfold symbolicShearTopCenter PolynomialSlots.specializeCenter
  rw [MvPolynomial.rename_eq_aeval, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun v => aeval v (A.form.topPart.center i))
  funext v
  cases v <;> simp

theorem symbolicShearTopCenter_homogeneous (i : Fin d) :
    (A.symbolicShearTopCenter (τ := τ) i).IsWeightedHomogeneous
      (patchSlotWeight A.weight i) (A.weight i) := by
  apply isWeightedHomogeneous_algHom (patchSlotWeight A.weight i)
    (patchSlotWeight A.weight i) _ _ (A.form.topPart_homogeneous i)
  intro v
  rw [aeval_X]
  cases v with
  | inl a => exact isWeightedHomogeneous_zero ℝ _ _
  | inr j => exact isWeightedHomogeneous_X ℝ _ (Sum.inr j)

theorem symbolicShearPrefix_topResidual (i : Fin d) :
    aeval (symbolicShearPrefixSubstitution (τ := τ) i)
      (X (Sum.inr i) - rename Sum.inr (A.form.topResidualEquiv (X i))) =
      A.symbolicShearTopCenter i := by
  classical
  simp only [PolynomialSlots.topResidualEquiv_X, map_sub, rename_X, sub_sub_cancel]
  rw [A.symbolicShearTopCenter_eq]
  rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename,
    MvPolynomial.rename_eq_aeval]
  apply congrArg (fun v => aeval v (A.form.topPart.specializeCenter 0 i))
  funext j
  simp only [Function.comp_apply, symbolicShearPrefixSubstitution, Sum.elim_inr,
    earlierSlot, dite_eq_left j.isLt]

variable
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n)
  (hlower : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 0) A.weight) n →
    f P - P ∈ weightedSupportLT (Sum.elim (fun _ : τ => 0) A.weight) n)

include hlower in
theorem symbolicShearForm_center_sub_top_lower (i : Fin d) :
    (A.symbolicShearForm f hdegree).center i - A.symbolicShearTopCenter i ∈
      weightedSupportLT (patchSlotWeight A.weight i) (A.weight i) := by
  have hP : rename (Sum.inr : Fin d → τ ⊕ Fin d) (A.form.topResidualEquiv (X i)) ∈
      weightedSupportLE (Sum.elim (fun _ : τ => 0) A.weight) (A.weight i) := by
    apply polynomialHom_preserves_weightedDegree A.weight _ (rename Sum.inr) _
      (A.form.topResidualEquiv_degree (weightedSupportLE_X A.weight i))
    intro j
    rw [rename_X]
    exact weightedSupportLE_X _ (Sum.inr j)
  have hh := (weightedSupportLT _ _).neg_mem (hlower hP)
  have he : A.symbolicShearFullCenter f i -
      (X (Sum.inr i) - rename Sum.inr (A.form.topResidualEquiv (X i))) =
      -(f (rename Sum.inr (A.form.topResidualEquiv (X i))) -
        rename Sum.inr (A.form.topResidualEquiv (X i))) := by
    unfold symbolicShearFullCenter
    abel
  rw [← he] at hh
  have h := weightedSupportLT_map (Sum.elim (fun _ : τ => 0) A.weight)
    (patchSlotWeight A.weight i) (aeval (symbolicShearPrefixSubstitution i))
    (fun v => by
      rw [aeval_X]
      exact symbolicShearPrefixSubstitution_slot_degree A.weight i v) hh
  rw [map_sub, A.symbolicShearPrefix_topResidual] at h
  exact h

include hlower in
theorem symbolicShearForm_topPart_center (i : Fin d) :
    (A.symbolicShearForm f hdegree).topPart.center i = A.symbolicShearTopCenter i := by
  exact weightedHomogeneousComponent_eq_of_sub_lower
    (patchSlotWeight A.weight i)
    (A.symbolicShearForm_center_sub_top_lower f hdegree hlower i)
    (A.symbolicShearTopCenter_homogeneous i)

include hlower in
theorem symbolicShearForm_topPart_specializeCenter (i : Fin d) :
    (A.symbolicShearForm f hdegree).topPart.specializeCenter 0 i =
      A.form.topPart.specializeCenter 0 i := by
  unfold PolynomialSlots.specializeCenter
  rw [A.symbolicShearForm_topPart_center f hdegree hlower,
    A.symbolicShearTopCenter_eq, MvPolynomial.aeval_rename]
  exact MvPolynomial.aeval_X_left_apply _

include hlower in
theorem symbolicShearForm_topResidualEquiv :
    (A.symbolicShearForm f hdegree).topResidualEquiv = A.form.topResidualEquiv := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  change (A.symbolicShearForm f hdegree).topResidualEquiv (X i) =
    A.form.topResidualEquiv (X i)
  rw [PolynomialSlots.topResidualEquiv_X, PolynomialSlots.topResidualEquiv_X,
    A.symbolicShearForm_topPart_specializeCenter f hdegree hlower]

variable (e : (τ → ℝ) → WeightedLoweringAut A.weight ℝ)
  (hspecialize : ∀ t P, patchParameterSpecialization t (f P) =
    (e t).val (patchParameterSpecialization t P))

include hspecialize in
theorem symbolicShearForm_specialized_residualHom (t : τ → ℝ) :
    (patchParameterSpecialization t).comp (A.symbolicShearForm f hdegree).residualHom =
      (e t).val.toAlgHom.comp A.form.topResidualEquiv.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  apply MvPolynomial.funext
  intro x
  simp only [AlgHom.comp_apply, ← MvPolynomial.aeval_eq_eval]
  rw [patchParameterSpecialization_eval, PolynomialSlots.residualHom_X,
    PolynomialSlots.residualCoordinate_eval,
    A.symbolicShearForm_slots f hdegree e hspecialize]
  change x i - (x i - aeval (polynomialSubstitutionPoint (e t).val.toAlgHom x)
    (A.form.topResidualEquiv (X i))) = aeval x ((e t).val (A.form.topResidualEquiv (X i)))
  rw [sub_sub_cancel]
  exact polynomialSubstitutionPoint_aeval (e t).val.toAlgHom x _

include hlower hspecialize in
theorem symbolicShearForm_loweringAt (t : τ → ℝ) :
    (A.symbolicShearForm f hdegree).loweringAt t = e t := by
  have hc := (A.symbolicShearForm f hdegree).loweringAt_comp_top t
  rw [A.symbolicShearForm_topResidualEquiv f hdegree hlower,
    A.symbolicShearForm_specialized_residualHom f hdegree e hspecialize] at hc
  apply Subtype.ext
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext
  intro P
  have h := congrArg (fun F : MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ =>
    F (A.form.topResidualEquiv.symm P)) hc
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h

include hlower hspecialize in
theorem symbolicShearForm_shearGroupLift
    (g : (τ → ℝ) → (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (he : ∀ t, e t = (polynomialShearRealAutEquiv A.weight s A.weight_le (g t))⁻¹)
    (t : τ → ℝ) :
    (A.symbolicShearForm f hdegree).shearGroupLift s A.weight_le t = g t := by
  unfold PolynomialSlots.shearGroupLift
  rw [A.symbolicShearForm_loweringAt f hdegree hlower e hspecialize, he t, inv_inv,
    MulEquiv.symm_apply_apply]

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {X Y : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem shearPatchValue_dist (A : PolynomialSlots X d w) (B : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hsmall : ε < 1 / 4)
    (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (hB : ∀ i, realPolynomialMass (B.center i) ≤ M)
    (hclose : ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ (1 + M) ^ (s * d)) →
      dist (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom x)
        (polynomialSubstitutionPoint B.topResidualEquiv.toAlgHom x) ≤ ε)
    (e : WeightedLoweringAut w ℝ) :
    dist ((A.shearTransformedSlots hw e).patchValue Φ)
      ((B.shearTransformedSlots hw e).patchValue Φ) ≤ Φ.lip * ε := by
  apply TriangularSlots.patchValue_dist_of_residuals_close _ _ Φ hε hsmall
  intro b hb
  let x := polynomialSubstitutionPoint e.val.toAlgHom (fun j => (b j : ℝ))
  have hx : ∀ i, |x i| ≤ (1 + M) ^ (s * d) := by
    rcases hb with hb | hb
    · apply A.topResidualPoint_preimage_bound hpos s hs hM hA x
      intro i
      have hi := Φ.support _ hb i
      rw [shearTransformedSlots_residual] at hi
      exact hi.trans (by norm_num)
    · apply B.topResidualPoint_preimage_bound hpos s hs hM hB x
      intro i
      have hi := Φ.support _ hb i
      rw [shearTransformedSlots_residual] at hi
      exact hi.trans (by norm_num)
  rw [shearTransformedSlots_residual, shearTransformedSlots_residual]
  exact hclose x hx

end Erdos3.PolynomialSlots

end

section

namespace Erdos3
open MvPolynomial

variable {τ : Type*} {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearOrbitSymbolicHom (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1)) :
    MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ :=
  polynomialShearExpHom (polynomialSymbolicShearDerivation w
    (polynomialShearOrbitParameterCoordinates s hw g))

theorem polynomialShearOrbitSymbolicHom_degree (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1))
    {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) w) n) :
    polynomialShearOrbitSymbolicHom hw g P ∈
      weightedSupportLE (Sum.elim (fun _ : τ => 1) w) n :=
  polynomialSymbolicShearExp_total_degree w _
    (polynomialShearOrbitParameterCoordinates_degree s hw g) hP

theorem polynomialShearOrbitSymbolicHom_specialization (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1))
    (t : τ → ℝ) (P : MvPolynomial (τ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialShearOrbitSymbolicHom hw g P) =
      (polynomialShearRealAutEquiv w s hw
        ((polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
          (fun _ : τ => 1) t g)).val (patchParameterSpecialization t P) :=
  polynomialShearOrbitSymbolicExp_specialization w s hw g t P

theorem polynomialShearOrbitSymbolicHom_lower (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1))
    {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 0) w) n) :
    polynomialShearOrbitSymbolicHom hw g P - P ∈
      weightedSupportLT (Sum.elim (fun _ : τ => 0) w) n :=
  polynomialShearExp_sub_lower _ hP

namespace PolynomialPatch
variable {σ : Type*} (A : PolynomialPatch σ s d)

noncomputable def ofShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : PolynomialPatch τ s d := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.symbolicShearPatch (polynomialShearOrbitSymbolicHom A.weight_le g⁻¹)
    (polynomialShearOrbitSymbolicHom_degree A.weight_le g⁻¹)

@[simp] theorem ofShearOrbit_weight
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : (A.ofShearOrbit g).weight = A.weight := rfl

@[simp] theorem ofShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : (A.ofShearOrbit g).kernel = A.kernel := rfl

theorem ofShearOrbit_value_real
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) (t : τ → ℝ) :
    (A.ofShearOrbit g).value t = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        (fun _ : τ => 1) t g)) := by
  let _ := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.symbolicShearPatch_value_eq_observable
    (polynomialShearOrbitSymbolicHom A.weight_le g⁻¹)
    (polynomialShearOrbitSymbolicHom_degree A.weight_le g⁻¹)
    (fun t => polynomialShearRealAutEquiv A.weight s A.weight_le
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        (fun _ : τ => 1) t g⁻¹))
    (polynomialShearOrbitSymbolicHom_specialization A.weight_le g⁻¹)
    (fun t => (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
      (fun _ : τ => 1) t g)
    (fun t => by rw [map_inv, map_inv]) t

theorem ofShearOrbit_value_integer
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) (t : τ → ℤ) :
    (A.ofShearOrbit g).value (fun i => (t i : ℝ)) = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
        (fun _ : τ => 1) t g)) := by
  rw [ofShearOrbit_value_real, NilpotentLieFiltration.polynomialOrbitRealEval_integer]

theorem ofShearOrbit_shearGroupLift_real
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) (t : τ → ℝ) :
    (A.ofShearOrbit g).form.shearGroupLift s A.weight_le t =
      (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        (fun _ : τ => 1) t g := by
  let _ := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.symbolicShearForm_shearGroupLift
    (polynomialShearOrbitSymbolicHom A.weight_le g⁻¹)
    (polynomialShearOrbitSymbolicHom_degree A.weight_le g⁻¹)
    (polynomialShearOrbitSymbolicHom_lower A.weight_le g⁻¹)
    (fun t => polynomialShearRealAutEquiv A.weight s A.weight_le
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        (fun _ : τ => 1) t g⁻¹))
    (polynomialShearOrbitSymbolicHom_specialization A.weight_le g⁻¹)
    (fun t => (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
      (fun _ : τ => 1) t g)
    (fun t => by rw [map_inv, map_inv]) t

theorem ofShearOrbit_shearGroupLift_integer
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) (t : τ → ℤ) :
    (A.ofShearOrbit g).form.shearGroupLift s A.weight_le (fun i => (t i : ℝ)) =
      (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
        (fun _ : τ => 1) t g := by
  rw [ofShearOrbit_shearGroupLift_real, NilpotentLieFiltration.polynomialOrbitRealEval_integer]

theorem exists_patch_of_shear_orbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) :
    ∃ B : PolynomialPatch τ s d, B.weight = A.weight ∧ B.kernel = A.kernel ∧
      ∀ t : τ → ℤ, B.value (fun i => (t i : ℝ)) = A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fun _ : τ => 1) t g)) :=
  ⟨A.ofShearOrbit g, rfl, rfl, A.ofShearOrbit_value_integer g⟩

end PolynomialPatch
end Erdos3

end

end OAI
