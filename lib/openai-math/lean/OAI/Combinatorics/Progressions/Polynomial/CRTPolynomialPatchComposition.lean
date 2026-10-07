import OAI.Combinatorics.Progressions.Estimates.WeightedPatchReparam
import OAI.Combinatorics.Progressions.Geometry.RepresentativeWindowTransport

namespace OAI

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

def liftInterleaving (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    SlotInterleaving D E :=
  SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono

theorem liftInterleaving_before (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (j : Fin D) (i : Fin E) (h : A.weight j ≤ B.weight i) :
    (A.liftInterleaving B).left j < (A.liftInterleaving B).right i :=
  SlotInterleaving.sorted_left_lt_right _ _ _ _ j i h

noncomputable def insertLifts (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    PolynomialPatch σ s (D + E) :=
  let I := A.liftInterleaving B
  { weight := I.fill A.weight B.weight
    weight_pos := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_pos i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_pos i)
    weight_le := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_le i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_le i)
    weight_mono := SlotInterleaving.sorted_weight_mono _ _ _ _
    form := A.form.insertLifts B.form I
    kernel := A.kernel.product B.kernel I }

@[simp] theorem insertLifts_lip (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    (A.insertLifts B).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

theorem insertLifts_term (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) (z : Fin (D + E) → ℤ) :
    (A.insertLifts B).kernel.value (((A.insertLifts B).form.slots t).residual z) =
      A.kernel.value ((A.form.slots t).residual (fun j => z ((A.liftInterleaving B).left j))) *
      B.kernel.value ((B.form.slots (Sum.elim t
        (fun j => (z ((A.liftInterleaving B).left j) : ℝ)))).residual
          (fun j => z ((A.liftInterleaving B).right j))) := by
  let I := A.liftInterleaving B
  change A.kernel.value (fun i => ((A.form.insertLifts B.form I).slots t).residual z (I.left i)) *
    B.kernel.value (fun i => ((A.form.insertLifts B.form I).slots t).residual z (I.right i)) = _
  simp only [PolynomialSlots.insertLifts_residual_left,
    PolynomialSlots.insertLifts_residual_right A.form B.form I (A.liftInterleaving_before B)]
  rfl

theorem insertLifts_contributing_lift (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) (b : Fin D → ℤ)
    (hb : ∀ i, |(A.form.slots t).residual b i| ≤ 1 / 3)
    {z : Fin (D + E) → ℤ}
    (hz : (A.insertLifts B).kernel.value (((A.insertLifts B).form.slots t).residual z) ≠ 0) :
    (fun j => z ((A.liftInterleaving B).left j)) = b := by
  rw [insertLifts_term] at hz
  exact (A.form.slots t).integer_unique (by norm_num)
    (A.kernel.support _ (mul_ne_zero_iff.mp hz).1) hb

theorem insertLifts_value_at_lift (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) (b : Fin D → ℤ)
    (hb : ∀ i, |(A.form.slots t).residual b i| ≤ 1 / 3) :
    (A.insertLifts B).value t = A.kernel.value ((A.form.slots t).residual b) *
      B.value (Sum.elim t (fun j => (b j : ℝ))) :=
  (A.form.slots t).factorized_patchValue_at_lift
    (fun b => B.form.slots (Sum.elim t (fun j => (b j : ℝ))))
    ((A.insertLifts B).form.slots t) A.kernel B.kernel (A.insertLifts B).kernel
    (A.liftInterleaving B) (A.insertLifts_term B t) b hb

theorem insertLifts_value (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) :
    (A.insertLifts B).value t = ∑' b : Fin D → ℤ,
      A.kernel.value ((A.form.slots t).residual b) *
        B.value (Sum.elim t (fun j => (b j : ℝ))) :=
  (A.form.slots t).factorized_patchValue
    (fun b => B.form.slots (Sum.elim t (fun j => (b j : ℝ))))
    ((A.insertLifts B).form.slots t) A.kernel B.kernel (A.insertLifts B).kernel
    (A.liftInterleaving B) (A.insertLifts_term B t)

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtLiftPolynomial : MvPolynomial (J ⊕ Fin 1) ℝ :=
  (∑ j, (crtIntegerCoefficient N hN j : ℝ) • X (Sum.inl j)) -
    ((∏ j, N j : ℕ) : ℝ) • X (Sum.inr 0)

omit [NeZero (∏ j, N j)] in
theorem crtLiftPolynomial_degree :
    crtLiftPolynomial N hN ∈
      weightedSupportLE (Sum.elim (fun _ : J => 1) (fun _ : Fin 1 => 1)) 1 := by
  apply (weightedSupportLE _ _).sub_mem
  · apply Submodule.sum_mem
    intro j _
    apply (weightedSupportLE _ _).smul_mem
    exact weightedSupportLE_X _ (Sum.inl j)
  · exact (weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ (Sum.inr 0))

omit [NeZero (∏ j, N j)] in
theorem crtLiftPolynomial_eval (u : J → ℤ) (b : Fin 1 → ℤ) :
    aeval (Sum.elim (fun j => (u j : ℝ)) (fun i => (b i : ℝ))) (crtLiftPolynomial N hN) =
      ((crtIntegerRepresentative N hN u - (∏ j, N j : ℕ) * b 0 : ℤ) : ℝ) := by
  simp only [crtLiftPolynomial, map_sub, map_sum, map_smul, aeval_X,
    Sum.elim_inl, Sum.elim_inr, smul_eq_mul, crtIntegerRepresentative,
    Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

namespace RepresentativeWindow

variable (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) {d : ℕ}

noncomputable def composeCRTPatch (P : PolynomialPatch Unit s d) : PolynomialPatch J s (1 + d) :=
  (w.crtPatch N hN s hs).insertLifts
    (P.weightedParameters.reparam
      (q := Sum.elim (fun _ : J => 1) (w.crtPatch N hN s hs).weight)
      (fun _ : Unit => crtLiftPolynomial N hN)
      (by
        intro _
        change crtLiftPolynomial N hN ∈
          weightedSupportLE (Sum.elim (fun _ : J => 1) (fun _ : Fin 1 => 1)) 1
        exact crtLiftPolynomial_degree N hN))

omit [NeZero (∏ j, N j)] in
@[simp] theorem composeCRTPatch_lip (P : PolynomialPatch Unit s d) :
    (w.composeCRTPatch N hN s hs P).kernel.lip = w.lip + P.kernel.lip := rfl

theorem composeCRTPatch_value (P : PolynomialPatch Unit s d) (u : J → ℤ) :
    (w.composeCRTPatch N hN s hs P).value (fun j => (u j : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) *
      P.value (fun _ => (((ZMod.prodEquivPi N hN).symm
        (fun j => (u j : ZMod (N j)))).val : ℝ)) := by
  rw [composeCRTPatch, PolynomialPatch.insertLifts_value]
  simpa only [WeightedParameterPatch.reparam_value, PolynomialPatch.weightedParameters_value,
    crtLiftPolynomial_eval, Int.cast_natCast] using
    w.crtPatch_weighted_value N hN s hs u (fun n => P.value (fun _ => (n : ℝ)))

theorem composeCRTPatch_value_residues [∀ j, NeZero (N j)]
    (P : PolynomialPatch Unit s d) (u : (j : J) → ZMod (N j)) :
    (w.composeCRTPatch N hN s hs P).value (fun j => ((u j).val : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm u).val : ℝ) / (∏ j, N j : ℕ)) *
      P.value (fun _ => (((ZMod.prodEquivPi N hN).symm u).val : ℝ)) := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
    w.composeCRTPatch_value N hN s hs P (fun j => ((u j).val : ℤ))

omit [NeZero (∏ j, N j)] in

theorem composeCRTPatch_cost (P : PolynomialPatch Unit s d) {p q : ℝ}
    (hP : (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ p)
    (hw : Real.log (2 + (w.lip : ℝ)) ≤ q) :
    ((1 + d : ℕ) : ℝ) +
      Real.log (2 + ((w.composeCRTPatch N hN s hs P).kernel.lip : ℝ)) ≤ p + q + 1 := by
  have hp0 := P.kernel.lip.coe_nonneg
  have hw0 := w.lip.coe_nonneg
  have hlog : Real.log (2 + ((w.lip : ℝ) + P.kernel.lip)) ≤
      Real.log (2 + (w.lip : ℝ)) + Real.log (2 + (P.kernel.lip : ℝ)) := by
    calc
      _ ≤ Real.log ((2 + (w.lip : ℝ)) * (2 + (P.kernel.lip : ℝ))) := by
        apply Real.log_le_log (by positivity)
        nlinarith [mul_nonneg hw0 hp0]
      _ = _ := Real.log_mul (by positivity) (by positivity)
  rw [composeCRTPatch_lip, NNReal.coe_add, Nat.cast_add, Nat.cast_one]
  linarith

end RepresentativeWindow
end Erdos3

end

end OAI
