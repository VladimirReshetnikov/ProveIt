import OAI.Combinatorics.Progressions.Estimates.AuxiliaryCellMeans
import OAI.Combinatorics.Progressions.Estimates.TranslatedStabilityStep
import OAI.Combinatorics.Progressions.Lattices.HalfResidueDescent

namespace OAI

section

namespace Erdos3

open Module CircleFourier NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_affine_stability_step (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ τ L : Type*} [Fintype τ] [DecidableEq τ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card τ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ (T : D.Niltest (fun _ : σ => 1)), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (V : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        {β : Type*} (A : β → σ → τ → ℤ) (b : β → σ → ℤ)
        (origin : β → τ → ℤ) (lengths : β → τ → ℕ),
      (∀ a i, 0 < lengths a i) →
      (∀ a i, Real.exp ((q + C) ^ C) ≤ (lengths a i : ℝ)) →
      (∃ (a : β) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
          (u : Fin d → D.filtration.AssociatedGraded),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        Submodule.span ℚ (Set.range u) = U.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
        (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (u i) j) ≤
          (q + C) ^ C) ∧
        finrank ℚ ↥(V ⊓ U) < finrank ℚ V ∧
        D.filtration.SymbolFactorizationIn D.basis ω hF (fun i => (lengths a i : ℝ))
          ((T.affinePullback (A a) (b a)).symbol D.basis ω hF) ((q + C) ^ C) l U) ∨
      (∃ S : D.Niltest (fun _ : σ => 1),
        S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ (D.filtration.gradedRefiltrationLayer V s).baseChange ℝ →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        ∀ a, ‖(𝔼 x ∈ translatedIntegerBox (origin a) (lengths a),
            (T.affinePullback (A a) (b a)).eval x) -
          (𝔼 x ∈ translatedIntegerBox (origin a) (lengths a),
            (S.affinePullback (A a) (b a)).eval x)‖ ≤
              2 * rho + Real.exp (verticalDecompositionBudget p - q)) := by
  classical
  obtain ⟨C, hC, hstep⟩ := exists_translated_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro σ τ L _ _ _ _ d _ _ _ _ D ω hF p q rho hp hpq hτ hfreq hrho hrhop
    T hunit hTc V β A b origin lengths hlength hlarge
  obtain ⟨J, inst, eta, U, hcard, hheight, hU, hvertical, _, _, happrox, _⟩ :=
    T.exists_controlled_vertical_decomposition hp hTc rho hrho hrhop
  let := inst
  let K := D.filtration.gradedRefiltrationLayer V s
  by_cases hevent : ∃ (j : J) (a : β),
      Real.exp (-q) < ‖𝔼 x ∈ translatedIntegerBox (origin a) (lengths a),
        ((U j).affinePullback (A a) (b a)).eval x‖ ∧ ∃ v ∈ K, eta j v ≠ 0
  · left
    obtain ⟨j, a, hbias, hnonzero⟩ := hevent
    have hfactor := hstep D ω hF q (hp.trans hpq) hτ ((U j).affinePullback (A a) (b a))
      ((hU j).1.mono hpq) (eta j) (fun i => (hheight j i).trans hfreq) (hvertical j)
      (origin a) (lengths a) (hlength a) (hlarge a) hbias.le
    have horbit := (U j).affinePullback_orbit_eq_of_orbit_eq T (hU j).2 (A a) (b a)
    have hsymbol := ((U j).affinePullback (A a) (b a)).symbol_eq_of_orbit_eq
      (T.affinePullback (A a) (b a)) horbit D.basis ω hF
    rw [hsymbol] at hfactor
    obtain ⟨l, W, u, hl, hlp, hspan, hgraded, hheightW, _hkill, hdim, hfixed⟩ :=
      ControlledSymbolFactorization.exists_dimension_drop D.filtration D.basis ω hF hfactor V hnonzero
    exact ⟨a, l, W, u, hl, hlp, hspan, hgraded, hheightW, hdim, hfixed⟩
  · right
    have hkill : ∀ j, (∃ a, Real.exp (-q) <
        ‖𝔼 x ∈ translatedIntegerBox (origin a) (lengths a),
          ((U j).affinePullback (A a) (b a)).eval x‖) →
        ∀ v ∈ K, eta j v = 0 := by
      intro j ⟨a, ha⟩ v hv
      by_contra hne
      exact hevent ⟨j, a, ha, v, hv, hne⟩
    have hboxes (a : β) : (translatedIntegerBox (origin a) (lengths a)).Nonempty := by
      refine ⟨origin a, (mem_translatedIntegerBox (origin a) (lengths a) (origin a)).mpr ?_⟩
      intro i
      have hi := hlength a i
      exact ⟨le_rfl, by omega⟩
    obtain ⟨S, hS, hSc, hSo, hinv, herr⟩ := T.exists_affine_finset_kernel_projection_family
      hunit hTc K (D.filtration.gradedRefiltrationLayer_le V s) eta U (fun j => (hU j).2)
      hvertical A b (fun a => translatedIntegerBox (origin a) (lengths a)) hboxes
      (fun _ => Real.exp (-q)) hrho.le (fun _ => (Real.exp_pos _).le)
      (fun x => by simpa only [norm_sub_rev] using happrox x) hkill
    refine ⟨S, hS, hSc, hSo, hinv, ?_⟩
    intro a
    apply (herr a).trans
    apply add_le_add le_rfl
    calc
      (Fintype.card J : ℝ) * Real.exp (-q) ≤
          Real.exp (verticalDecompositionBudget p) * Real.exp (-q) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = Real.exp (verticalDecompositionBudget p - q) := by rw [← Real.exp_add, sub_eq_add_neg]

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_residue_law_stability_step (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (V : LieSubalgebra ℚ D.filtration.AssociatedGraded) {β : Type*}
        (lo hi : β → σ → ℤ) (M : β → ℕ) (u v : β → σ → ℤ) (J : β → σ → ℕ),
      (∀ a, 0 < M a) → (∀ a i, 0 < J a i) →
      (∀ a i, v a i ≡ u a i [ZMOD (M a : ℤ)]) →
      (∀ a i, ((M a * J a i : ℕ) : ℝ) * (Real.exp ((q + C) ^ C) + 1) ≤
        ((hi a i - lo a i : ℤ) : ℝ)) →
      let lawMean : D.Niltest (fun _ : σ => 1) → β → ℂ := fun F a =>
        𝔼 x : IntegerResidueBox (lo a) (hi a) (fun i => (M a * J a i : ℕ)) (v a),
          residueBoxStrideValue F.eval (u a) (M a) x
      (∃ (a : β) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
          (z : Fin d → D.filtration.AssociatedGraded),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        Submodule.span ℚ (Set.range z) = U.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
        (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (z i) j) ≤
          (q + C) ^ C) ∧
        finrank ℚ ↥(V ⊓ U) < finrank ℚ V ∧
        D.filtration.SymbolFactorizationIn D.basis ω hF
          (fun i => (residueIndexLength (lo a i) (hi a i) (M a * J a i : ℕ) (v a i) : ℝ))
          ((T.affinePullback (residueStepMatrix (J a)) (commonStrideIndex (u a) (M a) (v a))).symbol
            D.basis ω hF) ((q + C) ^ C) l U) ∨
      (∃ S : D.Niltest (fun _ : σ => 1),
        S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer V s →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        (∀ a, ‖lawMean T a - lawMean S a‖ ≤
          2 * rho + Real.exp (verticalDecompositionBudget p - q)) ∧
        ∀ a b, ‖lawMean T a - lawMean T b‖ -
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤
            ‖lawMean S a - lawMean S b‖) := by
  obtain ⟨C, hC, hstep⟩ := exists_affine_stability_step s hs
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p q rho hp hpq hσ hfreq hrho hrhop
    T hunit hT V β lo hi M u v J hM hJ hv hlarge lawMean
  have hcounts : ∀ a i, Real.exp ((q + C) ^ C) ≤
      (residueIndexLength (lo a i) (hi a i) (M a * J a i : ℕ) (v a i) : ℝ) := by
    intro a i
    exact residueIndexLength_ge_of_width (lo a i) (hi a i) (M a * J a i : ℕ) (v a i)
      (by exact_mod_cast Nat.mul_pos (hM a) (hJ a i)) _ (Real.exp_nonneg _) (by
        simpa only [Int.cast_natCast] using hlarge a i)
  have hpositive : ∀ a i, 0 < residueIndexLength (lo a i) (hi a i) (M a * J a i : ℕ) (v a i) := by
    intro a i
    have h := (Real.exp_pos _).trans_le (hcounts a i)
    exact_mod_cast h
  let origin : β → σ → ℤ := fun a i => residueIndexLower (lo a i) (M a * J a i : ℕ) (v a i)
  let lengths : β → σ → ℕ := fun a i => residueIndexLength (lo a i) (hi a i) (M a * J a i : ℕ) (v a i)
  rcases hstep D ω hF p q rho hp hpq hσ hfreq hrho hrhop T hunit hT V
    (fun a => residueStepMatrix (J a)) (fun a => commonStrideIndex (u a) (M a) (v a))
    origin lengths hpositive hcounts with hevent | hprojection
  · exact Or.inl hevent
  · obtain ⟨S, hS, hSc, hSo, hinvariant, hmeans⟩ := hprojection
    have hm : ∀ a, ‖lawMean T a - lawMean S a‖ ≤
        2 * rho + Real.exp (verticalDecompositionBudget p - q) := by
      intro a
      dsimp only [lawMean]
      rw [T.residueBoxStride_mean (lo a) (hi a) (M a) (hM a) (u a) (v a) (J a) (hJ a) (hv a),
        S.residueBoxStride_mean (lo a) (hi a) (M a) (hM a) (u a) (v a) (J a) (hJ a) (hv a)]
      exact hmeans a
    refine Or.inr ⟨S, hS, hSc, hSo, hinvariant, hm, ?_⟩
    intro a b
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (lawMean T a) (lawMean S a) (lawMean T b)
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (lawMean S a) (lawMean S b) (lawMean T b)
    rw [norm_sub_rev (lawMean S b) (lawMean T b)] at h₂
    linarith [hm a, hm b]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

def residuePairStep {I : Type*} (J : I → ℕ) (flag : Bool) : I → ℕ :=
  if flag then J else fun _ => 1

def residuePairValue {I : Type*} (u v : I → ℤ) (flag : Bool) : I → ℤ :=
  if flag then v else u

noncomputable def residuePairMean {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ)
    (J : I → ℕ) (flag : Bool) : ℂ :=
  𝔼 x : IntegerResidueBox lo (fun i => lo i + N i)
    (fun i => (M * residuePairStep J flag i : ℕ)) (residuePairValue u v flag),
    residueBoxStrideValue f u M x

@[simp] theorem residuePairMean_false {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ) (J : I → ℕ) :
    residuePairMean f lo N M u v J false =
      𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u,
        residueBoxStrideValue f u M x := by
  exact congrArg
    (fun r : I → ℤ => 𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) r u,
      residueBoxStrideValue f u M x)
    (show (fun _ : I => ((M * 1 : ℕ) : ℤ)) = (fun _ => (M : ℤ)) by
      funext i
      rw [Nat.mul_one])

@[simp] theorem residuePairMean_true {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ) (J : I → ℕ) :
    residuePairMean f lo N M u v J true =
      𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v,
        residueBoxStrideValue f u M x := rfl

noncomputable def ResiduePairDimensionDrop {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ) (B : ℝ) : Prop :=
  ∃ (flag : Bool) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (z : Fin d → D.filtration.AssociatedGraded),
    0 < l ∧ (l : ℝ) ≤ Real.exp B ∧
    Submodule.span ℚ (Set.range z) = U.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (z i) j) ≤ B) ∧
    finrank ℚ ↥(W ⊓ U) < finrank ℚ W ∧
    D.filtration.SymbolFactorizationIn D.basis ω hF
      (fun i => (residueIndexLength (lo i) (lo i + N i) (M * residuePairStep J flag i : ℕ)
        (residuePairValue u v flag i) : ℝ))
      ((T.affinePullback (residueStepMatrix (residuePairStep J flag))
        (commonStrideIndex u M (residuePairValue u v flag))).symbol D.basis ω hF) B l U

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem auxiliary_piece_residue_pair {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} (T : D.Niltest (fun _ : σ => 1))
    (lo : σ → ℤ) (N : σ → ℕ) (cells : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (cells i).step k = 1) (hpos : ∀ i k, 0 < (cells i).length k)
    (M P : ℕ) (hM : 0 < M) (hP : 0 < P) (u v : σ → ℤ) (J : σ → ℕ)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (hcop : ∀ i, (M * (M * P)).Coprime (J i))
    (k : AuxiliaryBoxLabels cells (fun _ => M) (fun _ => M * P) u)
    (hk₀ : 0 < (partitionCell (baseAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P)
      (fun _ => Nat.mul_pos hM hP) u) k).card)
    (hk₁ : 0 < (partitionCell (refinedAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P) J
      (fun _ => Nat.mul_pos hM hP) u v hv) k).card) :
    let Q := Nat.lcm M (M * P)
    let w : σ → ℤ := fun i => (k i).2.baseValue
    let z : σ → ℤ := fun i => (k i).2.refinedValue (hcop i) (v i)
    let lo' : σ → ℤ := fun i => intervalCellLower (lo i) (cells i) (k i).1
    let N' : σ → ℕ := fun i => (cells i).length (k i).1
    let S := T.scalarAffinePullback (Q / M : ℕ) (fun i => (commonStrideIndex u M w i : ℚ))
    (∀ i, z i ≡ w i [ZMOD (Q : ℤ)]) ∧
    Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w) ∧
    Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z) ∧
    (𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P)
      (fun _ => Nat.mul_pos hM hP) u) k, residueBoxStrideValue T.eval u M x) =
      residuePairMean S.eval lo' N' Q w z J false ∧
    (𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P) J
      (fun _ => Nat.mul_pos hM hP) u v hv) k, residueBoxStrideValue T.eval u M x) =
      residuePairMean S.eval lo' N' Q w z J true := by
  intro Q w z lo' N' S
  have hw : ∀ i, w i ≡ u i [ZMOD (M : ℤ)] := fun i => (k i).2.baseValue_spec.1
  have hz : ∀ i, z i ≡ w i [ZMOD (Q : ℤ)] := by
    intro i
    have h := (k i).2.refinedValue_spec (hcop i) (v i)
    exact ((k i).2.baseConstraint_iff (z i)).mp ⟨h.1, h.2.1⟩
  have hMQ : M ∣ Q := Nat.dvd_lcm_left M (M * P)
  refine ⟨hz, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp hk₀
    exact ⟨boxAuxiliaryCellEquiv lo N cells hstep hpos (fun _ => M) (fun _ => M * P)
      (fun _ => Nat.mul_pos hM hP) u (fun _ => (M : ℤ)) u (fun _ _ hx => hx) k
      (fun _ => (Q : ℤ)) w (fun i => (k i).2.baseConstraint_iff) ⟨x, hx⟩⟩
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp hk₁
    exact ⟨boxAuxiliaryCellEquiv lo N cells hstep hpos (fun _ => M) (fun _ => M * P)
      (fun _ => Nat.mul_pos hM hP) u (fun i => (M * J i : ℕ)) v
      (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) k
      (fun i => (Q * J i : ℕ)) z (fun i => (k i).2.refinedConstraint_iff (hcop i) (v i) (hv i)) ⟨x, hx⟩⟩
  · rw [residuePairMean_false]
    exact (baseAuxiliaryBoxCell_expect lo N cells hstep hpos (fun _ => M) (fun _ => M * P)
      (fun _ => Nat.mul_pos hM hP) u k (fun y => T.eval (commonStrideIndex u M y))).trans
      (T.residueBoxStride_rebase lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w u w
        hM hMQ hw (fun _ _ hx => hx))
  · rw [residuePairMean_true]
    exact (refinedAuxiliaryBoxCell_expect lo N cells hstep hpos (fun _ => M) (fun _ => M * P) J
      (fun _ => Nat.mul_pos hM hP) u v hv hcop k (fun y => T.eval (commonStrideIndex u M y))).trans
      (T.residueBoxStride_rebase lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z u w
        hM hMQ hw (fun i => refinedResidue_implies_base Q (J i) (w i) (z i) (hz i)))

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem residuePairStep_const {σ : Type*} (J : ℕ) (flag : Bool) :
    residuePairStep (fun _ : σ => J) flag = fun _ => if flag then J else 1 := by
  cases flag <;> rfl

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

theorem residue_scalar_composed_symbol (T : D.Niltest (fun _ : σ => 1))
    (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (r : ℚ) (h : σ → ℚ) (J : ℕ) (shift : σ → ℤ) :
    ((T.scalarAffinePullback r h).affinePullback (residueStepMatrix (fun _ : σ => J)) shift).symbol
        D.basis ω hF =
      (T.scalarAffinePullback (r * J) (fun i => r * (shift i : ℚ) + h i)).symbol D.basis ω hF := by
  rw [(T.scalarAffinePullback r h).residue_scalar_affine_symbol ω hF J shift]
  exact ((T.scalarAffinePullback r h).scalarAffinePullback (J : ℚ) (fun i => (shift i : ℚ))).symbol_eq_of_orbit_eq
    (T.scalarAffinePullback (r * J) (fun i => r * (shift i : ℚ) + h i))
    (T.scalarAffinePullback_comp_orbit r (J : ℚ) h (fun i => (shift i : ℚ))) D.basis ω hF

end RationalFilteredNilmanifold.Niltest

theorem ResiduePairDimensionDrop.scalar_record {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) (r : ℚ) (h : σ → ℚ)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (M J : ℕ) (u v : σ → ℤ) (B : ℝ)
    (hevent : ResiduePairDimensionDrop D ω hF (T.scalarAffinePullback r h) W lo N M u v
      (fun _ => J) B) :
    ∃ (flag : Bool) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (z : Fin d → D.filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp B ∧
      Submodule.span ℚ (Set.range z) = U.toSubmodule ∧
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (z i) j) ≤ B) ∧
      finrank ℚ ↥(W ⊓ U) < finrank ℚ W ∧
      D.filtration.SymbolFactorizationIn D.basis ω hF
        (fun i => (residueIndexLength (lo i) (lo i + N i) (M * (if flag then J else 1) : ℕ)
          (residuePairValue u v flag i) : ℝ))
        ((T.scalarAffinePullback (r * (if flag then J else 1 : ℕ))
          (fun i => r * (commonStrideIndex u M (residuePairValue u v flag) i : ℚ) + h i)).symbol
            D.basis ω hF) B l U := by
  obtain ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩ := hevent
  rw [residuePairStep_const] at hfactor
  rw [T.residue_scalar_composed_symbol] at hfactor
  exact ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_residue_pair_stability_step (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (lo : σ → ℤ) (N : σ → ℕ)
        (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ),
      0 < M → (∀ i, 0 < J i) → (∀ i, v i ≡ u i [ZMOD (M : ℤ)]) →
      (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + C) ^ C) + 1) ≤ (N i : ℝ)) →
      let eta := 2 * rho + Real.exp (verticalDecompositionBudget p - q)
      ResiduePairDimensionDrop D ω hF T W lo N M u v J ((q + C) ^ C) ∨
      ∃ S : D.Niltest (fun _ : σ => 1),
        S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W s →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        (∀ flag, ‖residuePairMean T.eval lo N M u v J flag -
          residuePairMean S.eval lo N M u v J flag‖ ≤ eta) ∧
        ‖residuePairMean T.eval lo N M u v J false - residuePairMean T.eval lo N M u v J true‖ -
          2 * eta ≤
          ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖ := by
  obtain ⟨C, hC, hstep⟩ := exists_residue_law_stability_step s hs
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p q rho hp hpq hσ hfreq hrho hrhop
    T hunit hT W lo N M u v J hM hJ hv hlarge eta
  have hpositive : ∀ flag i, 0 < residuePairStep J flag i := by
    intro flag i
    cases flag
    · exact Nat.zero_lt_one
    · exact hJ i
  have hcompat : ∀ flag i, residuePairValue u v flag i ≡ u i [ZMOD (M : ℤ)] := by
    intro flag i
    cases flag
    · exact Int.ModEq.refl (u i)
    · exact hv i
  have hwidth : ∀ flag i, ((M * residuePairStep J flag i : ℕ) : ℝ) *
      (Real.exp ((q + C) ^ C) + 1) ≤ ((lo i + N i - lo i : ℤ) : ℝ) := by
    intro flag i
    simp only [add_sub_cancel_left, Int.cast_natCast]
    cases flag
    · change ((M * 1 : ℕ) : ℝ) * (Real.exp ((q + C) ^ C) + 1) ≤ (N i : ℝ)
      rw [Nat.mul_one]
      have hm : (M : ℝ) ≤ (M * J i : ℕ) := by exact_mod_cast Nat.le_mul_of_pos_right M (hJ i)
      exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans (hlarge i)
    · exact hlarge i
  rcases hstep D ω hF p q rho hp hpq hσ hfreq hrho hrhop T hunit hT W
    (fun _ : Bool => lo) (fun _ i => lo i + N i) (fun _ => M) (fun _ => u)
    (residuePairValue u v) (residuePairStep J) (fun _ => hM) hpositive hcompat hwidth with hevent | hprojection
  · exact Or.inl hevent
  · obtain ⟨S, hS, hSc, hSo, hinvariant, hmeans, hgap⟩ := hprojection
    exact Or.inr ⟨S, hS, hSc, hSo, hinvariant, hmeans, hgap false true⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem ResiduePairDimensionDrop.of_orbit_eq {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T S : D.Niltest (fun _ : σ => 1)) (hTS : T.orbit = S.orbit)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ) (B : ℝ)
    (hevent : ResiduePairDimensionDrop D ω hF T W lo N M u v J B) :
    ResiduePairDimensionDrop D ω hF S W lo N M u v J B := by
  obtain ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩ := hevent
  have horbit := T.affinePullback_orbit_eq_of_orbit_eq S hTS
    (residueStepMatrix (residuePairStep J flag)) (commonStrideIndex u M (residuePairValue u v flag))
  have hsymbol := (T.affinePullback (residueStepMatrix (residuePairStep J flag))
      (commonStrideIndex u M (residuePairValue u v flag))).symbol_eq_of_orbit_eq
    (S.affinePullback (residueStepMatrix (residuePairStep J flag))
      (commonStrideIndex u M (residuePairValue u v flag))) horbit D.basis ω hF
  rw [hsymbol] at hfactor
  exact ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_residue_event_or_child_descent (s : ℕ) (hs : 1 ≤ s) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ {σ L K : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {d t e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (V : RationalFilteredNilmanifold K t e)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (q₀ P C a : ℕ) (hP : 0 < P) (cost : ℝ),
      FixedResidueDescent D W V (fun _ : σ => 1) b child p q₀ P hP C a cost →
      ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (E R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
          ⟨⟨T.orbit.log, T.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q₀ R →
        ∀ A : σ → ℝ, (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A (Real.exp ((p + 2) ^ a)) E →
          ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (hM : 0 < M) (u v : σ → ℤ) (J : σ → ℕ),
          (∀ i, 0 < J i) → ∀ hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)],
          (∀ i, (M * (M * P)).Coprime (J i)) →
          (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) →
          ∀ Δ ε δ : ℝ, 0 < δ → δ ≤ 1 → ε < 1 / 2 →
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2 →
          8 * ε + 2 * (Real.exp ((p + 2) ^ C) * δ) ≤ Δ / 4 →
          (∀ i, 8 ≤ δ * (N i : ℝ)) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 →
          Δ ≤ ‖residuePairMean T.eval lo N M u v J false - residuePairMean T.eval lo N M u v J true‖ →
          ResiduePairDimensionDrop D ω hF T W lo N M u v J ((q + B) ^ B) ∨
          ∃ (H : σ → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i),
            (∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ)) ∧
            (∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4) ∧
            let Q := comparableBoxPartitions N H hH hHN
            let c₀ := baseAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P)
              (fun _ => Nat.mul_pos hM hP) u
            let c₁ := refinedAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P) J
              (fun _ => Nat.mul_pos hM hP) u v hv
            ∃ k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * P) u,
              0 < (partitionCell c₀ k).card ∧ 0 < (partitionCell c₁ k).card ∧
              ∃ U : V.Niltest (fun _ : σ => 1),
                U.orbit = child ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
                Δ / 4 ≤ ‖(𝔼 x ∈ partitionCell c₀ k, residueBoxStrideValue U.eval u M x) -
                  (𝔼 x ∈ partitionCell c₁ k, residueBoxStrideValue U.eval u M x)‖ := by
  obtain ⟨B, hB, hstep⟩ := exists_residue_pair_stability_step s hs
  refine ⟨B, hB, ?_⟩
  intro σ L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ d t e D V ω hF p q rho hp hpq hσ hfreq hrho hrhop
    W b child q₀ P C a hP cost hdesc T hunit hT E R κ hκ hprod hgrid A hA hE
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  rcases hstep D ω hF p q rho hp hpq hσ hfreq hrho hrhop T hunit hT W lo N M u v J
    hM hJ hv hsteplarge with hevent | hprojected
  · exact Or.inl hevent
  · obtain ⟨S, hunitS, hS, hSo, hinvariant, _, hSgap⟩ := hprojected
    have hprodS : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨S.orbit.log, S.orbit.property⟩⟩ := by
      simpa only [hSo] using hprod
    have hgapS : Δ / 2 ≤
        ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖ := by
      linarith
    simp only [residuePairMean_false, residuePairMean_true] at hgapS
    have hresult := hdesc.half_discrepancy S hS hunitS hinvariant E R κ hκ hprodS hgrid A hA hE
      M hM lo N u v J hJ hv hcop (Δ / 2) ε δ hδ hδone hε
      (by nlinarith : 8 * ε + 2 * (Real.exp ((p + 2) ^ C) * δ) ≤ (Δ / 2) / 2)
      hlarge hphysical hcount hgapS
    right
    simpa only [show (Δ / 2) / 2 = Δ / 4 by ring] using hresult

end Erdos3

end

end OAI
