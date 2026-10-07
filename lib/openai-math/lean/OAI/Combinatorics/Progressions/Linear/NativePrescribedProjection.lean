import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds

namespace OAI

section

namespace Erdos3.CircleFourier.IsometricCircleAction

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def project (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFourierComponent n f

theorem project_character (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ)
    (t : Circle) (x : X) :
    A.project n f (A.act t x) = character (n • t) * A.project n f x := by
  let := A.toAddAction
  exact circleFourierComponent_vadd n f t x

theorem project_lipschitz (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    {K : ℝ≥0} (hf : LipschitzWith K f) : LipschitzWith K (A.project n f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFourierComponent n hf A.isometry_act

theorem project_norm_le (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖A.project n f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_circleFourierComponent_le n f hf x

theorem project_equivariant (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    (g : X → X) (z : ℂ) (hg : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.project n f (g x) = z * A.project n f x := by
  unfold project circleFourierComponent
  change (∫ t : Circle, character ((-n) • t) * f (A.act t (g x)) ∂circleHaar) =
    z * (∫ t : Circle, character ((-n) • t) * f (A.act t x) ∂circleHaar)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hg, hf]
  ring

theorem project_eq_at (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ) (x : X)
    (hx : ∀ t, f (A.act t x) = character (n • t) * f x) : A.project n f x = f x := by
  unfold project circleFourierComponent
  change (∫ t : Circle, character ((-n) • t) * f (A.act t x) ∂circleHaar) = _
  have heq (t : Circle) : character ((-n) • t) * f (A.act t x) = f x := by
    rw [hx, ← mul_assoc, ← character_add, ← add_smul]
    simp only [neg_add_cancel, zero_smul, character_zero, one_mul]
  simp_rw [heq]
  simp

end Erdos3.CircleFourier.IsometricCircleAction

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedExactProjection (A : α → IsometricCircleAction X) (n : α → ℤ) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).project (n i) (iteratedExactProjection A n is f)

theorem iteratedExactProjection_lipschitz (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) {f : X → ℂ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (iteratedExactProjection A n is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).project_lipschitz (n i) ih

theorem iteratedExactProjection_norm_le (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) {f : X → ℂ} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedExactProjection A n is f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).project_norm_le (n i) ih

theorem iteratedExactProjection_character (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : α) (hj : j ∈ is) (t : Circle) (x : X) :
    iteratedExactProjection A n is f ((A j).act t x) =
      character (n j • t) * iteratedExactProjection A n is f x := by
  induction is generalizing x with
  | nil => simp only [List.not_mem_nil] at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · exact (A j).project_character (n j) _ t x
    · apply (A i).project_equivariant (n i) ((A j).act t) (character (n j • t))
      · exact fun u y => hcomm i List.mem_cons_self j (List.mem_cons_of_mem i hj) u t y
      · intro y
        exact ih (fun a ha b hb => hcomm a (List.mem_cons_of_mem i ha) b
          (List.mem_cons_of_mem i hb)) hj y

theorem iteratedExactProjection_eq_on (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) (S : Set X) (f : X → ℂ)
    (hstable : ∀ i ∈ is, ∀ t x, x ∈ S → (A i).act t x ∈ S)
    (hchar : ∀ i ∈ is, ∀ t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x) :
    ∀ x ∈ S, iteratedExactProjection A n is f x = f x := by
  induction is with
  | nil => exact fun _ _ => rfl
  | cons i is ih =>
    have htail := ih (fun j hj => hstable j (List.mem_cons_of_mem i hj))
      (fun j hj => hchar j (List.mem_cons_of_mem i hj))
    intro x hx
    change (A i).project (n i) (iteratedExactProjection A n is f) x = f x
    rw [(A i).project_eq_at (n i) _ x]
    · exact htail x hx
    · intro t
      rw [htail _ (hstable i List.mem_cons_self t x hx), htail x hx]
      exact hchar i List.mem_cons_self t x hx

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

theorem exists_prescribed_circle_projection {X α : Type*} [PseudoMetricSpace X] [Fintype α]
    (A : α → IsometricCircleAction X) (n : α → ℤ)
    (hcomm : ∀ i j, (A i).Commutes (A j)) (S : Set X) (f : X → ℂ)
    (hstable : ∀ i t x, x ∈ S → (A i).act t x ∈ S)
    (hchar : ∀ i t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x)
    {K : ℝ≥0} {B : ℝ} (hf : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ B) ∧
      (∀ i t x, g ((A i).act t x) = character (n i • t) * g x) ∧
      ∀ x ∈ S, g x = f x := by
  classical
  let is := (Finset.univ : Finset α).toList
  refine ⟨iteratedExactProjection A n is f, iteratedExactProjection_lipschitz A n is hf,
    iteratedExactProjection_norm_le A n is hb, ?_, ?_⟩
  · intro j t x
    exact iteratedExactProjection_character A n is (fun i _ j _ => hcomm i j) f j
      (by simp [is]) t x
  · exact iteratedExactProjection_eq_on A n is S f (fun i _ => hstable i) (fun i _ => hchar i)

end Erdos3.CircleFourier

end

section

namespace Erdos3.NilpotentLieBCHGroup

open CircleFourier
open scoped NNReal

variable {L ι : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_prescribed_central_projection
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    [PseudoMetricSpace (NilpotentLieBCHGroup L s hnil ⧸ Γ)]
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (u : ι → L) (hline : ∀ i r, realBCHLine (hnil := hnil) (u i) r ∈ T)
    (hspan : ∀ z ∈ T, z.coord ∈ Submodule.span ℝ (Set.range u))
    (A : ι → IsometricCircleAction (NilpotentLieBCHGroup L s hnil ⧸ Γ))
    (hcomm : ∀ i j, (A i).Commutes (A j))
    (hact : ∀ i (r : ℝ) x, (A i).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := hnil) (u i) r • x)
    (η : L →ₗ[ℝ] ℝ) (f : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ)
    (hseed : ∀ z ∈ T, f (QuotientGroup.mk z) = logCharacter η z)
    {K : ℝ≥0} {B : ℝ} (hf : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ,
      LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ B) ∧
      (∀ z ∈ T, ∀ x, g (z • x) = logCharacter η z * g x) ∧
      ∀ z ∈ T, g (QuotientGroup.mk z) = logCharacter η z := by
  classical
  have hperiod (i) : (QuotientGroup.mk (realBCHLine (hnil := hnil) (u i) 1) : _ ⧸ Γ) =
      QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil) := by
    have h := hact i 1 (QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil))
    simpa only [AddCircle.coe_period, (A i).zero_act, MulAction.Quotient.smul_mk,
      smul_eq_mul, mul_one] using h.symm
  have hint (i) : ∃ n : ℤ, η (u i) = n := by
    have he : character (η (u i) : CircleFourier.Circle) = 1 := by
      calc
        _ = f (QuotientGroup.mk (realBCHLine (hnil := hnil) (u i) 1)) := by
          rw [hseed _ (hline i 1)]
          simp only [logCharacter, realBCHLine, one_smul]
        _ = f (QuotientGroup.mk (1 : NilpotentLieBCHGroup L s hnil)) := congrArg f (hperiod i)
        _ = 1 := by rw [hseed _ T.one_mem]; simp only [logCharacter, coord_one, map_zero,
          AddCircle.coe_zero, character_zero]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp ((character_eq_one_iff _).mp he)
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩
  choose n hn using hint
  have hlinechar (i r) : logCharacter η (realBCHLine (hnil := hnil) (u i) r) =
      character (n i • (r : CircleFourier.Circle)) := by
    simp only [logCharacter, realBCHLine, map_smul, smul_eq_mul, hn, ← AddCircle.coe_zsmul,
      zsmul_eq_mul, mul_comm]
  let S : Set (NilpotentLieBCHGroup L s hnil ⧸ Γ) := Set.range (fun z : T => QuotientGroup.mk z.val)
  have hstable : ∀ i t x, x ∈ S → (A i).act t x ∈ S := by
    intro i t x hx
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨z, rfl⟩ := hx
    rw [hact, MulAction.Quotient.smul_mk, smul_eq_mul]
    exact ⟨⟨realBCHLine (u i) r * z.val, T.mul_mem (hline i r) z.property⟩, rfl⟩
  have hchar : ∀ i t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x := by
    intro i t x hx
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨z, rfl⟩ := hx
    rw [hact, MulAction.Quotient.smul_mk, smul_eq_mul,
      hseed _ (T.mul_mem (hline i r) z.property), hseed _ z.property,
      logCharacter_mul η _ _ (hT _ (hline i r) z.val.coord), hlinechar]
  obtain ⟨g, hg, hgb, hgchar, hgeq⟩ :=
    exists_prescribed_circle_projection A n hcomm S f hstable hchar hf hb
  refine ⟨g, hg, hgb, ?_, fun z hz => (hgeq _ ⟨⟨z, hz⟩, rfl⟩).trans (hseed z hz)⟩
  intro z hz x
  apply central_span_character u (fun i v => ?_) η g (fun i r y => ?_) (hspan z hz) x
  · simpa only [realBCHLine, one_smul] using hT _ (hline i 1) v
  · have h := hgchar i (r : CircleFourier.Circle) y
    rw [hact, ← hlinechar] at h
    simpa only [logCharacter, realBCHLine, map_smul, smul_eq_mul] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

theorem exists_native_prescribed_projection {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (f : D.Space → ℂ) {K : ℝ≥0} {B : ℝ}
    (hf : letI := D.metricSpace; LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B)
    (hseed : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
      f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z) :
    ∃ g : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K g) ∧
      (∀ x, ‖g x‖ ≤ B) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
        g (z • x) = logCharacter (realifyFunctional η) z * g x) ∧
      g (QuotientGroup.mk (1 : D.RealGroup)) = 1 := by
  let := D.metricSpace
  obtain ⟨b, w, N, hlayers, _, _, hN, _, _, _, A, hcomm, _, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let u (j : S) := (N : ℝ) • b.baseChange ℝ j
  have hbReal (j : S) : b.baseChange ℝ j ∈ D.filtration.realLayer s := by
    rw [Basis.baseChange_apply]
    change rationalLieInclusion (b j) ∈ D.filtration.realLayer s
    apply D.filtration.rational_inclusion_mem_realLayer
    rw [hlayers s]
    exact Submodule.subset_span ⟨j, j.property, rfl⟩
  have hline (j : S) (r : ℝ) : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (u j) r ∈ D.filtration.realification.subgroup s := by
    change r • ((N : ℝ) • b.baseChange ℝ j) ∈ D.filtration.realLayer s
    exact (D.filtration.realLayer s).smul_mem r ((D.filtration.realLayer s).smul_mem _ (hbReal j))
  obtain ⟨g, hg, hgb, hgvert, hgeq⟩ := exists_prescribed_central_projection
    D.realLattice (D.filtration.realification.subgroup s)
    (fun z hz v => D.filtration.realification.top_layer_central hz v) u hline
    (fun z hz => D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz)
    A hcomm hact (realifyFunctional η) f hseed hf hb
  refine ⟨g, hg, hgb, hgvert, ?_⟩
  have h := hgeq 1 (D.filtration.realification.subgroup s).one_mem
  simpa only [logCharacter, coord_one, map_zero, AddCircle.coe_zero, CircleFourier.character_zero] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
