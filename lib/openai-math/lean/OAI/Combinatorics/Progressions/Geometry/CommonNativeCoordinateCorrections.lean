import OAI.Combinatorics.Progressions.Estimates.CommonUniformCoefficientCorrections
import OAI.Combinatorics.Progressions.Linear.RankHorizontalRepresentatives
import OAI.Combinatorics.Progressions.Linear.RankNativeCoordinates

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem spaces_le_fourHorizontalLayer (d : Fin (s + 1)) :
    D.spaces d ≤ W.rank.filtration.fourHorizontalLayer d.val := by
  obtain ⟨t, ht⟩ := D.nonempty
  rw [← D.projection t ht d]
  let I := R.interval ⟨t, D.subset ht⟩
  let V : I.SunflowerWitness P := D.witness t ht
  change I.refilteredProjectionImage V.index V.subalgebra d.val ≤ _
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (W.rank.filtration.mem_fourHorizontalLayer d.val _).mpr
    (I.rankProjection_mem_refiltered V.index V.subalgebra d.val y hy)

noncomputable def coordinateSpace (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    Submodule ℚ (Fin 4 → κ → ℚ) :=
  (D.horizontal d).map (W.rank.filtration.fourHorizontalCoordinates d.val f)

theorem coordinateSpace_eq_map (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    D.coordinateSpace d f = (D.spaces d).map (W.rank.filtration.fourAmbientCoordinates d.val f) :=
  W.rank.filtration.horizontalImage_coordinates d.val f (D.spaces d) (D.spaces_le_fourHorizontalLayer d)

theorem exists_coordinate_generators (hP : 0 ≤ P) (d : Fin (s + 1))
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) {K : ℕ}
    (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer d.val 2).mkQ (W.model.basis j)) i) K) :
    ∃ v : Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim)) → (Fin 4 → κ → ℚ),
      Submodule.span ℚ (Set.range v) = D.coordinateSpace d f ∧
      ∀ a k i, RationalHeightLE (v a k i)
        ((W.dim + 1) * (⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ * K) ^ W.dim) := by
  obtain ⟨v, hspan, hv⟩ := (mem_heightBoundedSubspaces W.fourRankBasis _ _ _).mp
    (D.spaces_mem_candidates hP d)
  let φ := W.rank.filtration.fourAmbientCoordinates d.val f
  refine ⟨fun a => φ (v a), ?_, ?_⟩
  · rw [D.coordinateSpace_eq_map, ← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro a k i
    have hv' (j : Fin 4) (l : Fin W.dim) :
        RationalHeightLE (W.model.basis.repr (v a j) l)
          ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
      simpa only [NativeDegreeRankFamily.fourRankBasis, Pi.basis_repr] using hv a ⟨j, l⟩
    simpa only [Fintype.card_fin] using W.rank.filtration.fourAmbientCoordinates_height
      d.val f W.model.basis hf (v a) hv' k i

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_bounded_coordinate_generators (D : R.CommonData P) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) (hd : 1 ≤ d.val) :
    ∃ m : ℕ, m ≤ W.dim ∧ ∃ f : Basis (Fin m) ℚ (W.L ⧸ W.rank.filtration.layer d.val 2),
      (∀ i j, rationalLogHeight (f.repr ((W.rank.filtration.layer d.val 2).mkQ (W.model.basis j)) i) ≤
        (P + 3) ^ 7) ∧
      ∃ v : Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim)) → (Fin 4 → Fin m → ℚ),
        Submodule.span ℚ (Set.range v) = D.coordinateSpace d f ∧
        ∀ a k i, rationalLogHeight (v a k i) ≤ horizontalCoordinateBudget P := by
  obtain ⟨K, hK, hKp, m, hm, f, hf⟩ :=
    W.rank.exists_horizontal_ambient_basis d hd hP (W.complexity.mono W.rank hbP)
  obtain ⟨v, hv, hheight⟩ := D.exists_coordinate_generators hP d f hf
  have hdim : (W.dim : ℝ) ≤ P := W.complexity.1.1.trans hbP
  have hbound := horizontalCoordinateHeight_bound hP W.dim
    ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ K hdim
    (ceil_exp_le_exp_add_one (refiltrationCoordinateBudget_nonneg hP)) hKp
  refine ⟨m, hm, f, (fun i j => rationalLogHeight_le_of_height (hf i j) hKp), v, hv, ?_⟩
  intro a k i
  exact rationalLogHeight_le_of_height (hheight a k i) hbound

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (d : Fin (s + 1)) (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))

noncomputable def realCoordinateSpace : Submodule ℝ ((Σ _ : Fin 4, κ) → ℝ) :=
  ((D.coordinateSpace d f).baseChange ℝ).map
    (DegreeRankLieFiltration.realFourCoordinateEquiv (ι := κ)).toLinearMap

theorem realCoordinateSpace_eq_image :
    D.realCoordinateSpace d f =
      ((D.horizontal d).baseChange ℝ).map (W.rank.filtration.realFourHorizontalCoordinates d.val f) :=
  (W.rank.filtration.realFourHorizontalCoordinates_image d.val f (D.horizontal d)).symm

theorem realCoordinateSpace_mem
    (x : (W.rank.filtration.fourHorizontalLayer d.val).baseChange ℝ)
    (hx : W.rank.filtration.realFourHorizontalMap d.val x ∈ (D.horizontal d).baseChange ℝ) :
    W.rank.filtration.realFourAmbientCoordinates d.val f x.val ∈ D.realCoordinateSpace d f := by
  rw [D.realCoordinateSpace_eq_image, ← W.rank.filtration.realFourHorizontalCoordinates_map d.val f x]
  exact ⟨_, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_coordinate_corrections (D : R.CommonData P) (hs : 1 ≤ s) (hP : 0 ≤ P)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : (Σ _ : Fin 4, κ) → ℝ,
      (∀ j, |E j| ≤ ((W.dim : ℝ) + 1) * (K + 1) *
        (Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α)) ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * V.projectedDenominator) ∧
      W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
          (V.projectedOrbitCoefficient α).val - E - Q ∈
        D.realCoordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  let φ := W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
  refine ⟨φ (E α).val, φ (Q α).val, ?_, ?_, ?_⟩
  · intro j
    have hscale := monomialScale_pos (fun _ : Unit => (I.length : ℝ))
      (fun _ => by exact_mod_cast I.length_pos) α
    have hbound := W.rank.filtration.realFourAmbientCoordinates_bound
      (Finsupp.weight (fun _ : Unit => 1) α) f W.model.basis hf (E α).val
      (div_nonneg (Real.exp_pos _).le hscale.le) (hE α) j.1 j.2
    simpa only [Fintype.card_fin] using hbound
  · exact W.rank.filtration.realFourAmbientCoordinates_grid
      (Finsupp.weight (fun _ : Unit => 1) α) f W.model.basis V.projectedDenominator (Q α).val (hQ α)
  · have h := D.realCoordinateSpace_mem
      ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
      (V.projectedOrbitCoefficient α - E α - Q α) (hres α hα)
    change φ ((V.projectedOrbitCoefficient α).val - (E α).val - (Q α).val) ∈ _ at h
    simpa only [map_sub] using h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_uniform_native_coordinate_corrections
    (D : R.CommonData P) (hs : 1 ≤ s) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i})) :
    let B := (P + 2) ^ 3 + 2 * P
    ∃ (C : R.CommonData B) (l : ℕ), C.quadruples ⊆ D.quadruples ∧ C.spaces = D.spaces ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
        (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
        (K : ℕ),
        (∀ i j, RationalHeightLE
          (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ
            (W.model.basis j)) i) K) →
        ∀ t (ht : t ∈ C.quadruples),
          let I := R.interval ⟨t, C.subset ht⟩
          ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
            (∀ j, |E j| ≤ ((W.dim : ℝ) + 1) * (K + 1) *
              (Real.exp ((B + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α)) ∧
            Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l) ∧
            ((fun j : Σ _ : Fin 4, ι => (f.baseChange ℝ).repr
              ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
                (W.horizontalCoefficient hs c τ hG α
                  (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1)))) j.2) - E - Q) ∈
              realFourCoordinateSpan
                (C.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f) := by
  intro B
  obtain ⟨C, l, hCD, hspaces, hl, hlp, hdenom⟩ := D.exists_common_projected_denominator hP
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨C, l, hCD, hspaces, hl, hlp, ?_⟩
  intro α hα f K hf t ht I
  obtain ⟨E, Q, hE, hQ, hres⟩ := C.exists_coordinate_corrections hs hB t ht α hα f hf
  refine ⟨E, Q, hE, ?_, ?_⟩
  · change Q ∈ realDenominatorGrid
      (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * (C.witness t ht).projectedDenominator) at hQ
    simpa only [hdenom t ht] using hQ
  · have hcoeff : W.rank.filtration.realFourAmbientCoordinates
        (Finsupp.weight (fun _ : Unit => 1) α) f ((C.witness t ht).projectedOrbitCoefficient α).val =
        (fun j : Σ _ : Fin 4, ι => (f.baseChange ℝ).repr
          ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
            (W.horizontalCoefficient hs c τ hG α
              (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1)))) j.2) := by
      funext j
      exact (C.witness t ht).projectedOrbitCoefficient_native_coordinates hs c τ hG α f j.1 j.2
    rw [hcoeff] at hres
    exact hres

end Erdos3.NativeRankRelation.CommonData

end

end OAI
