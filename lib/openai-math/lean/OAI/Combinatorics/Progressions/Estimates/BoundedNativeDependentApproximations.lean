import OAI.Combinatorics.Progressions.Estimates.FiniteFourPointAnchors
import OAI.Combinatorics.Progressions.Geometry.CommonNativeCoordinateCorrections
import OAI.Combinatorics.Progressions.Geometry.DependentCoordinateCorrections
import OAI.Combinatorics.Progressions.Linear.RankSparseFamilies

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

def fourSparseAnchorChange (h : G) : (G × G) ≃ (G × G) where
  toFun u := (u.1, u.1 - u.2 + h)
  invFun u := (u.1, u.1 - u.2 + h)
  left_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · dsimp
      abel_nf
  right_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · dsimp
      abel_nf

theorem exists_simultaneous_four_point_anchors (T : Finset (G × G × G)) {δ : ℝ}
    (hδ : 0 < δ) (hsize : δ * (Fintype.card G : ℝ) ^ 3 ≤ T.card) :
    ∃ (a b c d : G) (S : Finset G), S.Nonempty ∧
      δ ^ 2 * Fintype.card G ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, (b - h, b, a) ∈ T ∧ (c - d, h + (c - d), c) ∈ T := by
  classical
  let w (t : G × G × G) : ℝ := if t ∈ T then 1 else 0
  let f (u : G × G) (h : G) := w (u.2 - h, u.2, u.1)
  let g (u : G × G) (h : G) := w (u.1 - u.2, h + (u.1 - u.2), u.1)
  have hmarginal (h : G) : (𝔼 u, f u h) = 𝔼 u, g u h := by
    apply Fintype.expect_equiv (fourSparseAnchorChange h)
    intro u
    change w (u.2 - h, u.2, u.1) =
      w (u.1 - (u.1 - u.2 + h), h + (u.1 - (u.1 - u.2 + h)), u.1)
    congr 1
    apply Prod.ext
    · abel_nf
    · apply Prod.ext
      · abel_nf
      · rfl
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hmean : δ ≤ 𝔼 h, 𝔼 u, f u h := by
    have htotal : δ ≤ 𝔼 t, w t := by
      rw [Fintype.expect_eq_sum_div_card]
      have hsum : (∑ t, w t) = (T.card : ℝ) := by simp [w]
      rw [hsum]
      have hcard : (Fintype.card (G × G × G) : ℝ) = (Fintype.card G : ℝ) ^ 3 := by
        simp only [Fintype.card_prod, Nat.cast_mul]
        ring
      rw [hcard]
      exact (le_div_iff₀ (by positivity)).mpr hsize
    have he : (𝔼 u : (G × G) × G, f u.1 u.2) = 𝔼 t, w t := by
      apply Fintype.expect_equiv (fourSparse12Equiv G).symm
      intro u
      rfl
    have hsplit : (𝔼 u : (G × G) × G, f u.1 u.2) = 𝔼 u, 𝔼 h, f u h := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (G × G)) (Finset.univ : Finset G) f)
    rw [Finset.expect_comm, ← hsplit, he]
    exact htotal
  obtain ⟨⟨a, b⟩, ⟨c, d⟩, hpair⟩ :=
    exists_common_slice_of_equal_marginals f g hδ.le hmarginal hmean
  let S := Finset.univ.filter (fun h => (b - h, b, a) ∈ T ∧ (c - d, h + (c - d), c) ∈ T)
  have hind (h : G) : f (a, b) h * g (c, d) h = if h ∈ S then 1 else 0 := by
    simp only [f, g, w, S, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp_all
  have hSsize : δ ^ 2 * Fintype.card G ≤ (S.card : ℝ) := by
    simp_rw [hind] at hpair
    rw [Fintype.expect_eq_sum_div_card] at hpair
    have hsum : (∑ h : G, if h ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by simp
    rw [hsum] at hpair
    exact (le_div_iff₀ hG).mp hpair
  have hpos : (0 : ℝ) < S.card := (mul_pos (sq_pos_of_pos hδ) hG).trans_le hSsize
  exact ⟨a, b, c, d, S, Finset.card_pos.mp (by exact_mod_cast hpos), hSsize,
    fun h hh => (Finset.mem_filter.mp hh).2⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

structure SparseAnchors (D : R.CommonData P) where
  anchors12 : ZMod N × ZMod N
  anchors13 : ZMod N × ZMod N
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-(2 * P)) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  relations : ∀ h ∈ shifts,
    (anchors12.2 - h, anchors12.2, anchors12.1) ∈ D.quadruples ∧
      (anchors13.1 - anchors13.2, h + (anchors13.1 - anchors13.2), anchors13.1) ∈ D.quadruples

theorem exists_sparse_anchors (D : R.CommonData P) : Nonempty D.SparseAnchors := by
  obtain ⟨a, b, c, d, S, hS, hsize, hmem⟩ :=
    exists_simultaneous_four_point_anchors D.quadruples (Real.exp_pos _) D.density
  refine ⟨{
    anchors12 := (a, b)
    anchors13 := (c, d)
    shifts := S
    nonempty := hS
    density := ?_
    relations := hmem }⟩
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_neg] using hsize

namespace SparseAnchors

variable {D : R.CommonData P} (A : D.SparseAnchors)

theorem shifts_subset : A.shifts ⊆ H := by
  intro h hh
  have hmem := (A.relations h hh).1
  have hsecond := (R.interval ⟨_, D.subset hmem⟩).second_mem
  simpa using hsecond

theorem anchors_mem : A.anchors12.1 ∈ H ∧ A.anchors12.2 ∈ H ∧
    A.anchors13.1 ∈ H ∧ A.anchors13.2 ∈ H := by
  obtain ⟨h, hh⟩ := A.nonempty
  have h12 := (A.relations h hh).1
  have h13 := (A.relations h hh).2
  have hfirst := (R.interval ⟨_, D.subset h12⟩).first_mem
  have hthird := (R.interval ⟨_, D.subset h12⟩).third_mem
  have hthird' := (R.interval ⟨_, D.subset h13⟩).third_mem
  have hfourth := (R.interval ⟨_, D.subset h13⟩).fourth_mem
  exact ⟨hthird, hfirst, hthird', by simpa using hfourth⟩

theorem partners_mem (h : ZMod N) (hh : h ∈ A.shifts) :
    A.anchors12.1 - (A.anchors12.2 - h) ∈ H ∧ h + (A.anchors13.1 - A.anchors13.2) ∈ H := by
  exact ⟨(R.interval ⟨_, D.subset (A.relations h hh).1⟩).fourth_mem,
    (R.interval ⟨_, D.subset (A.relations h hh).2⟩).first_mem⟩

end SparseAnchors

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_anchor_representative_corrections
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (n : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) :
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ,
      (∀ α, Finsupp.weight (fun _ : Unit => 1) α ≤ s →
        ‖(W.model.basis.baseChange ℝ).equivFun (E α).val‖ ≤
          Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α) ∧
      (∀ α, (W.model.basis.baseChange ℝ).equivFun (Q α).val ∈ realDenominatorGrid n) ∧
      ∀ α (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        W.horizontalCoefficient hs c τ hG α h₀ -
            W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) (E α) -
            W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) (Q α) ∈
          (fourFirstProjection (D.horizontal
            ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  let t := (A.anchors12.2 - h₀, A.anchors12.2, A.anchors12.1)
  have ht : t ∈ D.quadruples := (A.relations h₀ hh₀).1
  let I := R.interval ⟨t, D.subset ht⟩
  let V : I.SunflowerWitness P := D.witness t ht
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  refine ⟨fun α => W.rank.filtration.realFourLayerComponent _ 0 (E α),
    fun α => W.rank.filtration.realFourLayerComponent _ 0 (Q α), ?_, ?_, ?_⟩
  · intro α hα
    have he := W.rank.filtration.realFourLayerComponent_norm_bound
      (Finsupp.weight (fun _ : Unit => 1) α) W.model.basis 0 (E α)
      (div_nonneg (Real.exp_nonneg _) (monomialScale_pos _
        (fun _ => by exact_mod_cast I.length_pos) α).le) (hE α)
    have hb := I.norm_bound_on_modulus hp α hα (Real.exp_nonneg ((P + 3) ^ 2))
      ((W.model.basis.baseChange ℝ).equivFun
        (W.rank.filtration.realFourLayerComponent _ 0 (E α)).val) he
    rwa [← Real.exp_add] at hb
  · intro α
    have hg := W.rank.filtration.realFourLayerComponent_grid
      (Finsupp.weight (fun _ : Unit => 1) α) W.model.basis 0 (Q α)
      V.projectedDenominator (hQ α)
    simpa only [Basis.equivFun_apply] using
      realDenominatorGrid_subset_of_dvd V.projectedDenominator_pos (hdenom t ht) hg
  · intro α hα
    have hm := real_firstProjection_mem
      (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩) (hres α hα)
    have hfirst : rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) 0) = h₀ := by
      simp [t, rankQuadrupleParameters]
    let φ := ((LinearMap.proj (0 : Fin 4)).baseChange ℝ).comp
      (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α))
    have heq : φ (V.projectedOrbitCoefficient α - E α - Q α) =
        φ (V.projectedOrbitCoefficient α) - φ (E α) - φ (Q α) := by
      exact (map_sub φ (V.projectedOrbitCoefficient α - E α) (Q α)).trans
        (congrArg₂ (· - ·) (map_sub φ (V.projectedOrbitCoefficient α) (E α)) rfl)
    change φ (V.projectedOrbitCoefficient α - E α - Q α) ∈ _ at hm
    rw [heq] at hm
    change (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (V.projectedOrbitCoefficient α)) -
      (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (E α)) -
      (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (Q α)) ∈ _ at hm
    rw [V.projectedOrbitCoefficient_native_component hs c τ hG α 0, hfirst,
      W.rank.filtration.realFourLayerComponent_horizontal,
      W.rank.filtration.realFourLayerComponent_horizontal] at hm
    exact hm

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

noncomputable def nativeCoefficientCoordinates
    {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2)) :
    ZMod N → ι → ℝ :=
  fun h i => (f.baseChange ℝ).repr
    ((W.rank.filtration.higherHorizontalAmbient (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ
      (W.horizontalCoefficient hs c τ hG α h)) i

end NativeDegreeRankFamily

namespace NativeRankRelation.CommonData

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem native_scaled_correction
    (D : R.CommonData P) (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
      ‖E‖ ≤ ((W.dim : ℝ) + 1) * (K + 1) *
        (Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α) ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l) ∧
      rankCoordinateTuple β t - E - Q ∈ realFourCoordinateSpan
        (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f) := by
  intro β
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_coordinate_corrections hs hP t ht α hα f hf
  let I := R.interval ⟨t, D.subset ht⟩
  let M : ℝ := ((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hnorm : ‖E‖ ≤ M / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hM
      (monomialScale_pos _ (fun _ => hlength) α).le)).mpr
    intro j
    simpa only [Real.norm_eq_abs, M, mul_div_assoc] using hE j
  refine ⟨E, Q, ?_, ?_, ?_⟩
  · have h := I.norm_bound_on_modulus hp α hα hM E hnorm
    simpa only [M, Real.exp_add, mul_div_assoc, mul_assoc] using h
  · change Q ∈ realDenominatorGrid
      (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * (D.witness t ht).projectedDenominator) at hQ
    simpa only [hdenom t ht] using hQ
  · have hcoeff : W.rank.filtration.realFourAmbientCoordinates
        (Finsupp.weight (fun _ : Unit => 1) α) f ((D.witness t ht).projectedOrbitCoefficient α).val =
        rankCoordinateTuple β t := by
      funext j
      exact (D.witness t ht).projectedOrbitCoefficient_native_coordinates hs c τ hG α f j.1 j.2
    rw [hcoeff] at hres
    exact hres

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_native_sparse_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (v : ν → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) =
      D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)
    {JH : ℕ} (hJH : 1 ≤ JH) (hvH : ∀ a k i, RationalHeightLE (v a k i) JH)
    {z : ℝ} (hz : 0 ≤ z) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ z)
    (hcols : (Fintype.card ν : ℝ) ≤ z) (hJHz : (JH : ℝ) ≤ Real.exp z)
    (hlz : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤ Real.exp z)
    (hslow : 2 * (((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤ Real.exp z)
    (hN : Real.exp (separationBudget z) ≤ N) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    let J := D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36))) ∧
      matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l ∣ m ∧
      ∀ h ∈ A.shifts, ∃ e₁₂ q₁₂ e₁₃ q₁₃ : ι → ℝ,
        ‖e₁₂‖ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧
        ‖e₁₃‖ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧
        q₁₂ ∈ realDenominatorGrid m ∧ q₁₃ ∈ realDenominatorGrid m ∧
        β h - β h₀ - e₁₂ - q₁₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) ∧
        β h - β h₀ - e₁₃ - q₁₃ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) := by
  intro β J
  let M : ℝ := ((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)
  have hcorrect (t) (ht : t ∈ D.quadruples) : ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
      ‖E‖ ≤ M / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l) ∧
      rankCoordinateTuple β t - E - Q ∈ realFourCoordinateSpan J := by
    obtain ⟨E, Q, hE, hQ, hres⟩ := D.native_scaled_correction hs hp hP c τ hG l hdenom α hα f hf t ht
    exact ⟨E, Q, by simpa only [M, mul_div_assoc] using hE, hQ, hres⟩
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_rank_sparse_family A.shifts h₀ hh₀ J v hv hJH
    (Nat.mul_pos (matrixDenominator_pos _) hl) hvH hz hfour hcols hJHz hlz
    (fun _ : Unit => (N : ℝ)) (fun _ => hN)
  refine ⟨m, hm, hmp, hlm, ?_⟩
  exact hsolve α hα₀ β A.anchors12.1 A.anchors12.2 A.anchors13.1 A.anchors13.2 M hslow
    (fun h hh => hcorrect _ (A.relations h hh).1)
    (fun h hh => hcorrect _ (A.relations h hh).2)

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_native_dependent_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (v : ν → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) =
      D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)
    {JH : ℕ} (hJH : 1 ≤ JH) (hvH : ∀ a k i, RationalHeightLE (v a k i) JH)
    {z : ℝ} (hz : 0 ≤ z) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ z)
    (hcols : (Fintype.card ν : ℝ) ≤ z) (hJHz : (JH : ℝ) ≤ Real.exp z)
    (hlz : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤ Real.exp z)
    (hslow : 2 * (((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤ Real.exp z)
    (hN : Real.exp (separationBudget z) ≤ N)
    (hNdep : Real.exp (separationBudget
      (rankDependentInputBudget z + sparseGeneratorBudget (rankDependentInputBudget z))) ≤ N) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    let J := D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    let Z := rankDependentInputBudget z
    let Q := Z + sparseGeneratorBudget Z
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (Q + ((Q + 2) ^ 3 + (Q + 2) ^ 36)) ∧
      matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l ∣ m ∧
      ∀ h ∈ A.shifts, ∃ e q : ι → ℝ,
        ‖e‖ ≤ (Real.exp Q + Real.exp ((Q + 2) ^ 3 + (Q + 2) ^ 18 + Q)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧ q ∈ realDenominatorGrid m ∧
        β h - β h₀ - e - q ∈ realRationalCoordinateSpan (fourDependentProjection J) := by
  intro β J Z Q
  obtain ⟨m₀, hm₀, hmp₀, hdiv₀, hpairs⟩ := A.exists_native_sparse_approximations h₀ hh₀
    hs hp hP c τ hG l hl hdenom α hα hα₀ f hf v hv hJH hvH hz hfour hcols hJHz hlz hslow hN
  obtain ⟨hZ, hzZ, h2zZ, hdenZ, hslowZ⟩ := rankDependentInputBudget_bounds hz
  have hZQ : Z ≤ Q := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hZ)
  have hdim : (Fintype.card ι : ℝ) ≤ z := by
    have hcard : Fintype.card ι ≤ Fintype.card (Σ _ : Fin 4, ι) :=
      Fintype.card_le_of_injective (fun i : ι => (⟨0, i⟩ : Σ _ : Fin 4, ι))
        (fun _ _ h => congrArg (fun j : Σ _ : Fin 4, ι => j.2) h)
    exact (Nat.cast_le.mpr hcard).trans hfour
  have hselected (K : Finset (Fin 4)) : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ Z :=
    ((Nat.cast_le.mpr (card_selected_four_le K)).trans hfour).trans hzZ
  have hdoublecols : (Fintype.card (ν ⊕ ν) : ℝ) ≤ Z := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  obtain ⟨m, hm, hmp, hdiv, hsolve⟩ := exists_dependent_coordinate_corrections J v hv hJH hm₀ hvH
    hZ (hdim.trans hzZ) (hselected _) (hselected _) hdoublecols
    (hJHz.trans (Real.exp_le_exp.mpr hzZ)) (hmp₀.trans (Real.exp_le_exp.mpr hdenZ))
    (fun _ : Unit => (N : ℝ)) (fun _ => hNdep)
  refine ⟨m, hm, hmp, hdiv₀.trans hdiv, ?_⟩
  intro h hh
  obtain ⟨e₁, q₁, e₂, q₂, he₁, he₂, hq₁, hq₂, hres₁, hres₂⟩ := hpairs h hh
  have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) α :=
    monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α
  have hcost : 2 * (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) ≤ Real.exp Q :=
    hslowZ.trans (Real.exp_le_exp.mpr hZQ)
  have hsingle : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤ Real.exp Q := by
    linarith [Real.exp_pos z, Real.exp_pos ((z + 2) ^ 3 + (z + 2) ^ 18 + z)]
  have hfirst : ‖e₁‖ ≤ Real.exp Q / monomialScale (fun _ : Unit => (N : ℝ)) α :=
    he₁.trans (div_le_div_of_nonneg_right hsingle hscale.le)
  have hdiff : ‖e₂ - e₁‖ ≤ Real.exp Q / monomialScale (fun _ : Unit => (N : ℝ)) α := by
    calc
      ‖e₂ - e₁‖ ≤ ‖e₂‖ + ‖e₁‖ := norm_sub_le _ _
      _ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
            monomialScale (fun _ : Unit => (N : ℝ)) α +
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
            monomialScale (fun _ : Unit => (N : ℝ)) α := add_le_add he₂ he₁
      _ = (2 * (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) /
          monomialScale (fun _ : Unit => (N : ℝ)) α := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hcost hscale.le
  exact hsolve α hα₀ (β h - β h₀) e₁ e₂ q₁ q₂ hres₁ hres₂ hfirst hdiff hq₁ hq₂

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_bounded_native_dependent_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l) (hlP : (l : ℝ) ≤ Real.exp P)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    ∃ m : ℕ, m ≤ W.dim ∧
      ∃ f : Basis (Fin m) ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2),
        (∀ i j, rationalLogHeight
          (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) ≤
          (P + 3) ^ 7) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp (nativeDependentDenominatorBudget s P) ∧ l ∣ n ∧
          ∀ h ∈ A.shifts, ∃ e q : Fin m → ℝ,
            ‖e‖ ≤ Real.exp (nativeDependentSlowBudget s P) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
            q ∈ realDenominatorGrid n ∧
            W.nativeCoefficientCoordinates hs c τ hG α f h -
                W.nativeCoefficientCoordinates hs c τ hG α f h₀ - e - q ∈
              realRationalCoordinateSpan (fourDependentProjection
                (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)) := by
  have heval : α () ≠ 0 := by
    intro hzero
    apply hα₀
    apply Finsupp.ext
    intro u
    cases u
    exact hzero
  let d : Fin (s + 1) := ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩
  have hd : 1 ≤ d.val := Finsupp.le_weight_of_ne_zero' (fun _ : Unit => 1) heval
  obtain ⟨m, hm, f, hf, v, hv, hvH⟩ := D.exists_bounded_coordinate_generators hP hbP d hd
  let K := ⌈Real.exp ((P + 3) ^ 7)⌉₊
  let JH := ⌈Real.exp (horizontalCoordinateBudget P)⌉₊
  let z := nativeCoordinateInputBudget s P
  have hdim : (W.dim : ℝ) ≤ P := W.complexity.1.1.trans hbP
  have hK : (K : ℝ) ≤ Real.exp ((P + 3) ^ 7 + 1) := ceil_exp_le_exp_add_one (by positivity)
  obtain ⟨_, h4PU, _, _, hGU, _⟩ := nativeCoordinateBaseBudget_bounds s hP
  have hUz := (nativeCoordinateInputBudget_bounds s hP).1
  have hcount (a : ℕ) (ha : a ≤ W.dim) : (Fintype.card (Σ _ : Fin 4, Fin a) : ℝ) ≤ z := by
    have haP : (a : ℝ) ≤ P := (Nat.cast_le.mpr ha).trans hdim
    have h4 : 4 * (a : ℝ) ≤ z :=
      (mul_le_mul_of_nonneg_left haP (by norm_num : (0 : ℝ) ≤ 4)).trans (h4PU.trans hUz)
    simpa [Fintype.card_sigma] using h4
  have hJHz : (JH : ℝ) ≤ Real.exp z :=
    (ceil_exp_le_exp_add_one (horizontalCoordinateBudget_nonneg hP)).trans
      (Real.exp_le_exp.mpr (hGU.trans hUz))
  have hden : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤
      Real.exp z := nativeCoordinate_denominator_bound s hP _ l hlP
        (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hm).trans hdim)
        (by simpa only [Fintype.card_fin] using hdim) hf
  obtain ⟨hN₁, hN₂⟩ := nativeCoordinateSeparationBudget_cutoffs s hP hN
  obtain ⟨n, hn, hnp, hln, hsolve⟩ := A.exists_native_dependent_approximations h₀ hh₀ hs hp hP
    c τ hG l hl hdenom α hα hα₀ f (fun i j => rationalHeightLE_ceil_exp (hf i j))
    v hv (one_le_ceil_exp _) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    (nativeCoordinateInputBudget_nonneg s hP) (hcount m hm)
    (by simpa only [Fintype.card_fin] using hcount W.dim le_rfl) hJHz hden
    (nativeCoordinate_slow_bound s hP hpP W.dim K hdim hK) hN₁ hN₂
  refine ⟨m, hm, f, hf, n, hn, ?_, (dvd_mul_left l _).trans hln, ?_⟩
  · simpa only [nativeDependentDenominatorBudget, nativeDependentBudget, add_assoc] using hnp
  · intro h hh
    obtain ⟨e, q, he, hq, hres⟩ := hsolve h hh
    refine ⟨e, q, ?_, hq, hres⟩
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) α :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α
    exact he.trans (div_le_div_of_nonneg_right (nativeDependentSlowBudget_bound s hP) hscale.le)

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

end OAI
