import OAI.Combinatorics.Progressions.Estimates.CommonFreeSunflower
import OAI.Combinatorics.Progressions.Nilpotent.FreeDegreeRankNilmanifold

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}

structure FreeCoordinateFrame
    (b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
      (FreeDegreeRankLieAlgebra X s r w hw)) (p : ℝ) where
  tree_height : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
    rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ p
  sourceBasis : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ
    (FreeNilpotentLieAlgebra X s)
  sourceBasis_trees : ∀ i, sourceBasis i ∈ FreeNilpotentLieAlgebra.treeGenerators X s
  sourceDimension : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ p
  sectionMatrix : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
    (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
  section_right_inverse : LinearMap.toMatrix sourceBasis b
    (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * sectionMatrix = 1
  section_height : ∀ i j, rationalLogHeight (sectionMatrix i j) ≤ p

namespace FreeCoordinateFrame

variable {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
    (FreeDegreeRankLieAlgebra X s r w hw)} {p q : ℝ}

def mono (F : FreeCoordinateFrame b p) (hpq : p ≤ q) : FreeCoordinateFrame b q where
  tree_height x hx i := (F.tree_height x hx i).trans hpq
  sourceBasis := F.sourceBasis
  sourceBasis_trees := F.sourceBasis_trees
  sourceDimension := F.sourceDimension.trans hpq
  sectionMatrix := F.sectionMatrix
  section_right_inverse := F.section_right_inverse
  section_height i j := (F.section_height i j).trans hpq

end FreeCoordinateFrame
end Erdos3

end

section

namespace Erdos3

open Module

theorem FreeNilpotentLieAlgebra.of_mem_treeGenerators
    (X : Type*) [Fintype X] (s : ℕ) (hs : 1 ≤ s) (x : X) :
    FreeNilpotentLieAlgebra.of X s x ∈ FreeNilpotentLieAlgebra.treeGenerators X s := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨FreeMagma.of x, Finset.mem_filter.mpr ⟨?_, hs⟩, rfl⟩
  exact mem_finiteLieTrees_of_length_le X (FreeMagma.of x) hs

theorem FreeCoordinateFrame.generator_height
    {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}
    {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
      (FreeDegreeRankLieAlgebra X s r w hw)} {p : ℝ}
    (F : FreeCoordinateFrame b p) (hs : 1 ≤ s) (x : X) (i) :
    rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.of X s r w hw x) i) ≤ p :=
  F.tree_height (FreeNilpotentLieAlgebra.of X s x)
    (FreeNilpotentLieAlgebra.of_mem_treeGenerators X s hs x) i

theorem exists_submodule_basis_of_spanning_logHeight
    {V ι κ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (e : Basis ι ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {p : ℝ}
    (hv : ∀ a i, rationalLogHeight (e.repr (v a) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p := by
  classical
  let : FiniteDimensional ℚ V := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro a i
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz a
  rw [← hk]
  exact hv k i

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_petalComparisonSpace_basis_logHeight
    {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]
    (e : Basis μ ℚ V) (C P K : Submodule ℚ V)
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (p : Basis (Fin (finrank ℚ P)) ℚ P)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {q : ℝ} (hq : 0 ≤ q)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ q)
    (hp : ∀ a i, rationalLogHeight (e.repr (p a : V) i) ≤ q)
    (hk : ∀ a i, rationalLogHeight (e.repr (k a : V) i) ≤ q) :
    ∃ b : Basis (Fin (finrank ℚ (petalComparisonSpace C P K))) ℚ (petalComparisonSpace C P K),
      ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => e)).repr (b a : Fin 2 → V) i) ≤ q := by
  classical
  let Δ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.pi (fun _ => LinearMap.id)
  let S₀ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.single ℚ (fun _ : Fin 2 => V) 0
  let S₁ : V →ₗ[ℚ] (Fin 2 → V) := LinearMap.single ℚ (fun _ : Fin 2 => V) 1
  have hspace : petalComparisonSpace C P K =
      (C.map Δ ⊔ P.map S₀) ⊔ (K.map S₀ ⊔ K.map S₁) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, u, hu, v, hv, h₀, h₁⟩ := petalComparisonSpace_decompose C P K x hx
      have hh : (Δ a + S₀ b) + (S₀ u + S₁ v) ∈
          (C.map Δ ⊔ P.map S₀) ⊔ (K.map S₀ ⊔ K.map S₁) :=
        Submodule.add_mem_sup (Submodule.add_mem_sup ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
          (Submodule.add_mem_sup ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩)
      convert hh using 1
      ext i
      fin_cases i <;> simp [Δ, S₀, S₁, LinearMap.single_apply, h₀, h₁]
    · apply sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [Δ] using And.intro (Submodule.mem_sup_left ha)
          ((P ⊔ K).zero_mem)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₀, LinearMap.single_apply] using
          And.intro ((C ⊔ K).zero_mem) (Submodule.mem_sup_left ha)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₀, LinearMap.single_apply] using
          And.intro ((C ⊔ K).zero_mem) (Submodule.mem_sup_right ha)
      · rintro x ⟨a, ha, rfl⟩
        apply (mem_petalComparisonSpace C P K _).mpr
        simpa [S₁, LinearMap.single_apply] using
          And.intro (Submodule.mem_sup_right ha) (Submodule.mem_sup_right (K.neg_mem ha))
  have hspan (U : Submodule ℚ V) (b : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (b j : V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ b)) = U
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hmap (U : Submodule ℚ V) (b : Basis (Fin (finrank ℚ U)) ℚ U)
      (φ : V →ₗ[ℚ] (Fin 2 → V)) :
      Submodule.span ℚ (Set.range (fun j => φ (b j : V))) = U.map φ := by
    change Submodule.span ℚ (Set.range (φ ∘ fun j => (b j : V))) = _
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  let v := Sum.elim (Sum.elim (fun j => Δ (c j : V)) (fun j => S₀ (p j : V)))
    (Sum.elim (fun j => S₀ (k j : V)) (fun j => S₁ (k j : V)))
  have hv : Submodule.span ℚ (Set.range v) = petalComparisonSpace C P K := by
    dsimp only [v]
    rw [span_range_sumElim, span_range_sumElim, span_range_sumElim,
      hmap, hmap, hmap, hmap, hspace]
  have hsingle (j : Fin 2) (x : V) (hx : ∀ i, rationalLogHeight (e.repr x i) ≤ q)
      (i : Σ _ : Fin 2, μ) :
      rationalLogHeight ((Pi.basis (fun _ : Fin 2 => e)).repr
        (LinearMap.single ℚ (fun _ : Fin 2 => V) j x) i) ≤ q := by
    rcases i with ⟨i, a⟩
    by_cases hji : j = i
    · subst i
      simpa [Pi.basis_repr, LinearMap.single_apply] using hx a
    · simpa [Pi.basis_repr, LinearMap.single_apply, hji, Ne.symm hji, rationalLogHeight] using hq
  apply exists_submodule_basis_of_spanning_logHeight (Pi.basis (fun _ : Fin 2 => e)) _ v hv
  intro j i
  cases j with
  | inl j =>
    cases j with
    | inl j => simpa [v, Δ, Pi.basis_repr] using hc j i.2
    | inr j => exact hsingle 0 (p j) (hp j) i
  | inr j =>
    cases j with
    | inl j => exact hsingle 0 (k j) (hk j) i
    | inr j => exact hsingle 1 (k j) (hk j) i

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def coefficientFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  D.commonFreeSpan d ⊔ D.dependentFreeSpan d

theorem commonFreeSpan_le_coefficientFreeSpan (d : Fin s) :
    D.commonFreeSpan d ≤ D.coefficientFreeSpan d := le_sup_left

theorem dependentFreeSpan_le_coefficientFreeSpan (d : Fin s) :
    D.dependentFreeSpan d ≤ D.coefficientFreeSpan d := le_sup_right

theorem coefficientFreeSpan_le_layer (d : Fin s) :
    D.coefficientFreeSpan d ≤ D.coefficientFreeFiltration.layer (d.val + 1) 1 :=
  sup_le (D.commonFreeSpan_le_layer d) (D.dependentFreeSpan_le_layer d)

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_coefficientFreeSpan (d : Fin s) :
    (D.coefficientFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  rw [coefficientFreeSpan, Submodule.map_sup, B.freeEvaluation_commonFreeSpan D,
    B.freeEvaluation_dependentFreeSpan D]
  exact sup_eq_left.mpr (D.dependentCoefficientSpace_le_common _)

theorem CoefficientBases.realEvaluation_coefficientFreeSpan (d : Fin s)
    {x : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra}
    (hx : x ∈ (D.coefficientFreeSpan d).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) x ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
  rw [← B.freeEvaluation_coefficientFreeSpan D d, realification_map]
  exact ⟨x, hx, rfl⟩

theorem CoefficientBases.combined_free_sunflower (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D.coefficientFreeSpan (d i))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ D.dependentFreeSpan (d j)) (hvk : v k ∈ D.dependentFreeSpan (d k)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  have h := D.coefficient_sunflower n (fun i => ⟨(d i).val + 1, by omega⟩) a hd hr
    (fun i => B.freeEvaluation D (v i))
    (fun i => (B.freeEvaluation_coefficientFreeSpan D (d i)).le ⟨v i, hv i, rfl⟩)
    j k hjk hj hk
    ((B.freeEvaluation_dependentFreeSpan D (d j)).le ⟨v j, hvj, rfl⟩)
    ((B.freeEvaluation_dependentFreeSpan D (d k)).le ⟨v k, hvk, rfl⟩)
  change W.vertical.frequency (B.freeEvaluation D (lieTreeEval v a)) = 0
  rw [map_lieTreeEval]
  exact h

theorem CoefficientBases.real_combined_free_sunflower (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ (D.coefficientFreeSpan (d i)).baseChange ℝ)
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ (D.dependentFreeSpan (d j)).baseChange ℝ)
    (hvk : v k ∈ (D.dependentFreeSpan (d k)).baseChange ℝ) :
    realifyFunctional (B.freeFrequency D) (lieTreeEval v a) = 0 := by
  have h := D.real_coefficient_sunflower n (fun i => ⟨(d i).val + 1, by omega⟩) a hd hr
    (fun i => realificationLieHom (B.freeEvaluation D) (v i))
    (fun i => B.realEvaluation_coefficientFreeSpan D (d i) (hv i))
    j k hjk hj hk
    (B.realEvaluation_dependentFreeSpan D (d j) hvj)
    (B.realEvaluation_dependentFreeSpan D (d k) hvk)
  change realifyFunctional (W.vertical.frequency.comp (B.freeEvaluation D).toLinearMap)
    (lieTreeEval v a) = 0
  rw [realifyFunctional_comp]
  exact (congrArg (realifyFunctional W.vertical.frequency)
    (map_lieTreeEval (realLieHomToRat (realificationLieHom (B.freeEvaluation D))) v a)).trans h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_marked_source_basis (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M), 0 ≤ M → b ≤ M →
      ∃ e : Basis (Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) ℚ D.CoefficientFreeLieAlgebra,
        ∃ ω : Fin (finrank ℚ D.CoefficientFreeLieAlgebra) → ℕ,
          (∀ j, D.coefficientFreeFiltration.associatedDegree.layer j =
            Submodule.span ℚ (e '' {i | j ≤ ω i})) ∧
          (∀ i, ω i ≤ s) ∧
          (finrank ℚ D.CoefficientFreeLieAlgebra : ℝ) ≤ (M + C) ^ C ∧
          (∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ (M + C) ^ C) ∧
          (∀ x i, rationalLogHeight (e.repr (D.coefficientFreeGenerator x) i) ≤ (M + C) ^ C) ∧
          ∀ i, rationalLogHeight (B.freeFrequency D (e i)) ≤ (M + C) ^ C := by
  obtain ⟨a, _, hfree⟩ := exists_adapted_free_degree_rank_model s
  let K₀ : Polynomial ℕ := Polynomial.C (2 * s + 1) * Polynomial.X + 1
  let A₀ := (K₀ + Polynomial.C a) ^ a
  let T₀ := Polynomial.X + A₀
  let V₀ := ((T₀ + 3) ^ (6 * s + 2) + T₀ + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A₀ + (T₀ + V₀ + 2) ^ 4)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B hM hbM
  let K := ((2 * s + 1 : ℕ) : ℝ) * M + 1
  let A := (K + a) ^ a
  let T := M + A
  let V := ((T + 3) ^ (6 * s + 2) + T + 2) ^ 4
  let Z := T + V
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := add_nonneg hM hA
  have hMT : M ≤ T := le_add_of_nonneg_right hA
  have hAT : A ≤ T := le_add_of_nonneg_left hM
  have hTZ : T ≤ Z := le_add_of_nonneg_right (by dsimp [V]; positivity)
  have hVZ : V ≤ Z := le_add_of_nonneg_left hT
  have hZ : 0 ≤ Z := hT.trans hTZ
  have hcost : A + (Z + 2) ^ 4 ≤ (M + C) ^ C := by
    simpa [K₀, A₀, T₀, V₀, K, A, T, V, Z, Polynomial.eval₂_pow] using hbudget M hM
  have hAC : A ≤ (M + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (Z + 2) ^ 4)).trans hcost
  have hZC : (Z + 2) ^ 4 ≤ (M + C) ^ C := (le_add_of_nonneg_left hA).trans hcost
  have hdim : (W.dim : ℝ) ≤ M := W.complexity.1.1.trans hbM
  have hX : (Fintype.card D.CoefficientAlphabet : ℝ) ≤ K := by
    calc
      _ ≤ (2 : ℝ) * s * W.dim := by exact_mod_cast D.coefficientAlphabet_card
      _ ≤ (2 : ℝ) * s * M := mul_le_mul_of_nonneg_left hdim (by positivity)
      _ ≤ (2 : ℝ) * s * M + (M + 1) := le_add_of_nonneg_right (by linarith only [hM])
      _ = K := by dsimp [K]; push_cast; ring
  obtain ⟨hd, e, _, htail, hc, htree, e₀, he₀, hd₀, S, hS, hSH⟩ :=
    hfree D.CoefficientAlphabet r W.rank.filtration.rank_le_degree
      D.coefficientWeight D.coefficientWeight_pos K hK hX
  have htail' : ∀ j, ∃ c, D.coefficientFreeFiltration.associatedDegree.layer j = basisTail e c := by
    intro j
    obtain ⟨c, _, hc⟩ := htail j 0
    exact ⟨c, hc⟩
  obtain ⟨ω, hω⟩ := D.coefficientFreeFiltration.associatedDegree.exists_weights_of_tails e htail'
  have hmatrix (i j) : rationalLogHeight (W.model.basis.repr (B.freeEvaluation D (e j)) i) ≤ V := by
    have h := FreeDegreeRankLieAlgebra.lift_basis_matrix_logHeight W.rank.filtration
      D.coefficientWeight D.coefficientWeight_pos (B.generator D) (B.generator_mem_layer D)
      e₀ he₀ e W.model.basis S hS hT (hd₀.trans hAT)
      (by simpa only [Fintype.card_fin] using hdim.trans hMT)
      (fun i j => (hSH i j).trans hAT)
      (fun i j k => (W.complexity.1.2.2.1 i j k).trans (hbM.trans hMT))
      (fun x i => (B.generator_height D x i).trans hMT) i j
    rw [LinearMap.toMatrix_apply] at h
    exact h
  refine ⟨e, ω, hω, D.coefficientFreeFiltration.associatedDegree.adaptedBasis_weight_le_step e ω hω,
    hd.trans hAC, (fun i j k => (hc i j k).trans hAC), ?_, ?_⟩
  · intro x i
    exact (htree (FreeNilpotentLieAlgebra.of D.CoefficientAlphabet s x)
      (FreeNilpotentLieAlgebra.of_mem_treeGenerators D.CoefficientAlphabet s hs x) i).trans hAC
  · intro i
    have h := rational_functional_value_logHeight W.model.basis W.vertical.frequency hZ
      (by simpa only [Fintype.card_fin] using hdim.trans (hMT.trans hTZ))
      (fun j => (W.vertical.height j).trans (hbM.trans (hMT.trans hTZ)))
      (B.freeEvaluation D (e i)) (fun j => (hmatrix j i).trans hVZ)
    exact h.trans hZC

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (e : Basis (Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) ℚ D.CoefficientFreeLieAlgebra)
  {Q : ℝ} (F : FreeCoordinateFrame e Q)

include F

theorem exists_commonFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.commonFreeSpan d))) ℚ (D.commonFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q :=
  exists_submodule_basis_of_spanning_logHeight e _
    (fun a => D.coefficientFreeGenerator (Sum.inl ⟨d, a⟩)) rfl
    (fun a i => F.generator_height hs (Sum.inl ⟨d, a⟩) i)

theorem exists_dependentFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.dependentFreeSpan d))) ℚ (D.dependentFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q :=
  exists_submodule_basis_of_spanning_logHeight e _
    (fun a => D.coefficientFreeGenerator (Sum.inr ⟨d, a⟩)) rfl
    (fun a i => F.generator_height hs (Sum.inr ⟨d, a⟩) i)

theorem exists_coefficientFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.coefficientFreeSpan d))) ℚ (D.coefficientFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q := by
  let v := Sum.elim (fun a => D.coefficientFreeGenerator (Sum.inl ⟨d, a⟩))
    (fun a => D.coefficientFreeGenerator (Sum.inr ⟨d, a⟩))
  have hspan : Submodule.span ℚ (Set.range v) = D.coefficientFreeSpan d := by
    dsimp only [v]
    rw [span_range_sumElim]
    rfl
  apply exists_submodule_basis_of_spanning_logHeight e _ v hspan
  intro a i
  cases a with
  | inl a => exact F.generator_height hs (Sum.inl ⟨d, a⟩) i
  | inr a => exact F.generator_height hs (Sum.inr ⟨d, a⟩) i

end Erdos3.NativeRankRelation.CommonData

end

end OAI
