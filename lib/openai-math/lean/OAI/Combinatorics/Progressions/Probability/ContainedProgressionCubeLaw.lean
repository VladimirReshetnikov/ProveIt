import OAI.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
import OAI.Combinatorics.Progressions.Geometry.FiniteGoodSupport
import OAI.Combinatorics.Progressions.Lattices.NormalizedIntegerBoxZeroCube

namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem complexMean_pi_sum {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {X : I ⊕ J → Type*} [∀ i, Fintype (X i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (f : (∀ i, X i) → ℂ) :
    (pi p).complexMean f =
      (pi (fun i => p (.inl i))).complexMean (fun a =>
        (pi (fun j => p (.inr j))).complexMean (fun b => f (Sum.rec a b))) := by
  classical
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * f x) = _
  calc
    _ = ∑ ab : (∀ i, X (.inl i)) × (∀ j, X (.inr j)),
        ((∏ i, (p i).weight (Sum.rec ab.1 ab.2 i) : ℝ) : ℂ) *
          f (Sum.rec ab.1 ab.2) := by
      apply Fintype.sum_equiv (Equiv.sumPiEquivProdPi X)
      intro x
      have he : (fun i => Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i) = x := by
        funext i
        cases i <;> rfl
      change ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * f x =
        ((∏ i, (p i).weight (Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i) : ℝ) : ℂ) *
          f (fun i => Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i)
      simp only [he]
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.prod_sum_type,
        Complex.ofReal_mul, complexMean, pi, Finset.mul_sum, mul_assoc]

theorem complexMean_commute {I J : Type*} [Fintype I] [Fintype J]
    (p : FiniteProbabilityWeights I) (q : FiniteProbabilityWeights J) (f : I → J → ℂ) :
    p.complexMean (fun i => q.complexMean (f i)) =
      q.complexMean (fun j => p.complexMean (fun i => f i j)) := by
  simp only [complexMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end FiniteProbabilityWeights

theorem integerBox_cube_mean_split {G P : Type*} [Fintype G] [Fintype P]
    [DecidableEq G] [DecidableEq P] (S : ℕ) (hS : 0 < S)
    (L : P → ℕ) (hL : ∀ j, 0 < L j) (q : ℕ)
    (f : ((Fin q → G ⊕ P → ℤ) × (G ⊕ P → ℤ)) → ℂ) :
    (𝔼 c : SupportedCube q (integerBox (Sum.elim (fun _ : G => S) L) : Set (G ⊕ P → ℤ)),
      f c.val) =
    (FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights (Fin q) S hS)).complexMean
      (fun x => (FiniteProbabilityWeights.pi (fun j => integerScalarCubeWeights (Fin q) (L j) (hL j))).complexMean
        (fun y => f (fun i => Sum.elim (fun g => (x g (some i) : ℤ)) (fun j => (y j (some i) : ℤ)),
          Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ))))) := by
  rw [← integerScalarCubeProduct_complexMean _ (Sum.rec (fun _ => hS) hL) q f,
    FiniteProbabilityWeights.complexMean_pi_sum]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  apply Prod.ext
  · funext i j
    cases j <;> rfl
  · funext i
    cases i <;> rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

noncomputable def containedProgressionTupleMap (v : PrincipalIntegerTuples B h α H) :
    PrincipalIntegerTuples B h α L :=
  fun j => containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j) (hsubset j) (v j)

omit [DecidableEq D] [∀ d, DecidableEq (B d)] in
theorem containedProgressionTupleMap_normalized [DecidableEq D] [∀ d, DecidableEq (B d)]
    (v : PrincipalIntegerTuples B h α H)
    (hv : ∀ j, IntegerScalarCube (H j) (fun i => (v j i : ℤ))) :
    principalTupleNormalized L (containedProgressionTupleMap B h L H step c hL hsubset v) =
      principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j) := by
  funext a
  simp only [principalTupleNormalized, principalTupleIntegers, containedProgressionTupleMap,
    containedProgressionCubeMap_value _ _ _ _ _ _ _ _ (hv _), principalTupleFlatten_apply,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero]

theorem containedProgressionTupleLaw_mean
    (p : FiniteProbabilityWeights (PrincipalIntegerTuples B h α H))
    (hp : ∀ v, p.weight v ≠ 0 → ∀ j, IntegerScalarCube (H j) (fun i => (v j i : ℤ)))
    (f : (JointBlockParameter B h α → ℝ) → ℝ) :
    (p.fiberLaw (containedProgressionTupleMap B h L H step c hL hsubset)).mean
        (fun v => f (principalTupleNormalized L v)) =
      p.mean (fun v => f (principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j))) := by
  rw [p.fiberLaw_mean]
  apply p.mean_congr_on_support
  intro v hv
  rw [containedProgressionTupleMap_normalized B h L H step c hL hsubset v (hp v hv)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K α : Type*} [Fintype K] [DecidableEq K] [Fintype α] [DecidableEq α]
variable (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
variable (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ) (L k : ℤ))

noncomputable def containedProgressionCubeLaw :
    FiniteProbabilityWeights (∀ k, IntegerScalarCubeBox α (L k)) :=
  (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (H k) (hH k))).fiberLaw
    (fun y k => containedProgressionCubeMap α (L k) (H k) (step k) (c k) (hL k) (hsubset k) (y k))

theorem containedProgressionCubeLaw_complexMean
    (f : (K → Option α → ℤ) → ℂ) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).complexMean
        (fun y => f (fun k i => (y k i : ℤ))) =
      (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (H k) (hH k))).complexMean
        (fun y => f (fun k i => (if i = none then c k else 0) + (step k : ℤ) * (y k i : ℤ))) := by
  rw [containedProgressionCubeLaw, FiniteProbabilityWeights.fiberLaw_complexMean]
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro y hy
  apply congrArg f
  funext k i
  have hpos := lt_of_le_of_ne ((FiniteProbabilityWeights.pi
    (fun k => integerScalarCubeWeights α (H k) (hH k))).nonneg y) hy.symm
  have hk := FiniteProbabilityWeights.pi_weight_pos_component
    (fun k => integerScalarCubeWeights α (H k) (hH k)) y hpos k
  have hc := (mem_integerScalarCubeSet (H k) (y k)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y k)).mp hk).1
  exact containedProgressionCubeMap_value α (L k) (H k) (step k) (c k) (hL k) (hsubset k) (y k) hc i

theorem containedProgressionCubeLaw_sum
    {G P : Type*} [Fintype G] [DecidableEq G] [Fintype P] [DecidableEq P]
    (L H step : G ⊕ P → ℕ) (c : G ⊕ P → ℤ)
    (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L k : ℤ))
    (f : (∀ k, IntegerScalarCubeBox α (L k)) → ℂ) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).complexMean f =
      (containedProgressionCubeLaw (α := α) (fun g => L (.inl g)) (fun g => H (.inl g))
        (fun g => step (.inl g)) (fun g => c (.inl g))
        (fun g => hL (.inl g)) (fun g => hH (.inl g)) (fun g => hsubset (.inl g))).complexMean
      (fun x => (containedProgressionCubeLaw (α := α) (fun j => L (.inr j)) (fun j => H (.inr j))
        (fun j => step (.inr j)) (fun j => c (.inr j))
        (fun j => hL (.inr j)) (fun j => hH (.inr j)) (fun j => hsubset (.inr j))).complexMean
        (fun y => f (Sum.rec x y))) := by
  simp only [containedProgressionCubeLaw, FiniteProbabilityWeights.fiberLaw_complexMean]
  rw [FiniteProbabilityWeights.complexMean_pi_sum]
  congr 1
  funext x
  congr 1
  funext y
  apply congrArg f
  funext k
  cases k <;> rfl

end Erdos3

end

end OAI
