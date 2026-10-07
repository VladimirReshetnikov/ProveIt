/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Geometry.UnitIntervalBox
import OAI.Combinatorics.Progressions.Linear.NativeRankRelationExistence
import OAI.Combinatorics.Progressions.Linear.RankUnadaptedFactorization
import OAI.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest

namespace OAI

section

namespace Erdos3

def rankIntervalInputBudget (c : ℕ) (p : ℝ) : ℝ :=
  (p + c) ^ c + raisedNiltestBudget p + p + 5

theorem rankIntervalInputBudget_bounds (c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    5 ≤ rankIntervalInputBudget c p ∧ p + 4 ≤ rankIntervalInputBudget c p ∧
      raisedNiltestBudget p ≤ rankIntervalInputBudget c p ∧
      (p + c) ^ c ≤ rankIntervalInputBudget c p := by
  have ha : 0 ≤ (p + c) ^ c := by positivity
  have hb : 0 ≤ raisedNiltestBudget p := by unfold raisedNiltestBudget; positivity
  unfold rankIntervalInputBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exists_rank_interval_product_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      productNiltestBudget (rankIntervalInputBudget c p) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C c) ^ c + (X + (X + 2) ^ 2 + 3) + X + 5
  let P := (U + 2) ^ 2 + U + (U + (U ^ 2 + U + 3) ^ 2) + U ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, U, X, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget,
    rankIntervalInputBudget, raisedNiltestBudget] using hbound p hp

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (R : ∀ i, (D i).DegreeRankStructure r)

noncomputable def productRankLayerBasis (j k : Fin (s + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((R i).filtration.layer j.val k.val))) ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val) :=
  (Pi.basis (fun i => (R i).basis j k)).map
    (DegreeRankLieFiltration.piLayerEquiv (fun i => (R i).filtration) j.val k.val)

noncomputable def productRankLayerFinBasis (j k : Fin (s + 1)) :
    Basis (Fin (finrank ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val))) ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val) :=
  (productRankLayerBasis D R j k).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productRankLayerBasis D R j k)).symm)

noncomputable def piRank : (pi D).DegreeRankStructure r where
  filtration := DegreeRankLieFiltration.pi (fun i => (R i).filtration)
  associated := by
    rw [DegreeRankLieFiltration.pi_associatedDegree]
    exact congrArg NilpotentLieFiltration.pi (funext (fun i => (R i).associated))
  basis := productRankLayerFinBasis D R

theorem productRankLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p) (j k : Fin (s + 1))
    (a : Σ i, Fin (finrank ℚ ((R i).filtration.layer j.val k.val)))
    (b : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr
      ((productRankLayerBasis D R j k a).val) b) ≤ p := by
  classical
  rcases a with ⟨a, m⟩
  rcases b with ⟨b, n⟩
  simp only [productRankLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D b).basis.repr
    (((Pi.basis (fun i => (R i).basis j k)) ⟨a, m⟩ b).val) n) ≤ p
  rw [Pi.basis_apply]
  by_cases hab : a = b
  · subst b
    rw [Pi.single_eq_same]
    exact (hR a).2 j k m n
  · rw [Pi.single_eq_of_ne (Ne.symm hab)]
    simpa [rationalLogHeight] using hp

theorem piRank_complexity {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p) :
    (piRank D R).ComplexityLE ((p + 2) ^ 2) := by
  refine ⟨pi_geometry D hp hι (fun i => (hR i).1), ?_⟩
  intro j k a b
  change Fin (finrank ℚ
    ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val)) at a
  change rationalLogHeight ((productFinBasis D).repr
    ((productRankLayerFinBasis D R j k a).val) b) ≤ (p + 2) ^ 2
  rw [productFinBasis, Basis.repr_reindex_apply, productRankLayerFinBasis, Basis.reindex_apply]
  exact (productRankLayerBasis_logHeight D R hp hR j k _ _).trans (by nlinarith [sq_nonneg p])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) {G : NilpotentLieFiltration L s}

theorem orbitEquivOfEq_log (h : F = G) (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    (F.orbitEquivOfEq h w g).log = g.log := by
  subst G
  rfl

theorem orbitEquivOfEq_translate (h : F = G) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : F.PolynomialOrbit w) (a : σ → ℤ) :
    F.orbitEquivOfEq h w (g.translate hw a) = (F.orbitEquivOfEq h w g).translate hw a := by
  subst G
  rfl

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem orbitEquiv_log (w : σ → ℕ) (g : D.filtration.realification.PolynomialOrbit w) :
    (R.orbitEquiv w g).log = g.log :=
  D.filtration.realification.orbitEquivOfEq_log R.real_associated.symm w g

theorem orbitEquiv_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : D.filtration.realification.PolynomialOrbit w) (a : σ → ℤ) :
    R.orbitEquiv w (g.translate hw a) = (R.orbitEquiv w g).translate hw a :=
  D.filtration.realification.orbitEquivOfEq_translate R.real_associated.symm w hw g a

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (R : ∀ i, (D i).DegreeRankStructure r)

theorem productProjectionHom_mem_rank (i : ι) (k j : ℕ) (g : (pi D).RealGroup)
    (hg : g ∈ (piRank D R).realSubgroup k j) :
    productProjectionHom D i g ∈ (R i).realSubgroup k j := by
  apply baseChange_mem_of_mapsTo ((piRank D R).filtration.layer k j)
    ((R i).filtration.layer k j) (liePiEval i).toLinearMap _ hg
  intro x hx
  exact (DegreeRankLieFiltration.mem_pi_layer (fun i => (R i).filtration) k j x).mp hx i

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {w : σ → ℕ}

theorem productObservable_rank_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (hvert : ∀ i z, z ∈ (R i).realSubgroup s r → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (piRank D R).realSubgroup s r)
    (x : (pi D).Space) :
    productObservable D T (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        productObservable D T x := by
  have hchar :
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) =
        ∏ i, CircleFourier.character
          ((realifyFunctional (eta i) (productProjectionHom D i z).coord : ℝ) : CircleFourier.Circle) := by
    rw [realify_piFrequency]
    have hcoe (f : ι → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) =
        ∑ i, (f i : CircleFourier.Circle) :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
    simp only [hcoe, CircleFourier.character_fintype_sum,
      productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  rw [hchar, productObservable, productObservable, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_smul]
  exact hvert i _ (productProjectionHom_mem_rank D R i s r z hz) _

variable [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem piNiltest_rank_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hvert : ∀ i z, z ∈ (R i).realSubgroup s r → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (piRank D R).realSubgroup s r)
    (x : (pi D).Space) :
    (piNiltest D T hp hι hT).observable (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        (piNiltest D T hp hι hT).observable x :=
  productObservable_rank_vertical D R T eta hvert z hz x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NativeDegreeRankFamily

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def fourPointFactors (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ) :
    Fin 4 → W.model.Niltest (fun _ : Unit => 1) :=
  ![(W.component out (a 0)).conjugate,
    (W.component out (a 1)).translate (fun _ => by decide) (fun _ => δ),
    W.component out (a 2),
    ((W.component out (a 3)).translate (fun _ => by decide) (fun _ => δ)).conjugate]

noncomputable def fourPointFrequencies : Fin 4 → (W.L →ₗ[ℚ] ℚ) :=
  ![-W.vertical.frequency, W.vertical.frequency, W.vertical.frequency, -W.vertical.frequency]

theorem fourPointFactors_complexity (hp : 0 ≤ p) (out : Fin W.outputDim)
    (a : Fin 4 → A) (δ : ℤ) (i : Fin 4) :
    (W.fourPointFactors out a δ i).ComplexityLE (p + 4) := by
  fin_cases i
  · exact W.component_complexity hp out (a 0)
  · exact W.component_complexity hp out (a 1)
  · exact W.component_complexity hp out (a 2)
  · exact W.component_complexity hp out (a 3)

theorem fourPointFactors_eval (out : Fin W.outputDim) (a : Fin 4 → A) (δ n : ℤ) :
    (∏ i, (W.fourPointFactors out a δ i).eval (fun _ => n)) =
      fourPointProduct (W.eval out (a 0)) (W.eval out (a 1))
        (W.eval out (a 2)) (W.eval out (a 3)) δ n := by
  have hshift : (fun _ : Unit => n) + (fun _ => δ) = (fun _ => n + δ) := rfl
  simp [fourPointFactors, Fin.prod_univ_succ, fourPointProduct, component_eval, hshift, mul_assoc]

theorem fourPointFactors_vertical (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ)
    (i : Fin 4) (z : W.model.RealGroup) (hz : z ∈ W.rank.realSubgroup s r)
    (x : W.model.Space) :
    (W.fourPointFactors out a δ i).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (W.fourPointFrequencies i) z.coord : ℝ) : CircleFourier.Circle) *
          (W.fourPointFactors out a δ i).observable x := by
  have h := W.vertical.vertical out z hz x
  have hn : star (W.vertical.observable out (z • x)) =
      CircleFourier.character
        ((realifyFunctional (-W.vertical.frequency) z.coord : ℝ) : CircleFourier.Circle) *
          star (W.vertical.observable out x) := by
    rw [h, star_mul, realifyFunctional_neg, AddCircle.coe_neg, CircleFourier.character_neg]
    exact mul_comm _ _
  fin_cases i
  · exact hn
  · exact h
  · exact h
  · exact hn

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 4 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 4 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 4 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 4 → W.L))]

noncomputable def fourPointNiltest (hp : 0 ≤ p) (out : Fin W.outputDim)
    (a : Fin 4 → A) (δ : ℤ) :
    (pi (fun _ : Fin 4 => W.model)).Niltest (fun _ : Unit => 1) :=
  piNiltest (fun _ : Fin 4 => W.model) (W.fourPointFactors out a δ)
    (by linarith) (by simpa using hp) (W.fourPointFactors_complexity hp out a δ)

theorem fourPointNiltest_complexity (hp : 0 ≤ p) (out : Fin W.outputDim)
    (a : Fin 4 → A) (δ : ℤ) :
    (W.fourPointNiltest hp out a δ).ComplexityLE (productNiltestBudget (p + 4)) :=
  piNiltest_complexity (fun _ : Fin 4 => W.model) (W.fourPointFactors out a δ)
    (by linarith) (by simpa using hp) (W.fourPointFactors_complexity hp out a δ)

theorem fourPointNiltest_eval (hp : 0 ≤ p) (out : Fin W.outputDim)
    (a : Fin 4 → A) (δ n : ℤ) :
    (W.fourPointNiltest hp out a δ).eval (fun _ => n) =
      fourPointProduct (W.eval out (a 0)) (W.eval out (a 1))
        (W.eval out (a 2)) (W.eval out (a 3)) δ n := by
  rw [fourPointNiltest, piNiltest_eval]
  exact W.fourPointFactors_eval out a δ n

theorem fourPointNiltest_vertical (hp : 0 ≤ p) (out : Fin W.outputDim)
    (a : Fin 4 → A) (δ : ℤ) (z : (pi (fun _ : Fin 4 => W.model)).RealGroup)
    (hz : z ∈ (piRank (fun _ : Fin 4 => W.model) (fun _ => W.rank)).realSubgroup s r)
    (x : (pi (fun _ : Fin 4 => W.model)).Space) :
    (W.fourPointNiltest hp out a δ).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency W.fourPointFrequencies) z.coord : ℝ) : CircleFourier.Circle) *
          (W.fourPointNiltest hp out a δ).observable x :=
  piNiltest_rank_vertical (fun _ : Fin 4 => W.model) (fun _ => W.rank)
    (W.fourPointFactors out a δ) W.fourPointFrequencies
    (by linarith) (by simpa using hp) (W.fourPointFactors_complexity hp out a δ)
    (W.fourPointFactors_vertical out a δ) z hz x

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3.NativeDegreeRankFamily

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {κ A : Type*} {s r : ℕ} {p : ℝ} (W : NativeDegreeRankFamily s r A p)
  (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
  (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))

noncomputable def horizontalCoefficient (α : Unit →₀ ℕ) (a : A) :
    ℝ ⊗[ℚ] W.rank.filtration.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) α) :=
  Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α
    (W.rank.orbitEquiv (fun _ => 1) (W.orbit a)))

theorem fourPointFactors_orbit (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ) (k : Fin 4) :
    (W.fourPointFactors out a δ k).orbit =
      ![W.orbit (a 0), (W.orbit (a 1)).translate (fun _ => Nat.zero_lt_one) (fun _ => δ),
        W.orbit (a 2), (W.orbit (a 3)).translate (fun _ => Nat.zero_lt_one) (fun _ => δ)] k := by
  fin_cases k <;> rfl

theorem fourPoint_horizontalCoefficient (out : Fin W.outputDim) (a : Fin 4 → A)
    (δ : ℤ) (α : Unit →₀ ℕ) (k : Fin 4) :
    Multiplicative.toAdd (W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α
      (W.rank.orbitEquiv (fun _ => 1) (W.fourPointFactors out a δ k).orbit)) =
        W.horizontalCoefficient hs c τ hG α (a k) := by
  rw [W.fourPointFactors_orbit]
  fin_cases k
  · rfl
  · have h := congrArg
      (fun g : W.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) =>
        W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α g)
      (W.rank.orbitEquiv_translate (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)
        (W.orbit (a 1)) (fun _ => δ))
    exact congrArg Multiplicative.toAdd (h.trans
      (W.rank.filtration.nativeHorizontalCoefficientHom_translate hs c τ hG
        (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) α
        (W.rank.orbitEquiv (fun _ => 1) (W.orbit (a 1))) (fun _ => δ)))
  · rfl
  · have h := congrArg
      (fun g : W.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) =>
        W.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ => 1) α g)
      (W.rank.orbitEquiv_translate (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)
        (W.orbit (a 3)) (fun _ => δ))
    exact congrArg Multiplicative.toAdd (h.trans
      (W.rank.filtration.nativeHorizontalCoefficientHom_translate hs c τ hG
        (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) α
        (W.rank.orbitEquiv (fun _ => 1) (W.orbit (a 3))) (fun _ => δ)))

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

def rankQuadrupleParameters {N : ℕ} (t : ZMod N × ZMod N × ZMod N) : Fin 4 → ZMod N :=
  ![t.2.1, t.2.1 - t.1, t.2.2, t.2.2 - t.1]

namespace NativeRankInterval

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

noncomputable def productModels (i : Fin I.expansion.count) : ∀ k : Option (Fin 4),
    RationalFilteredNilmanifold (optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) s
      (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k) :=
  optionFactors ((I.expansion.model i).raiseStep (Nat.sub_le s 1)) (fun _ : Fin 4 => W.model)

noncomputable def productRanks (i : Fin I.expansion.count)
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r) :
    ∀ k, (I.productModels i k).DegreeRankStructure r
  | none => R₀
  | some _ => W.rank

noncomputable def productTests (i : Fin I.expansion.count) :
    ∀ k, (I.productModels i k).Niltest (fun _ : Unit => 1)
  | none => (I.expansion.test i).raiseStep (Nat.sub_le s 1)
  | some k => W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch) k

noncomputable def productFrequencies (i : Fin I.expansion.count) :
    ∀ k, optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => W.fourPointFrequencies k

theorem productTests_eval (i : Fin I.expansion.count) (n : ℤ) :
    (∏ k, (I.productTests i k).eval (fun _ => n)) =
      fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
        (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) := by
  rw [Fintype.prod_option]
  change ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) *
    (∏ k, (W.fourPointFactors out (rankQuadrupleParameters t)
      (cyclicBranchOffset t.1 branch) k).eval (fun _ => n)) = _
  rw [W.fourPointFactors_eval]
  exact mul_comm _ _

theorem productTests_vertical (hs : 1 ≤ s) (i : Fin I.expansion.count)
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r)
    (k : Option (Fin 4)) (z : (I.productModels i k).RealGroup)
    (hz : z ∈ (I.productRanks i R₀ k).realSubgroup s r) (x : (I.productModels i k).Space) :
    (I.productTests i k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (I.productFrequencies i k) z.coord : ℝ) : CircleFourier.Circle) *
          (I.productTests i k).observable x := by
  cases k with
  | none => exact (I.expansion.test i).raiseStep_rank_vertical (by omega) R₀ z hz x
  | some k =>
    exact W.fourPointFactors_vertical out (rankQuadrupleParameters t)
      (cyclicBranchOffset t.1 branch) k z hz x

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

def rankCoordinateTuple {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (t : ZMod N × ZMod N × ZMod N) : (Σ _ : Fin 4, ι) → ℝ :=
  fun j => β (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1)) j.2

theorem rankCoordinateTuple_first12 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (a b h : ZMod N) (i : ι) : rankCoordinateTuple β (b - h, b, a) ⟨0, i⟩ = β h i := by
  simp [rankCoordinateTuple, rankQuadrupleParameters]

theorem rankCoordinateTuple_first13 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (c d h : ZMod N) (i : ι) :
    rankCoordinateTuple β (c - d, h + (c - d), c) ⟨0, i⟩ = β h i := by
  simp [rankCoordinateTuple, rankQuadrupleParameters]

theorem rankCoordinateTuple_fixed12 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (a b h h₀ : ZMod N) (j : Σ _ : ({1, 2} : Finset (Fin 4)), ι) :
    rankCoordinateTuple β (b - h, b, a) ⟨j.1, j.2⟩ =
      rankCoordinateTuple β (b - h₀, b, a) ⟨j.1, j.2⟩ := by
  have hj := j.1.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with hj | hj <;> simp [rankCoordinateTuple, rankQuadrupleParameters, hj]

theorem rankCoordinateTuple_fixed13 {N : ℕ} {ι : Type*} (β : ZMod N → ι → ℝ)
    (c d h h₀ : ZMod N) (j : Σ _ : ({1, 3} : Finset (Fin 4)), ι) :
    rankCoordinateTuple β (c - d, h + (c - d), c) ⟨j.1, j.2⟩ =
      rankCoordinateTuple β (c - d, h₀ + (c - d), c) ⟨j.1, j.2⟩ := by
  have hj := j.1.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with hj | hj <;> simp [rankCoordinateTuple, rankQuadrupleParameters, hj]

theorem card_selected_four_le {ι : Type*} [Fintype ι] (K : Finset (Fin 4)) :
    Fintype.card (Σ _ : K, ι) ≤ Fintype.card (Σ _ : Fin 4, ι) := by
  let f : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  exact Sigma.ext (Subtype.ext (congrArg Sigma.fst h))
    (heq_of_eq (congrArg (fun z : Σ _ : Fin 4, ι => z.2) h))

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_product (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      ∃ i : Fin I.expansion.count,
        ∃ R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R₀.ComplexityLE ((p + C) ^ C) ∧ R₀.realSubgroup s r = ⊥ ∧
          letI : FiniteDimensional ℚ
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
            (productFinBasis (I.productModels i)).finiteDimensional_of_finite
          letI := moduleTopology ℝ (ℝ ⊗[ℚ]
            (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
          letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
            IsModuleTopology.topologicalAddGroup ℝ _
          letI : T2Space (ℝ ⊗[ℚ]
              (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
            realification_moduleTopology_t2 (productFinBasis (I.productModels i))
          ∃ T : (pi (I.productModels i)).Niltest (fun _ : Unit => 1),
            T.ComplexityLE ((p + C) ^ C) ∧
            (piRank (I.productModels i) (I.productRanks i R₀)).ComplexityLE ((p + C) ^ C) ∧
            T.orbit = NilpotentLieFiltration.piRealOrbit (fun k => (I.productModels i k).filtration)
              (fun k => (I.productTests i k).orbit) ∧
            (∀ n, T.eval (fun _ => n) =
              fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
                (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
                  ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n)) ∧
            (∀ z ∈ (piRank (I.productModels i) (I.productRanks i R₀)).realSubgroup s r, ∀ x,
              T.observable (z • x) = CircleFourier.character
                ((realifyFunctional (piFrequency (I.productFrequencies i)) z.coord : ℝ) :
                  CircleFourier.Circle) * T.observable x) ∧
            Real.exp (-(2 * p)) ≤
              ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length), T.eval x‖ := by
  obtain ⟨c, _, hlower⟩ := exists_rank_interval_raised_lower_term s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_interval_product_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I
  obtain ⟨i, R₀, hR₀, hzero, hT₀, hcorr⟩ := hlower I
  let u := rankIntervalInputBudget c p
  obtain ⟨hu5, hup, huraise, hurank⟩ := rankIntervalInputBudget_bounds c hp
  have hu : 0 ≤ u := (by norm_num : (0 : ℝ) ≤ 5).trans hu5
  have hub : u ≤ productNiltestBudget u := by
    have hg := productNiltestBudget_geometry hu
    nlinarith [sq_nonneg u]
  have hcost : productNiltestBudget u ≤ (p + C) ^ C := hbudget p hp
  have hsmall : u ≤ (p + C) ^ C := hub.trans hcost
  have hb : 0 ≤ b := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hbu : b ≤ u := hbp.trans (by linarith)
  have hcard : (Fintype.card (Option (Fin 4)) : ℝ) ≤ u := by
    simpa using hu5
  have htests : ∀ k, (I.productTests i k).ComplexityLE u := by
    intro k
    cases k with
    | none => exact hT₀.mono huraise
    | some k => exact (W.fourPointFactors_complexity hb out (rankQuadrupleParameters t)
        (cyclicBranchOffset t.1 branch) k).mono (by linarith)
  have hranks : ∀ k, (I.productRanks i R₀ k).ComplexityLE u := by
    intro k
    cases k with
    | none => exact hR₀.mono R₀ hurank
    | some _ => exact W.complexity.mono W.rank hbu
  refine ⟨i, R₀, hR₀.mono R₀ (hurank.trans hsmall), hzero, ?_⟩
  let : FiniteDimensional ℚ
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
    (productFinBasis (I.productModels i)).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    realification_moduleTopology_t2 (productFinBasis (I.productModels i))
  let T := piNiltest (I.productModels i) (I.productTests i) hu hcard htests
  have heval (n : ℤ) : T.eval (fun _ => n) =
      fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
        (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n) :=
    (piNiltest_eval (I.productModels i) (I.productTests i) hu hcard htests _).trans
      (I.productTests_eval i n)
  refine ⟨T, (piNiltest_complexity _ _ hu hcard htests).mono hcost,
    (piRank_complexity _ _ hu hcard hranks).mono (piRank (I.productModels i) (I.productRanks i R₀))
      ((productNiltestBudget_geometry hu).trans hcost), rfl, heval, ?_, ?_⟩
  · exact piNiltest_rank_vertical _ _ _ _ hu hcard htests (I.productTests_vertical hs i R₀)
  · rw [unitIntervalBox_expect]
    simpa only [heval, two_mul] using hcorr

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

noncomputable def productOrbit :
    (pi (I.productModels i)).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
  NilpotentLieFiltration.piRealOrbit (fun k => (I.productModels i k).filtration)
    (fun k => (I.productTests i k).orbit)

noncomputable def productSymbol {κ : Type*}
    (e : Basis κ ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) (ω : κ → ℕ)
    (hF : ∀ j, (pi (I.productModels i)).filtration.layer j =
      Submodule.span ℚ (e '' {a | j ≤ ω a})) :
    (pi (I.productModels i)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1) :=
  (pi (I.productModels i)).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
    ⟨⟨(I.productOrbit i).log, (I.productOrbit i).property⟩⟩

variable [TopologicalSpace (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]
  [T2Space (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))]

theorem productSymbol_eq {κ : Type*}
    (e : Basis κ ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) (ω : κ → ℕ)
    (hF : ∀ j, (pi (I.productModels i)).filtration.layer j =
      Submodule.span ℚ (e '' {a | j ≤ ω a}))
    (T : (pi (I.productModels i)).Niltest (fun _ : Unit => 1)) (hT : T.orbit = I.productOrbit i) :
    T.symbol e ω hF = I.productSymbol i e ω hF := by
  unfold RationalFilteredNilmanifold.Niltest.symbol productSymbol
  apply congrArg ((pi (I.productModels i)).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1))
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : (pi (I.productModels i)).filtration.realification.PolynomialOrbit
    (fun _ : Unit => 1) => o.log) hT

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

def rankProjection :
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) →ₗ⁅ℚ⁆
      (Fin 4 → W.L) :=
  liePiMap (fun k : Fin 4 => liePiEval (R := ℚ)
    (M := optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L))
    (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)))

theorem rankProjection_frequency
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :
    piFrequency (I.productFrequencies i) x =
      W.vertical.frequency (I.rankProjection i x 0) + W.vertical.frequency (I.rankProjection i x 1) -
        W.vertical.frequency (I.rankProjection i x 2) - W.vertical.frequency (I.rankProjection i x 3) := by
  rw [piFrequency_apply, Fintype.sum_option]
  simp only [Fin.sum_univ_succ]
  change 0 + (-W.vertical.frequency (x (some 0)) +
    (W.vertical.frequency (x (some 1)) + (W.vertical.frequency (x (some 2)) +
      (-W.vertical.frequency (x (some 3)) + 0)))) =
    W.vertical.frequency (x (some 1)) + W.vertical.frequency (x (some 2)) -
      W.vertical.frequency (x (some 0)) - W.vertical.frequency (x (some 3))
  ring

theorem rankProjection_mem_layer (d : ℕ)
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (hx : x ∈ (pi (I.productModels i)).filtration.layer d) (k : Fin 4) :
    I.rankProjection i x k ∈ W.rank.filtration.layer d 1 := by
  have h := (NilpotentLieFiltration.mem_pi_layer (fun j => (I.productModels i j).filtration) d x).mp hx
    (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))
  change I.rankProjection i x k ∈ W.model.filtration.layer d at h
  rw [← W.rank.associated] at h
  change I.rankProjection i x k ∈ W.rank.filtration.layer d 0 at h
  rwa [W.rank.filtration.rank_zero_eq_one] at h

theorem rankProjection_mem_refiltered
    (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded) (d : ℕ)
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (hx : x ∈ (pi (I.productModels i)).filtration.gradedRefiltrationLayer U d) (k : Fin 4) :
    I.rankProjection i x k ∈ W.rank.filtration.layer d 1 :=
  I.rankProjection_mem_layer i d x
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer_le U d hx) k

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      Real.exp ((p + C) ^ C) ≤ (I.length : ℝ) →
      ∃ i : Fin I.expansion.count,
        ∃ R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R₀.ComplexityLE ((p + C) ^ C) ∧ R₀.realSubgroup s r = ⊥ ∧
          ∃ F : (piRank (I.productModels i) (I.productRanks i R₀)).AdaptedData,
            F.rank.ComplexityLE ((p + C) ^ C) ∧
            (∀ j k, rationalLogHeight ((pi (I.productModels i)).basis.repr (F.basis j) k) ≤
              (p + C) ^ C) ∧
            (∀ k j, rationalLogHeight (F.basis.repr ((pi (I.productModels i)).basis k) j) ≤
              (p + C) ^ C) ∧
            F.rank.ControlledRankBracketFactorization F.weight F.layers
              (piFrequency (I.productFrequencies i)) (fun _ : Unit => (I.length : ℝ))
              (I.productSymbol i F.basis F.weight F.layers) ((p + C) ^ C) := by
  obtain ⟨a, _, hproduct⟩ := exists_rank_interval_product s hs
  obtain ⟨c, _, hfactor⟩ := exists_rank_unadapted_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a + 2 * X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  let u := (p + a) ^ a + 2 * p + 1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hQu : (p + a) ^ a ≤ u := by dsimp [u]; linarith
  have h2pu : 2 * p ≤ u := by dsimp [u]; linarith
  have hone : 1 ≤ u := by dsimp [u]; linarith
  have hsum : u + (u + c) ^ c ≤ (p + C) ^ C := by
    simpa [U, X, u, Polynomial.eval₂_pow] using hbudget p hp
  have hfactor0 : 0 ≤ (u + c) ^ c := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hfactorC : (u + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨i, R₀, hR₀, hzero, htest⟩ := hproduct hp hbp I
  let : FiniteDimensional ℚ
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
    (productFinBasis (I.productModels i)).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    realification_moduleTopology_t2 (productFinBasis (I.productModels i))
  obtain ⟨T, hT, hR, horbit, _, hvert, hbias⟩ := htest
  have hbiasu : Real.exp (-u) ≤
      ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length), T.eval x‖ :=
    (Real.exp_le_exp.mpr (neg_le_neg h2pu)).trans hbias
  obtain ⟨F, hFR, hforward, hback, hF⟩ := hfactor (pi (I.productModels i))
    (piRank (I.productModels i) (I.productRanks i R₀)) u hu (by simpa using hone)
    (hR.mono _ hQu) T (hT.mono hQu) (piFrequency (I.productFrequencies i)) hvert
    (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length) (fun _ => I.length_pos)
    (fun _ => (Real.exp_le_exp.mpr hfactorC).trans hlarge) hbiasu
  have hsymbol := I.productSymbol_eq i F.basis F.weight F.layers T horbit
  rw [hsymbol] at hF
  refine ⟨i, R₀, hR₀.mono R₀ (hQu.trans huC), hzero, F, hFR.mono F.rank hfactorC,
    (fun j k => (hforward j k).trans hfactorC),
    (fun k j => (hback k j).trans hfactorC), ?_⟩
  exact DegreeRankStructure.ControlledRankBracketFactorization.mono F.rank F.weight F.layers
    hF hfactorC (fun _ => by exact_mod_cast I.length_pos)

end Erdos3

end

end OAI
