/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.CommonSubspaceFamily
import OAI.Combinatorics.Progressions.Estimates.ProjectedHorizontalFactorization
import OAI.Combinatorics.Progressions.Fourier.RealLayerHorizontalFrequency
import OAI.Combinatorics.Progressions.Geometry.NativeCoordinateEstimates
import OAI.Combinatorics.Progressions.Linear.RankProductOrbitCoefficients

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realifyFunctional_lieTreeEval_rational (η : L →ₗ[ℚ] ℚ) (v : I → L) (a : FreeMagma I) :
    realifyFunctional η (lieTreeEval (fun i => rationalLieInclusion (v i)) a) =
      (η (lieTreeEval v a) : ℝ) := by
  rw [lieTreeEval_hom rationalLieInclusion v a]
  simp only [rationalLieInclusion_apply, realifyFunctional_tmul, one_mul]

theorem rational_lieTree_kernel_of_real (A : I → Submodule ℚ L)
    (η : L →ₗ[ℚ] ℚ) (a : FreeMagma I)
    (hker : ∀ z : I → ℝ ⊗[ℚ] L, (∀ i, z i ∈ (A i).baseChange ℝ) →
      realifyFunctional η (lieTreeEval z a) = 0)
    (v : I → L) (hv : ∀ i, v i ∈ A i) : η (lieTreeEval v a) = 0 := by
  have h := hker (fun i => rationalLieInclusion (v i))
    (fun i => Submodule.tmul_mem_baseChange_of_mem (1 : ℝ) (hv i))
  rw [realifyFunctional_lieTreeEval_rational] at h
  exact_mod_cast h

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
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
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

noncomputable def refilteredHorizontalImage (d : ℕ) :
    Submodule ℚ (Fin 4 → W.rank.filtration.HigherHorizontal d) :=
  W.rank.filtration.layerHorizontalImage
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) d

theorem refilteredHorizontalImage_frequency {J : Type*} (d : J → ℕ) (a : FreeMagma J)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ z : J → ℝ ⊗[ℚ]
        (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
      (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
      realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0)
    (v : ∀ j, Fin 4 → W.rank.filtration.HigherHorizontal (d j))
    (hv : ∀ j, v j ∈ I.refilteredHorizontalImage i U (d j)) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 0)) +
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 1)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 2)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a (fun j => v j 3)) = 0 := by
  apply W.rank.filtration.layerHorizontalImage_frequency
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) W.vertical.frequency d a hd hr ?_ v hv
  intro u hu
  rw [← I.rankProjection_frequency i]
  exact rational_lieTree_kernel_of_real
    (fun j => (pi (I.productModels i)).filtration.gradedRefiltrationLayer U (d j))
    (piFrequency (I.productFrequencies i)) a hker u hu

theorem refiltered_sunflower_bracket {J : Type*} (d : J → ℕ) (a : FreeMagma J)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ z : J → ℝ ⊗[ℚ]
        (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
      (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
      realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0)
    (v : ∀ j, W.rank.filtration.HigherHorizontal (d j))
    (hv : ∀ j, v j ∈ fourFirstProjection (I.refilteredHorizontalImage i U (d j)))
    (j k : J) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d j)))
    (hvk : v k ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d k))) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a) (W.rank.filtration.horizontalTreeValue d a)
    (fun u j hj hu => W.rank.filtration.horizontalTreeValue_zero_of_leaf d a u (i := j) hj hu)
    W.vertical.frequency (map_zero _) (fun j => I.refilteredHorizontalImage i U (d j))
    (I.refilteredHorizontalImage_frequency i U d a hd hr hker) v hv j k hjk hj hk hvj hvk

theorem refiltered_sunflower_representatives {J : Type*} (d : J → ℕ) (a : FreeMagma J)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ z : J → ℝ ⊗[ℚ]
        (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
      (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
      realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0)
    (v : ∀ j, W.rank.filtration.layer (d j) 1)
    (hv : ∀ j, W.rank.filtration.higherHorizontalMk (d j) (v j) ∈
      fourFirstProjection (I.refilteredHorizontalImage i U (d j)))
    (j k : J) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : W.rank.filtration.higherHorizontalMk (d j) (v j) ∈
      fourDependentProjection (I.refilteredHorizontalImage i U (d j)))
    (hvk : W.rank.filtration.higherHorizontalMk (d k) (v k) ∈
      fourDependentProjection (I.refilteredHorizontalImage i U (d k))) :
    W.vertical.frequency (lieTreeEval (fun j => (v j).val) a) = 0 := by
  have h := I.refiltered_sunflower_bracket i U d a hd hr hker
    (fun j => W.rank.filtration.higherHorizontalMk (d j) (v j)) hv j k hjk hj hk hvj hvk
  rwa [W.rank.filtration.horizontalTreeValue_mk d a hd hr v] at h

def SunflowerKernel : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℕ) (a : FreeMagma (Fin n)),
    lieTreeWeight d a = s → a.length = r →
    ∀ v : ∀ j, W.rank.filtration.HigherHorizontal (d j),
      (∀ j, v j ∈ fourFirstProjection (I.refilteredHorizontalImage i U (d j))) →
      ∀ j k, j ≠ k → j ∈ lieTreeSupport a → k ∈ lieTreeSupport a →
      v j ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d j)) →
      v k ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d k)) →
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a v) = 0

def BracketKernel : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℕ) (a : FreeMagma (Fin n)),
    lieTreeWeight d a = s → a.length = r →
    ∀ z : Fin n → ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
    (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
    realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0

theorem sunflowerKernel_of_real (hker : I.BracketKernel i U) :
    I.SunflowerKernel i U := by
  intro n d a hd hr v hv j k hjk hj hk hvj hvk
  exact I.refiltered_sunflower_bracket i U d a hd hr (hker n d a hd hr) v hv j k hjk hj hk hvj hvk

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold

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
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

noncomputable def refilteredProjectionImage (d : ℕ) : Submodule ℚ (Fin 4 → W.L) :=
  ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U d).map (I.rankProjection i).toLinearMap

theorem refilteredHorizontalImage_eq (d : ℕ) :
    I.refilteredHorizontalImage i U d =
      W.rank.filtration.horizontalImageOfSubmodule (I.refilteredProjectionImage i U d) d :=
  W.rank.filtration.layerHorizontalImage_eq_of_submodule
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) d

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_sunflower (s : ℕ) (hs : 1 ≤ s) :
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
            ∃ (l : ℕ) (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)
              (v : Fin (finrank ℚ (∀ k : Option (Fin 4),
                optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) →
                (pi (I.productModels i)).filtration.AssociatedGraded),
              0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
              BasisGradedSubmodule
                ((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers)
                F.weight U.toSubmodule ∧
              (∀ j k, rationalLogHeight
                (((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers).repr
                  (v j) k) ≤ (p + C) ^ C) ∧
              I.BracketKernel i U ∧ I.SunflowerKernel i U ∧
              (pi (I.productModels i)).filtration.SymbolFactorizationIn F.basis F.weight F.layers
                (fun _ : Unit => (I.length : ℝ)) (I.productSymbol i F.basis F.weight F.layers)
                ((p + C) ^ C) l U := by
  obtain ⟨C, hC, hfactor⟩ := exists_rank_interval_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  obtain ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, hfact⟩ := hfactor hp hbp I hlarge
  obtain ⟨l, U, v, hl, hlp, hv, hU, hheight, hker, hinside⟩ :=
    DegreeRankStructure.ControlledRankBracketFactorization.exists_in F.rank F.weight F.layers hfact
  exact ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, l, U, v, hl, hlp, hv, hU, hheight,
    hker, I.sunflowerKernel_of_real i U hker, hinside⟩

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
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

theorem real_rankProjection_frequency
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :
    realifyFunctional (piFrequency (I.productFrequencies i)) x =
      realifyFunctional W.vertical.frequency (realificationLieHom ((liePiEval 0).comp (I.rankProjection i)) x) +
      realifyFunctional W.vertical.frequency (realificationLieHom ((liePiEval 1).comp (I.rankProjection i)) x) -
      realifyFunctional W.vertical.frequency (realificationLieHom ((liePiEval 2).comp (I.rankProjection i)) x) -
      realifyFunctional W.vertical.frequency (realificationLieHom ((liePiEval 3).comp (I.rankProjection i)) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [realificationLieHom_tmul, realifyFunctional_tmul, LieHom.comp_apply,
      liePiEval_apply, I.rankProjection_frequency, Rat.cast_add, Rat.cast_sub, mul_add, mul_sub]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

theorem real_refilteredHorizontalImage_frequency
    (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)
    {J : Type*} (d : J → ℕ) (a : FreeMagma J)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ z : J → ℝ ⊗[ℚ]
        (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
      (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
      realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0)
    (v : ∀ j, ℝ ⊗[ℚ] (Fin 4 → W.rank.filtration.HigherHorizontal (d j)))
    (hv : ∀ j, v j ∈ (I.refilteredHorizontalImage i U (d j)).baseChange ℝ) :
    realifyFunctional W.vertical.frequency (W.rank.filtration.realHorizontalTreeValue d a
      (fun j => (LinearMap.proj (0 : Fin 4)).baseChange ℝ (v j))) +
    realifyFunctional W.vertical.frequency (W.rank.filtration.realHorizontalTreeValue d a
      (fun j => (LinearMap.proj (1 : Fin 4)).baseChange ℝ (v j))) -
    realifyFunctional W.vertical.frequency (W.rank.filtration.realHorizontalTreeValue d a
      (fun j => (LinearMap.proj (2 : Fin 4)).baseChange ℝ (v j))) -
    realifyFunctional W.vertical.frequency (W.rank.filtration.realHorizontalTreeValue d a
      (fun j => (LinearMap.proj (3 : Fin 4)).baseChange ℝ (v j))) = 0 := by
  apply W.rank.filtration.real_layerHorizontalImage_frequency
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U)
    W.vertical.frequency d a hd hr ?_ v hv
  intro z hz
  rw [← I.real_rankProjection_frequency i]
  exact hker z hz

end Erdos3.NativeRankInterval

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

noncomputable def fourRankBasis {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p) :
    Basis (Σ _ : Fin 4, Fin W.dim) ℚ (Fin 4 → W.L) :=
  Pi.basis (fun _ : Fin 4 => W.model.basis)

end NativeDegreeRankFamily

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem rankProjection_coordinates
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (j : Σ _ : Fin 4, Fin W.dim) :
    W.fourRankBasis.repr (I.rankProjection i x) j =
      (pi (I.productModels i)).basis.repr x
        ((Fintype.equivFin (Σ k : Option (Fin 4),
          Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
          ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩) := by
  change (Pi.basis (fun _ : Fin 4 => W.model.basis)).repr (I.rankProjection i x) j = _
  rw [Pi.basis_repr]
  let k : Σ a : Option (Fin 4), Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) a) :=
    ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩
  have hk := (Fintype.equivFin _).symm_apply_apply k
  have h := productFinBasis_repr (I.productModels i) x ((Fintype.equivFin _) k)
  have heq := congrArg (fun z : Σ a : Option (Fin 4),
      Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) a) =>
    (I.productModels i z.1).basis.repr (x z.1) z.2) hk
  exact (h.trans heq).symm

theorem rankProjection_coordinates_logHeight
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    {P : ℝ} (hx : ∀ j, rationalLogHeight ((pi (I.productModels i)).basis.repr x j) ≤ P)
    (j : Σ _ : Fin 4, Fin W.dim) :
    rationalLogHeight (W.fourRankBasis.repr (I.rankProjection i x) j) ≤ P := by
  rw [I.rankProjection_coordinates i x j]
  exact hx _

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold

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

theorem refilteredProjectionImage_mem_candidates
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r)
    (F : (piRank (I.productModels i) (I.productRanks i R₀)).AdaptedData)
    (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)
    (v : Fin (finrank ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) →
      (pi (I.productModels i)).filtration.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {P : ℝ} (hP : 0 ≤ P) (hF : F.rank.ComplexityLE P)
    (hforward : ∀ j k, rationalLogHeight ((pi (I.productModels i)).basis.repr (F.basis j) k) ≤ P)
    (hv : ∀ j k, rationalLogHeight
      (((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers).repr
        (v j) k) ≤ P) (d : ℕ) :
    I.refilteredProjectionImage i U d ∈
      heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
  have hdim : (Fintype.card (Fin (finrank ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))) : ℝ) ≤ P := by
    simpa only [Fintype.card_fin] using hF.1.1
  obtain ⟨a, ha⟩ := (pi (I.productModels i)).filtration.exists_refiltration_bases_in_coordinates
    F.basis F.weight F.layers (pi (I.productModels i)).basis U v hspan hP hdim hdim hv hforward d
  let z := fun j => I.rankProjection i (a j).val
  have hz : Submodule.span ℚ (Set.range z) = I.refilteredProjectionImage i U d := by
    have hsource := span_submodule_basis ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U d) a
    calc
      _ = (Submodule.span ℚ (Set.range (fun j => (a j).val))).map (I.rankProjection i).toLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = _ := congrArg (fun K => K.map (I.rankProjection i).toLinearMap) hsource
  apply bounded_submodule_spanning_mem_candidates W.fourRankBasis _ z hz
    (one_le_ceil_exp (refiltrationCoordinateBudget P))
  intro j k
  apply rationalHeightLE_ceil_exp
  exact I.rankProjection_coordinates_logHeight i (a j).val (ha j) k

end Erdos3.NativeRankInterval

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

theorem real_rankProjection_coordinates
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    (j : Σ _ : Fin 4, Fin W.dim) :
    (W.fourRankBasis.baseChange ℝ).repr ((I.rankProjection i).toLinearMap.baseChange ℝ x) j =
      ((pi (I.productModels i)).basis.baseChange ℝ).repr x
        ((Fintype.equivFin (Σ k : Option (Fin 4),
          Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
          ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
    exact congrArg (fun q : ℚ => q • a) (I.rankProjection_coordinates i x j)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem real_rankProjection_abs_bound
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    {B : ℝ} (hx : ∀ j, |((pi (I.productModels i)).basis.baseChange ℝ).repr x j| ≤ B)
    (j : Σ _ : Fin 4, Fin W.dim) :
    |(W.fourRankBasis.baseChange ℝ).repr ((I.rankProjection i).toLinearMap.baseChange ℝ x) j| ≤ B := by
  rw [I.real_rankProjection_coordinates i]
  exact hx _

theorem real_rankProjection_grid (l : ℕ)
    (x : ℝ ⊗[ℚ] (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
    (hx : (fun j => ((pi (I.productModels i)).basis.baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    (fun j => (W.fourRankBasis.baseChange ℝ).repr
      ((I.rankProjection i).toLinearMap.baseChange ℝ x) j) ∈ realDenominatorGrid l := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨fun j => a ((Fintype.equivFin (Σ k : Option (Fin 4),
    Fin (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k)))
      ⟨some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j.1), j.2⟩), ?_⟩
  funext j
  exact (congrFun ha _).trans
    (congrArg (fun y : ℝ => (l : ℝ) * y) (I.real_rankProjection_coordinates i x j)).symm

end Erdos3.NativeRankInterval

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

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

structure SunflowerWitness (I : NativeRankInterval W out H t branch p q) (P : ℝ) where
  index : Fin I.expansion.count
  lowerRank : ((I.expansion.model index).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r
  lower_complexity : lowerRank.ComplexityLE P
  lower_top : lowerRank.realSubgroup s r = ⊥
  adapted : (piRank (I.productModels index) (I.productRanks index lowerRank)).AdaptedData
  adapted_complexity : adapted.rank.ComplexityLE P
  forward : ∀ j k, rationalLogHeight ((pi (I.productModels index)).basis.repr (adapted.basis j) k) ≤ P
  backward : ∀ k j, rationalLogHeight (adapted.basis.repr ((pi (I.productModels index)).basis k) j) ≤ P
  denominator : ℕ
  subalgebra : LieSubalgebra ℚ (pi (I.productModels index)).filtration.AssociatedGraded
  spanning : Fin (finrank ℚ (∀ k : Option (Fin 4),
    optionLieSpace (I.expansion.L index) (fun _ : Fin 4 => W.L) k)) →
    (pi (I.productModels index)).filtration.AssociatedGraded
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp P
  span : Submodule.span ℚ (Set.range spanning) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (I.productModels index)).filtration.associatedGradedBasis adapted.basis adapted.weight adapted.layers)
    adapted.weight subalgebra.toSubmodule
  height : ∀ j k, rationalLogHeight
    (((pi (I.productModels index)).filtration.associatedGradedBasis adapted.basis adapted.weight adapted.layers).repr
      (spanning j) k) ≤ P
  bracket : I.BracketKernel index subalgebra
  sunflower : I.SunflowerKernel index subalgebra
  factorization : (pi (I.productModels index)).filtration.SymbolFactorizationIn
    adapted.basis adapted.weight adapted.layers (fun _ : Unit => (I.length : ℝ))
    (I.productSymbol index adapted.basis adapted.weight adapted.layers) P denominator subalgebra

namespace SunflowerWitness

variable {I : NativeRankInterval W out H t branch p q} {P : ℝ} (D : I.SunflowerWitness P)

noncomputable def projection (d : ℕ) : Submodule ℚ (Fin 4 → W.L) :=
  I.refilteredProjectionImage D.index D.subalgebra d

theorem projection_mem_candidates (hP : 0 ≤ P) (d : ℕ) :
    D.projection d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
      ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ :=
  I.refilteredProjectionImage_mem_candidates D.index D.lowerRank D.adapted D.subalgebra
    D.spanning D.span hP D.adapted_complexity D.forward D.height d

theorem horizontalImage_eq (d : ℕ) :
    I.refilteredHorizontalImage D.index D.subalgebra d =
      W.rank.filtration.horizontalImageOfSubmodule (D.projection d) d :=
  I.refilteredHorizontalImage_eq D.index D.subalgebra d

end SunflowerWitness

end NativeRankInterval

theorem exists_rank_sunflower_witness (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      Real.exp ((p + C) ^ C) ≤ (I.length : ℝ) →
      Nonempty (I.SunflowerWitness ((p + C) ^ C)) := by
  obtain ⟨C, hC, hexists⟩ := exists_rank_interval_sunflower s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  obtain ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, l, U, v, hl, hlp, hv, hU, hheight,
    hker, hsunflower, hinside⟩ := hexists hp hbp I hlarge
  exact ⟨{
    index := i
    lowerRank := R₀
    lower_complexity := hR₀
    lower_top := hzero
    adapted := F
    adapted_complexity := hF
    forward := hforward
    backward := hback
    denominator := l
    subalgebra := U
    spanning := v
    denominator_pos := hl
    denominator_bound := hlp
    span := hv
    graded := hU
    height := hheight
    bracket := hker
    sunflower := hsunflower
    factorization := hinside
  }⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_projection_family
    {α : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {t : α → ZMod N × ZMod N × ZMod N} {branch : Bool}
    (I : ∀ a, NativeRankInterval W out H (t a) branch p q)
    (S : Finset α) (hS : S.Nonempty) (hP : 0 ≤ P)
    (D : ∀ a ∈ S, (I a).SunflowerWitness P) :
    ∃ (K : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)) (T : Finset α),
      T ⊆ S ∧ T.Nonempty ∧
      Real.exp (-(3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
        Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2)) * (s + 1)) *
        S.card ≤ (T.card : ℝ) ∧
      (∀ d, K d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊) ∧
      ∀ a ∈ T, ∃ E : (I a).SunflowerWitness P,
        (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
        ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
          W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
  classical
  let code (a : α) : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L) :=
    if ha : a ∈ S then fun d => (D a ha).projection d.val else 0
  have hcode (a : α) (ha : a ∈ S) : code a = fun d => (D a ha).projection d.val := by
    simp only [code, dite_eq_left ha]
  have hmem : ∀ a ∈ S, ∀ d, code a d ∈
      heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
    intro a ha d
    rw [hcode a ha]
    exact (D a ha).projection_mem_candidates hP d.val
  obtain ⟨a₀, ha₀, T, hTS, haT, hcommon, hsize⟩ := exists_common_height_bounded_subspace_family
    W.fourRankBasis S hS code (Fintype.card (Σ _ : Fin 4, Fin W.dim))
    (refiltrationCoordinateBudget_nonneg hP) hmem
  refine ⟨code a₀, T, hTS, ⟨a₀, haT⟩, ?_, hmem a₀ ha₀, ?_⟩
  · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hsize
  · intro a ha
    let E := D a (hTS ha)
    have heq (d : Fin (s + 1)) : E.projection d.val = code a₀ d := by
      have h := congrFun (hcommon a ha) d
      rwa [hcode a (hTS ha)] at h
    exact ⟨E, heq, fun d => (E.horizontalImage_eq d.val).trans (congrArg
      (fun B => W.rank.filtration.horizontalImageOfSubmodule B d.val) (heq d))⟩

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
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
  (I : NativeRankInterval W out H t branch p q)

noncomputable def projectedCoefficient (i : Fin I.expansion.count) (α : Unit →₀ ℕ) :
    (pi (I.productModels i)).filtration.PolynomialSymbol (fun _ : Unit => 1) →ₗ[ℚ]
      (Fin 4 → W.rank.filtration.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) α)) :=
  W.rank.filtration.projectedHorizontalSymbolCoefficient (pi (I.productModels i)).filtration
    (I.rankProjection i) (I.rankProjection_mem_layer i) (fun _ => 1) α

namespace SunflowerWitness

variable {I} {P : ℝ} (D : I.SunflowerWitness P)

theorem exists_projected_corrections (hs : 1 ≤ s) :
    ∃ E R : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1),
      (pi (I.productModels D.index)).filtration.SymbolSlowBound
        D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1)
        (fun _ => (I.length : ℝ)) (Real.exp P) E ∧
      (pi (I.productModels D.index)).filtration.SymbolRationalGrid
        D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) D.denominator R ∧
      ∀ α : Unit →₀ ℕ,
        (I.projectedCoefficient D.index α).baseChange ℝ
            (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord -
          (I.projectedCoefficient D.index α).baseChange ℝ E.coord -
          (I.projectedCoefficient D.index α).baseChange ℝ R.coord ∈
        (I.refilteredHorizontalImage D.index D.subalgebra (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  exact W.rank.filtration.projectedHorizontal_factorization (pi (I.productModels D.index)).filtration
    (I.rankProjection D.index) (I.rankProjection_mem_layer D.index) hs
    D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => (I.length : ℝ))
    (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers)
    P D.denominator D.subalgebra D.factorization

end SunflowerWitness

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

noncomputable def mono (D : I.SunflowerWitness P) (hPQ : P ≤ Q) : I.SunflowerWitness Q :=
  { D with
    lower_complexity := D.lower_complexity.mono D.lowerRank hPQ
    adapted_complexity := D.adapted_complexity.mono D.adapted.rank hPQ
    forward := fun j k => (D.forward j k).trans hPQ
    backward := fun k j => (D.backward k j).trans hPQ
    denominator_bound := D.denominator_bound.trans (Real.exp_le_exp.mpr hPQ)
    height := fun j k => (D.height j k).trans hPQ
    factorization := NilpotentLieFiltration.SymbolFactorizationIn.mono
      (pi (I.productModels D.index)).filtration D.adapted.basis D.adapted.weight D.adapted.layers
      D.factorization hPQ (fun _ => by exact_mod_cast I.length_pos) }

theorem mono_projection (D : I.SunflowerWitness P) (hPQ : P ≤ Q) (d : ℕ) :
    (D.mono hPQ).projection d = D.projection d := rfl

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

noncomputable def projectedRepresentative
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) : ℝ ⊗[ℚ] (Fin 4 → W.L) :=
  (I.rankProjection D.index).toLinearMap.baseChange ℝ
    (coefficients ((pi (I.productModels D.index)).filtration.realSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord) α)

noncomputable def projectedDenominator : ℕ :=
  matrixDenominator (fun i j => (pi (I.productModels D.index)).basis.repr (D.adapted.basis j) i) *
    D.denominator

theorem projectedDenominator_pos : 0 < D.projectedDenominator :=
  Nat.mul_pos (matrixDenominator_pos _) D.denominator_pos

theorem projectedDenominator_bound (hP : 0 ≤ P) :
    (D.projectedDenominator : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) := by
  have hdim := D.adapted_complexity.1.1
  apply NilpotentLieFiltration.original_coordinate_denominator_bound D.adapted.basis
    (pi (I.productModels D.index)).basis hP
  · simpa only [Fintype.card_fin] using hdim
  · simpa only [← finrank_eq_card_basis (pi (I.productModels D.index)).basis] using hdim
  · exact D.forward
  · exact D.denominator_bound

theorem projectedRepresentative_slow (hP : 0 ≤ P)
    (E : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (hE : (pi (I.productModels D.index)).filtration.SymbolSlowBound
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1)
      (fun _ => (I.length : ℝ)) (Real.exp P) E) (α : Unit →₀ ℕ) (j : Σ _ : Fin 4, Fin W.dim) :
    |(W.fourRankBasis.baseChange ℝ).repr (D.projectedRepresentative E α) j| ≤
      Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
  apply I.real_rankProjection_abs_bound D.index
  intro k
  apply (pi (I.productModels D.index)).filtration.realSymbolRepresentative_slow_original_coordinates
    D.adapted.basis D.adapted.weight D.adapted.layers (pi (I.productModels D.index)).basis
    (fun _ : Unit => 1) (fun _ => (I.length : ℝ)) (fun _ => by exact_mod_cast I.length_pos) hP
  · simpa only [Fintype.card_fin] using D.adapted_complexity.1.1
  · exact D.forward
  · exact hE

theorem projectedRepresentative_grid
    (R : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (hR : (pi (I.productModels D.index)).filtration.SymbolRationalGrid
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) D.denominator R)
    (α : Unit →₀ ℕ) :
    (fun j => (W.fourRankBasis.baseChange ℝ).repr (D.projectedRepresentative R α) j) ∈
      realDenominatorGrid D.projectedDenominator := by
  unfold projectedDenominator projectedRepresentative
  have hgrid := (pi (I.productModels D.index)).filtration.realSymbolRepresentative_original_grid
    D.adapted.basis D.adapted.weight D.adapted.layers (pi (I.productModels D.index)).basis
    (fun _ : Unit => 1) D.denominator R hR α
  have hp := I.real_rankProjection_grid D.index
    (matrixDenominator (fun i j => (pi (I.productModels D.index)).basis.repr (D.adapted.basis j) i) *
      D.denominator)
    (coefficients ((pi (I.productModels D.index)).filtration.realSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) R.coord) α) hgrid
  convert hp using 2

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedRepresentative_mem
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) : D.projectedRepresentative X α ∈
      (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  have h := W.rank.filtration.real_projectedCoefficient_mem (pi (I.productModels D.index)).filtration
    (I.rankProjection D.index) (I.rankProjection_mem_layer D.index)
    D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) α
    ((pi (I.productModels D.index)).filtration.realAdaptedSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord)
  convert h using 2
  dsimp only [projectedRepresentative, NilpotentLieFiltration.realAdaptedSymbolRepresentative]

noncomputable def projectedRepresentativeLayer
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) :
    (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ :=
  ⟨D.projectedRepresentative X α, D.projectedRepresentative_mem X α⟩

theorem projectedRepresentative_horizontal
    (X : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) :
    W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
        (D.projectedRepresentativeLayer X α) =
      (I.projectedCoefficient D.index α).baseChange ℝ X.coord := by
  have h := W.rank.filtration.real_projectedCoefficient_horizontal
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) D.adapted.basis D.adapted.weight D.adapted.layers
    (fun _ => 1) α ((pi (I.productModels D.index)).filtration.realAdaptedSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) X.coord)
    (D.projectedRepresentativeLayer X α) (by
      dsimp only [projectedRepresentativeLayer, projectedRepresentative,
        NilpotentLieFiltration.realAdaptedSymbolRepresentative])
  rwa [NilpotentLieFiltration.realPolynomialSymbolMap_representative] at h

noncomputable def projectedOrbitCoefficient (α : Unit →₀ ℕ) :
    (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ :=
  ⟨(I.rankProjection D.index).toLinearMap.baseChange ℝ (coefficients (I.productOrbit D.index).log α),
    W.rank.filtration.real_projectedCoefficient_mem (pi (I.productModels D.index)).filtration
      (I.rankProjection D.index) (I.rankProjection_mem_layer D.index)
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) α
      ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩⟩

@[simp] theorem projectedOrbitCoefficient_coe (α : Unit →₀ ℕ) :
    (D.projectedOrbitCoefficient α : ℝ ⊗[ℚ] (Fin 4 → W.L)) =
      (I.rankProjection D.index).toLinearMap.baseChange ℝ
        (coefficients (I.productOrbit D.index).log α) := rfl

theorem projectedOrbitCoefficient_horizontal (α : Unit →₀ ℕ) :
    W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
        (D.projectedOrbitCoefficient α) =
      (I.projectedCoefficient D.index α).baseChange ℝ
        (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord := by
  exact W.rank.filtration.real_projectedCoefficient_horizontal
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) D.adapted.basis D.adapted.weight D.adapted.layers
    (fun _ => 1) α ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩
    (D.projectedOrbitCoefficient α) rfl

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

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
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)
  (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
  (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))

theorem projectedSymbol_native_component (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        ((I.projectedCoefficient D.index α).baseChange ℝ
          (I.productSymbol D.index D.adapted.basis D.adapted.weight D.adapted.layers).coord) =
      W.horizontalCoefficient hs c τ hG α
        (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)) := by
  have h := W.rank.filtration.projectedHorizontalSymbolCoefficient_native
    (pi (I.productModels D.index)).filtration (I.rankProjection D.index)
    (I.rankProjection_mem_layer D.index) hs D.adapted.basis D.adapted.weight D.adapted.layers
    c τ hG (fun _ : Unit => 1) α
    ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩
    (W.rank.orbitEquiv (fun _ => 1)
      (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
        ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit) k (by
      exact (I.rankProjection_component_log D.index k).trans
        (W.rank.orbitEquiv_log (fun _ : Unit => 1)
          (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
            ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit).symm)
  exact h.trans (W.fourPoint_horizontalCoefficient hs c τ hG out
    (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch) α
    ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))

theorem projectedOrbitCoefficient_native_component (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
          (D.projectedOrbitCoefficient α)) =
      W.horizontalCoefficient hs c τ hG α
        (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)) := by
  exact (congrArg ((LinearMap.proj k).baseChange ℝ) (D.projectedOrbitCoefficient_horizontal α)).trans
    (D.projectedSymbol_native_component hs c τ hG α k)

end Erdos3.NativeRankInterval.SunflowerWitness

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

variable {A κ : Type*} {s r : ℕ} {b : ℝ} (W : NativeDegreeRankFamily s r A b)

theorem logCoefficient_mem_rank_one (α : Unit →₀ ℕ) (a : A) :
    coefficients (W.orbit a).log α ∈
      (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ := by
  have h := W.rank.filtration.polynomialOrbit_coefficient_mem_rank_one (fun _ : Unit => 1) α
    (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a))
  exact (congrArg (fun z => coefficients z α ∈
    (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ)
    (W.rank.orbitEquiv_log (fun _ : Unit => 1) (W.orbit a))).mp h

theorem horizontalCoefficient_real_log (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i})) (α : Unit →₀ ℕ) (a : A)
    (v : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ)
    (hv : v.val = coefficients (W.orbit a).log α) :
    W.horizontalCoefficient hs c τ hG α a =
      W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) v := by
  apply W.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs c τ hG
    (fun _ : Unit => 1) α (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a)) v
  exact hv.trans (congrArg (fun z => coefficients z α)
    (W.rank.orbitEquiv_log (fun _ : Unit => 1) (W.orbit a))).symm

end NativeDegreeRankFamily

namespace NativeRankInterval.SunflowerWitness

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedOrbitCoefficient_native_log_mod_kernel
    (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i})) (α : Unit →₀ ℕ) (k : Fin 4) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (D.projectedOrbitCoefficient α).val k -
      coefficients (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α ∈
        (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).baseChange ℝ := by
  let a := rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)
  let v := W.rank.filtration.realFourLayerComponent (Finsupp.weight (fun _ : Unit => 1) α) k
    (D.projectedOrbitCoefficient α)
  let z : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ :=
    ⟨coefficients (W.orbit a).log α, W.logCoefficient_mem_rank_one α a⟩
  have heq : W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) v =
      W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) z :=
    (W.rank.filtration.realFourLayerComponent_horizontal _ k (D.projectedOrbitCoefficient α)).symm.trans
      ((D.projectedOrbitCoefficient_native_component hs c τ hG α k).trans
        (W.horizontalCoefficient_real_log hs c τ hG α a z rfl))
  have h := (W.rank.filtration.realHorizontalMap_eq _ v z).mp heq
  simpa only [v, z, a, W.rank.filtration.realFourLayerComponent_coe, real_four_projection] using h

end NativeRankInterval.SunflowerWitness
end Erdos3

end

end OAI
