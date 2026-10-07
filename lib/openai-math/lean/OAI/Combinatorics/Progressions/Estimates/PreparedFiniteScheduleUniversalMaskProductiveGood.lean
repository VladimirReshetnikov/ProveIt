import Mathlib.Data.Fin.Tuple.Basic
import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteScheduleUniversalDegreeModel

namespace OAI

section

namespace Erdos3

structure FinitePrecenterInputFamily (X : Type*) (p countLog : ℝ) where
  Branch : Type
  [branchFintype : Fintype Branch]
  input : Branch → X → ℂ
  norm : ∀ branch x, ‖input branch x‖ ≤ Real.exp p
  card : (Fintype.card Branch : ℝ) ≤ Real.exp countLog

attribute [instance] FinitePrecenterInputFamily.branchFintype

structure FinitePrecenterSelectedModels (X : Type*) where
  Branch : Type
  [branchFintype : Fintype Branch]
  input : Branch → X → ℂ
  models : Branch → CenteredForecastModel X

attribute [instance] FinitePrecenterSelectedModels.branchFintype

def FinitePrecenterInputFamily.withModels {X : Type*} {p countLog : ℝ}
    (family : FinitePrecenterInputFamily X p countLog)
    (models : family.Branch → CenteredForecastModel X) :
    FinitePrecenterSelectedModels X where
  Branch := family.Branch
  input := family.input
  models := models

abbrev FinitePrecenterValidPrefix (X : Type*)
    (Bounds : ℕ → FinitePrecenterSelectedModels X → Prop) (n : ℕ) :=
  (i : Fin n) → {raw : FinitePrecenterSelectedModels X // Bounds i.val raw}

namespace FinitePrecenterModelSelection

variable {X : Type*} {depth : ℕ}
    (p countLog : Fin depth → ℝ)
    (Bounds : ℕ → FinitePrecenterSelectedModels X → Prop)
    (next : (n : Fin depth) → FinitePrecenterValidPrefix X Bounds n.val →
      FinitePrecenterInputFamily X (p n) (countLog n))
    (hmodels : ∀ n modelPrefix, ∃ models : (next n modelPrefix).Branch → CenteredForecastModel X,
      Bounds n.val ((next n modelPrefix).withModels models))

noncomputable def step (n : Fin depth) (modelPrefix : FinitePrecenterValidPrefix X Bounds n.val) :
    {raw : FinitePrecenterSelectedModels X // Bounds n.val raw} :=
  ⟨(next n modelPrefix).withModels (Classical.choose (hmodels n modelPrefix)),
    Classical.choose_spec (hmodels n modelPrefix)⟩

theorem step_eq (n : Fin depth) (modelPrefix : FinitePrecenterValidPrefix X Bounds n.val) :
    ∃ models : (next n modelPrefix).Branch → CenteredForecastModel X,
      (step p countLog Bounds next hmodels n modelPrefix).val = (next n modelPrefix).withModels models ∧
      Bounds n.val ((next n modelPrefix).withModels models) :=
  ⟨Classical.choose (hmodels n modelPrefix), rfl, Classical.choose_spec (hmodels n modelPrefix)⟩

noncomputable def modelPrefix
    (p countLog : Fin depth → ℝ)
    (Bounds : ℕ → FinitePrecenterSelectedModels X → Prop)
    (next : (n : Fin depth) → FinitePrecenterValidPrefix X Bounds n.val →
      FinitePrecenterInputFamily X (p n) (countLog n))
    (hmodels : ∀ n history, ∃ models : (next n history).Branch → CenteredForecastModel X,
      Bounds n.val ((next n history).withModels models)) :
    (n : ℕ) → n ≤ depth → FinitePrecenterValidPrefix X Bounds n
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, hn => Fin.snoc
      (modelPrefix p countLog Bounds next hmodels n (Nat.le_of_succ_le hn))
      (step p countLog Bounds next hmodels ⟨n, Nat.lt_of_succ_le hn⟩
        (modelPrefix p countLog Bounds next hmodels n (Nat.le_of_succ_le hn)))

@[simp] theorem prefix_zero (h : 0 ≤ depth) :
    modelPrefix p countLog Bounds next hmodels 0 h = (fun i => Fin.elim0 i) := rfl

@[simp] theorem prefix_succ (n : ℕ) (hn : n + 1 ≤ depth) :
    modelPrefix p countLog Bounds next hmodels (n + 1) hn =
      Fin.snoc (modelPrefix p countLog Bounds next hmodels n (Nat.le_of_succ_le hn))
        (step p countLog Bounds next hmodels ⟨n, Nat.lt_of_succ_le hn⟩
          (modelPrefix p countLog Bounds next hmodels n (Nat.le_of_succ_le hn))) := rfl

@[simp] theorem prefix_castSucc (n : ℕ) (hn : n + 1 ≤ depth) (i : Fin n) :
    modelPrefix p countLog Bounds next hmodels (n + 1) hn i.castSucc =
      modelPrefix p countLog Bounds next hmodels n (Nat.le_of_succ_le hn) i := by
  exact Fin.snoc_castSucc _ _ _

@[simp] theorem prefix_last (n : ℕ) (hn : n + 1 ≤ depth) :
    modelPrefix p countLog Bounds next hmodels (n + 1) hn (Fin.last n) =
      step p countLog Bounds next hmodels ⟨n, Nat.lt_of_succ_le hn⟩
        (modelPrefix p countLog Bounds next hmodels n (Nat.le_of_succ_le hn)) := by
  exact Fin.snoc_last _ _

theorem prefix_castLE : ∀ (k : ℕ) (hk : k ≤ depth) (n : ℕ) (hn : n ≤ depth)
    (hnk : n ≤ k) (i : Fin n),
    modelPrefix p countLog Bounds next hmodels k hk (i.castLE hnk) =
      modelPrefix p countLog Bounds next hmodels n hn i := by
  intro k
  induction k with
  | zero =>
      intro hk n hn hnk i
      have : n = 0 := Nat.eq_zero_of_le_zero hnk
      subst n
      exact Fin.elim0 i
  | succ k ih =>
      intro hk n hn hnk i
      rcases eq_or_lt_of_le hnk with rfl | hlt
      · rfl
      · have hnk' : n ≤ k := Nat.le_of_lt_succ hlt
        change modelPrefix p countLog Bounds next hmodels (k + 1) hk
          ((i.castLE hnk').castSucc) = _
        rw [prefix_castSucc]
        exact ih _ n hn hnk' i

noncomputable def selected : FinitePrecenterValidPrefix X Bounds depth :=
  modelPrefix p countLog Bounds next hmodels depth le_rfl

theorem selected_eq_step (n : Fin depth) :
    selected p countLog Bounds next hmodels n =
      step p countLog Bounds next hmodels n
        (modelPrefix p countLog Bounds next hmodels n.val (Nat.le_of_lt n.isLt)) := by
  have h := prefix_castLE p countLog Bounds next hmodels depth le_rfl
    (n.val + 1) n.isLt n.isLt (Fin.last n.val)
  change selected p countLog Bounds next hmodels n = _ at h
  exact h.trans (prefix_last p countLog Bounds next hmodels n.val n.isLt)

theorem selected_eq_withModels (n : Fin depth) :
    let family := next n (modelPrefix p countLog Bounds next hmodels n.val (Nat.le_of_lt n.isLt))
    ∃ models : family.Branch → CenteredForecastModel X,
      (selected p countLog Bounds next hmodels n).val = family.withModels models ∧
      Bounds n.val (family.withModels models) := by
  rw [selected_eq_step]
  exact step_eq p countLog Bounds next hmodels n _

theorem selected_castLE (n : ℕ) (hn : n ≤ depth) (i : Fin n) :
    selected p countLog Bounds next hmodels (i.castLE hn) =
      modelPrefix p countLog Bounds next hmodels n hn i :=
  prefix_castLE p countLog Bounds next hmodels depth le_rfl n hn hn i

include hmodels in

theorem exists_selection :
    ∃ chosen : FinitePrecenterValidPrefix X Bounds depth,
      ∀ n : Fin depth,
      let history : FinitePrecenterValidPrefix X Bounds n.val :=
        fun i => chosen (i.castLE (Nat.le_of_lt n.isLt))
      let family := next n history
      ∃ models : family.Branch → CenteredForecastModel X,
        (chosen n).val = family.withModels models ∧
        Bounds n.val (family.withModels models) := by
  refine ⟨selected p countLog Bounds next hmodels, ?_⟩
  intro n
  have hhistory :
      (fun i : Fin n.val => selected p countLog Bounds next hmodels
        (i.castLE (Nat.le_of_lt n.isLt))) =
      modelPrefix p countLog Bounds next hmodels n.val (Nat.le_of_lt n.isLt) := by
    funext i
    exact selected_castLE p countLog Bounds next hmodels n.val (Nat.le_of_lt n.isLt) i
  dsimp only
  rw [hhistory]
  exact selected_eq_withModels p countLog Bounds next hmodels n

end FinitePrecenterModelSelection
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

abbrev ExternalHistoryMaskIndex {History : Type*}
    (Freq Bin : History → Type*) := Σ h, Freq h × Bin h

noncomputable def externalHistoryMaskFamily
    {History X : Type*} {Freq Bin Y : History → Type*}
    (F : ∀ h, Freq h → X → Y h → ℂ)
    (centers : ∀ h, Freq h → Bin h → Y h → ℂ) {ε : History → ℝ}
    (hnet : ∀ h f x, ∃ i, ∀ y, ‖F h f x y - centers h f i y‖ ≤ ε h)
    (input : X → ℂ) : ExternalHistoryMaskIndex Freq Bin → X → ℂ :=
  fun b => externalNetMaskFamily (F b.1) (centers b.1) (hnet b.1) input b.2

theorem externalHistoryMaskFamily_at
    {History X : Type*} {Freq Bin Y : History → Type*}
    (F : ∀ h, Freq h → X → Y h → ℂ)
    (centers : ∀ h, Freq h → Bin h → Y h → ℂ) {ε : History → ℝ}
    (hnet : ∀ h f x, ∃ i, ∀ y, ‖F h f x y - centers h f i y‖ ≤ ε h)
    (input : X → ℂ) (h : History) (b : Freq h × Bin h) :
    externalHistoryMaskFamily F centers hnet input ⟨h, b⟩ =
      externalNetMaskFamily (F h) (centers h) (hnet h) input b := rfl

theorem externalNetMaskFamily_norm_le
    {Freq X Y I : Type*} (F : Freq → X → Y → ℂ)
    (centers : Freq → I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ f x, ∃ i, ∀ y, ‖F f x y - centers f i y‖ ≤ ε)
    (input : X → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hinput : ∀ x, ‖input x‖ ≤ B) (b : Freq × I) (x : X) :
    ‖externalNetMaskFamily F centers hnet input b x‖ ≤ B := by
  unfold externalNetMaskFamily
  split_ifs
  · exact hinput x
  · simpa only [norm_zero] using hB

theorem externalHistoryMaskFamily_norm_le
    {History X : Type*} {Freq Bin Y : History → Type*}
    (F : ∀ h, Freq h → X → Y h → ℂ)
    (centers : ∀ h, Freq h → Bin h → Y h → ℂ) {ε : History → ℝ}
    (hnet : ∀ h f x, ∃ i, ∀ y, ‖F h f x y - centers h f i y‖ ≤ ε h)
    (input : X → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hinput : ∀ x, ‖input x‖ ≤ B)
    (b : ExternalHistoryMaskIndex Freq Bin) (x : X) :
    ‖externalHistoryMaskFamily F centers hnet input b x‖ ≤ B :=
  externalNetMaskFamily_norm_le (F b.1) (centers b.1) (hnet b.1)
    input hB hinput b.2 x

theorem externalHistoryMaskFamily_real_norm_le_exp
    {History X : Type*} {Freq Bin Y : History → Type*}
    (F : ∀ h, Freq h → X → Y h → ℂ)
    (centers : ∀ h, Freq h → Bin h → Y h → ℂ) {ε : History → ℝ}
    (hnet : ∀ h f x, ∃ i, ∀ y, ‖F h f x y - centers h f i y‖ ≤ ε h)
    (input : X → ℝ) {p : ℝ} (hinput : ∀ x, |input x| ≤ Real.exp p)
    (b : ExternalHistoryMaskIndex Freq Bin) (x : X) :
    ‖externalHistoryMaskFamily F centers hnet (fun x => (input x : ℂ)) b x‖ ≤
      Real.exp p := by
  apply externalHistoryMaskFamily_norm_le F centers hnet _ (Real.exp_nonneg p)
  intro y
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hinput y

theorem externalHistoryMaskIndex_card_le_exp
    {History : Type*} [Fintype History] (Freq Bin : History → Type*)
    [∀ h, Fintype (Freq h)] [∀ h, Fintype (Bin h)]
    {historyLog frequencyLog binLog : ℝ}
    (hh : (Fintype.card History : ℝ) ≤ Real.exp historyLog)
    (hf : ∀ h, (Fintype.card (Freq h) : ℝ) ≤ Real.exp frequencyLog)
    (hi : ∀ h, (Fintype.card (Bin h) : ℝ) ≤ Real.exp binLog) :
    (Fintype.card (ExternalHistoryMaskIndex Freq Bin) : ℝ) ≤
      Real.exp (historyLog + frequencyLog + binLog) := by
  classical
  simp only [ExternalHistoryMaskIndex, Fintype.card_sigma, Fintype.card_prod,
    Nat.cast_sum, Nat.cast_mul]
  calc
    ∑ h, (Fintype.card (Freq h) : ℝ) * Fintype.card (Bin h)
        ≤ ∑ _h : History, Real.exp frequencyLog * Real.exp binLog := by
      exact Finset.sum_le_sum (fun h _ =>
        mul_le_mul (hf h) (hi h) (Nat.cast_nonneg _) (Real.exp_nonneg _))
    _ = (Fintype.card History : ℝ) * (Real.exp frequencyLog * Real.exp binLog) := by
      simp
    _ ≤ Real.exp historyLog * (Real.exp frequencyLog * Real.exp binLog) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = Real.exp (historyLog + frequencyLog + binLog) := by
      rw [Real.exp_add, Real.exp_add]
      ring

end Erdos3

end

section

namespace Erdos3

variable {History : Type} {X : Type*} {Freq Bin : History → Type}
    {Y : History → Type*} [Fintype History]
    [∀ h, Fintype (Freq h)] [∀ h, Fintype (Bin h)]
    (F : ∀ h, Freq h → X → Y h → ℂ)
    (netCenters : ∀ h, Freq h → Bin h → Y h → ℂ) {ε : History → ℝ}
    (hnet : ∀ h f x, ∃ i, ∀ y, ‖F h f x y - netCenters h f i y‖ ≤ ε h)
    (a : X → ℝ) {p historyLog frequencyLog binLog : ℝ}
    (ha : ∀ x, |a x| ≤ Real.exp p)
    (hHistory : (Fintype.card History : ℝ) ≤ Real.exp historyLog)
    (hFrequency : ∀ h, (Fintype.card (Freq h) : ℝ) ≤ Real.exp frequencyLog)
    (hBin : ∀ h, (Fintype.card (Bin h) : ℝ) ≤ Real.exp binLog)

noncomputable def externalHistoryPrecenterInputFamily :
    FinitePrecenterInputFamily X p (historyLog + frequencyLog + binLog) where
  Branch := ExternalHistoryMaskIndex Freq Bin
  input := externalHistoryMaskFamily F netCenters hnet (fun x => (a x : ℂ))
  norm := externalHistoryMaskFamily_real_norm_le_exp F netCenters hnet a ha
  card := externalHistoryMaskIndex_card_le_exp Freq Bin hHistory hFrequency hBin

@[simp] theorem externalHistoryPrecenterInputFamily_input
    (branch : ExternalHistoryMaskIndex Freq Bin) (x : X) :
    (externalHistoryPrecenterInputFamily F netCenters hnet a ha
      hHistory hFrequency hBin).input branch x =
      externalHistoryMaskFamily F netCenters hnet (fun x => (a x : ℂ)) branch x := rfl

@[simp] theorem externalHistoryPrecenterInputFamily_at
    (h : History) (branch : Freq h × Bin h) :
    (externalHistoryPrecenterInputFamily F netCenters hnet a ha
      hHistory hFrequency hBin).input ⟨h, branch⟩ =
      externalNetMaskFamily (F h) (netCenters h) (hnet h)
        (fun x => (a x : ℂ)) branch := rfl

@[simp] theorem externalHistoryPrecenterInputFamily_withModels_input
    (models : ExternalHistoryMaskIndex Freq Bin → CenteredForecastModel X) :
    ((externalHistoryPrecenterInputFamily F netCenters hnet a ha
      hHistory hFrequency hBin).withModels models).input =
      externalHistoryMaskFamily F netCenters hnet (fun x => (a x : ℂ)) := rfl

@[simp] theorem externalHistoryPrecenterInputFamily_withModels_models
    (models : ExternalHistoryMaskIndex Freq Bin → CenteredForecastModel X) :
    ((externalHistoryPrecenterInputFamily F netCenters hnet a ha
      hHistory hFrequency hBin).withModels models).models = models := rfl

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable section

attribute [local irreducible] preparedSamplerTransverse preparedCommonBlockCount RankPreparationLayer.rank
attribute [local irreducible] PreparedFiniteScheduleDegreeModelsAtLaw integerBox allocatedPrincipalSides

variable
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    (bW : ∀ j, Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))

local instance (j : Fin m) : DecidableEq (PreparedSamplerContinuous prep j) := Classical.decEq _
local instance (a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)) :
    DecidableEq (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)) a) :=
  Classical.decEq _

variable
    (Pdetect : Polynomial ℕ) (hbox : (integerBox N).Nonempty)
    (physical : (bases × rectangularWeightIndices 0 width 1) → integerBox (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value)
      (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)) → integerBox N)
variable
    {Stage : Type} [Fintype Stage]
    (degree : Stage → ℕ) (u p cap sliceLog testLog budget E : Stage → ℝ)
variable
    (hModel : ∀ k : Stage, PreparedFiniteScheduleDegreeModelsAtLaw
      (m := m) (nX := nX) (R := R) (σ := σ)
      (Path := bases × rectangularWeightIndices 0 width 1) (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N Pdetect μ poly hbox law hweight
      physical (degree k) (u k) (p k) (cap k) (sliceLog k) (testLog k) (budget k) (E k))
variable
    {Tests : Stage → (bases × rectangularWeightIndices 0 width 1) → Type} [∀ k z, Nonempty (Tests k z)]
    {Ldetect : ∀ k z, Tests k z → Type} [∀ k z j, LieRing (Ldetect k z j)]
    [∀ k z j, LieAlgebra ℚ (Ldetect k z j)] {dims : ∀ k z, Tests k z → ℕ}
    [∀ k z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, T2Space (ℝ ⊗[ℚ] Ldetect k z j)]
variable
    (Ddetect : ∀ k z j, RationalFilteredNilmanifold (Ldetect k z j) (degree k) (dims k z j))
    (Vdetect : ∀ k z j, (Ddetect k z j).Niltest (fun _ : LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) => 1))
variable
    (slices : ∀ k z, Tests k z → Finset (integerBox
      (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value) (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S))))
    (cdetect : ∀ k z, Tests k z → LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    (stepdetect : ∀ k z, Tests k z → ℕ)
    (Hdetect : ∀ k z, Tests k z → LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℕ)
variable
    (hstep : ∀ k z j, 0 < stepdetect k z j)
    (hSlices : ∀ k z j, (slices k z j).image Subtype.val =
      commonStrideBox (cdetect k z j) (stepdetect k z j) (Hdetect k z j))
    (hDense : ∀ k z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value) (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)) (sliceLog k)
      ((slices k z j).image Subtype.val))
variable
    (hnum : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    (hcomplex : ∀ k z j, (Vdetect k z j).ComplexityLE
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k)))
    (hcap : ∀ k z j, ((Vdetect k z j).normBound : ℝ) ≤ 1)
variable
    {Forecast : Stage → Type} [∀ k, Nonempty (Forecast k)]
    (Pnative massLog capLog Edata : Stage → ℝ)
    (data : ∀ k, Forecast k → ActualForecastData N poly (Pnative k) (massLog k) (capLog k) (Edata k))
variable
    (hNative : ∀ k, 0 ≤ Pnative k)
    (hAccuracy : ∀ k, 2 * u k + 4 * p k + 12 ≤ Edata k)
    (hCap : ∀ k, Real.exp (capLog k) ≤ cap k)
    (hPrecision : ∀ k, actualForecastDataModelRequired (budget k) (Pnative k) (massLog k)
      (u k) (p k) ≤ E k)
variable
    {History : Stage → Type} [∀ k, Fintype (History k)]
    {Freq Bin Y : ∀ k, History k → Type}
    [∀ k h, Fintype (Freq k h)] [∀ k h, Fintype (Bin k h)]
    (F : ∀ k h, Freq k h → integerBox N → Y k h → ℂ)
    (netCenters : ∀ k h, Freq k h → Bin k h → Y k h → ℂ)
    {ε : ∀ k, History k → ℝ}
    (hnet : ∀ k h f x, ∃ i, ∀ y, ‖F k h f x y - netCenters k h f i y‖ ≤ ε k h)
variable
    (a : integerBox N → ℝ) (inputCap : ℝ)
    (ha : ∀ x, |a x| ≤ Real.exp inputCap)
    (hInputCap : ∀ k, inputCap ≤ p k)
variable
    (historyLog frequencyLog binLog Eres : Stage → ℝ) (stageLog : ℝ)
    (hHistory : ∀ k, (Fintype.card (History k) : ℝ) ≤ Real.exp (historyLog k))
    (hFrequency : ∀ k h, (Fintype.card (Freq k h) : ℝ) ≤ Real.exp (frequencyLog k))
    (hBin : ∀ k h, (Fintype.card (Bin k h) : ℝ) ≤ Real.exp (binLog k))
    (hStageCount : (Fintype.card Stage : ℝ) + 1 ≤ Real.exp stageLog)
    (hErrorBudget : ∀ k, historyLog k + frequencyLog k + binLog k + gainLog +
      Eres k + stageLog + 6 ≤ u k)

include hgood hproductive htest hgain hmean hModel hstep hSlices hDense hnum hcomplex hcap
  hNative hAccuracy hCap hPrecision ha hInputCap hHistory hFrequency hBin
  hStageCount hErrorBudget in

theorem exists_preparedFiniteScheduleExternalMaskProductiveGood :
    let input : ∀ k, ExternalHistoryMaskIndex (Freq k) (Bin k) → integerBox N → ℂ :=
      fun k => externalHistoryMaskFamily (F k) (netCenters k) (hnet k)
        (fun x => (a x : ℂ))
    let tests : ∀ k z, Tests k z → integerBox
        (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value) (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)) → ℂ :=
      fun k z j t => star ((Vdetect k z j).eval
        (commonStrideIndex (cdetect k z j) (stepdetect k z j) t.val))
    let commonBudget := fun k => max (budget k) (3 * Pnative k + 3)
    let Qmodel := fun k => max (commonBudget k) (2 * u k + 4 * p k + max 0 (massLog k) + 20)
    let native := fun k => twistedNativeSampleFunctions (1 : Fin nX → ℕ) (degree k) (commonBudget k)
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, (fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)
        (Real.exp (commonBudget k)) (Real.exp (commonBudget k))
        ⟨Real.exp (commonBudget k), Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : Stage → (integerBox N → ℂ) → ℝ := fun k =>
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical (slices k) (tests k)
    let selectedLocal : Stage → (integerBox N → ℂ) →
        (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1) → ℂ) → Prop :=
      fun k err errLocal => ∀ center z, ∃ j, errLocal (center, z) =
        𝔼 t ∈ slices k z j, err (physical z t) * tests k z j t
    ∃ models : ∀ k, ExternalHistoryMaskIndex (Freq k) (Bin k) → CenteredForecastModel (integerBox N),
      (∀ k branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        (native k) (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
        (fun f => (data k f).target) (localSeminorm k) (selectedLocal k) (input k branch)
        (Real.exp (Qmodel k + 2)) (Real.exp (-u k))
        (Real.exp (2 * Qmodel k + 2 * u k + 4 * p k + 34)) (models k branch)) ∧
      PreparedCenteredStagedModelProductiveGoodConclusion (m := m) (nX := nX) (M := M)
        prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
        physical slices tests models Eres := by
  intro input
  have hinput (k) (branch) (x) : ‖input k branch x‖ ≤ Real.exp (p k) :=
    (externalHistoryMaskFamily_real_norm_le_exp (F k) (netCenters k) (hnet k) a ha
      branch x).trans (Real.exp_le_exp.mpr (hInputCap k))
  have hBranch (k) :
      (Fintype.card (ExternalHistoryMaskIndex (Freq k) (Bin k)) : ℝ) ≤
        Real.exp (historyLog k + frequencyLog k + binLog k) :=
    externalHistoryMaskIndex_card_le_exp (Freq k) (Bin k) (hHistory k) (hFrequency k) (hBin k)
  exact exists_preparedFiniteScheduleActualDegreeProductiveGood
    (prep := prep) (U := U) (b := b) (S := S) (bW := bW) (hb := hb) (o := o)
    (hR := hR) (hσ := hσ) (μ := μ) (poly := poly) (hm := hm) (stride := stride)
    (width := width) (bases := bases) (gainLog := gainLog) (gain := gain) (Q := Q)
    (e := e) (law := law) (N := N) (test := test) (hweight := hweight)
    (hgood := hgood) (hproductive := hproductive) (htest := htest) (hgain := hgain) (hmean := hmean)
    (Pdetect := Pdetect) (hbox := hbox) (physical := physical)
    (degree := degree) (u := u) (p := p) (cap := cap) (sliceLog := sliceLog)
    (testLog := testLog) (budget := budget) (E := E) (hModel := hModel)
    (Ddetect := Ddetect) (Vdetect := Vdetect) (slices := slices) (cdetect := cdetect)
    (stepdetect := stepdetect) (Hdetect := Hdetect) (hstep := hstep) (hSlices := hSlices)
    (hDense := hDense) (hnum := hnum) (hcomplex := hcomplex) (hcap := hcap)
    (Pnative := Pnative) (massLog := massLog) (capLog := capLog) (Edata := Edata)
    (data := data) (hNative := hNative) (hAccuracy := hAccuracy) (hCap := hCap)
    (hPrecision := hPrecision) (input := input) (hinput := hinput)
    (Bbranch := fun k => historyLog k + frequencyLog k + binLog k) (Eres := Eres)
    (stageLog := stageLog) (hBranch := hBranch) (hStageCount := hStageCount)
    (hErrorBudget := hErrorBudget)

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable section

attribute [local irreducible] preparedSamplerTransverse preparedCommonBlockCount RankPreparationLayer.rank
attribute [local irreducible] PreparedFiniteScheduleDegreeModelsAtLaw integerBox allocatedPrincipalSides

variable
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    (bW : ∀ j, Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))

local instance (j : Fin m) : DecidableEq (PreparedSamplerContinuous prep j) := Classical.decEq _
local instance (a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)) :
    DecidableEq (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)) a) :=
  Classical.decEq _

variable
    (Pdetect : Polynomial ℕ) (hbox : (integerBox N).Nonempty)
    (physical : (bases × rectangularWeightIndices 0 width 1) → integerBox (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value)
      (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)) → integerBox N)
variable
    {Stage : Type} [Fintype Stage]
    (degree : Stage → ℕ) (u p cap sliceLog testLog budget E : Stage → ℝ)
variable
    (hModel : ∀ k : Stage, PreparedFiniteScheduleDegreeModelsAtLaw
      (m := m) (nX := nX) (R := R) (σ := σ)
      (Path := bases × rectangularWeightIndices 0 width 1) (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N Pdetect μ poly hbox law hweight
      physical (degree k) (u k) (p k) (cap k) (sliceLog k) (testLog k) (budget k) (E k))
variable
    {L : Stage → Type} [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    {dims : Stage → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)]
    [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) (degree k) (dims k))
variable
    (hSliceLog : ∀ k, 0 ≤ sliceLog k)
    (hDetectorBudget : ∀ k, 1 ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    (hGeometry : ∀ k, (D k).GeometryComplexityLE
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k)))
    (hnum : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
variable
    {Forecast : Stage → Type} [∀ k, Nonempty (Forecast k)]
    (Pnative massLog capLog Edata : Stage → ℝ)
    (data : ∀ k, Forecast k → ActualForecastData N poly (Pnative k) (massLog k) (capLog k) (Edata k))
variable
    (hNative : ∀ k, 0 ≤ Pnative k)
    (hAccuracy : ∀ k, 2 * u k + 4 * p k + 12 ≤ Edata k)
    (hCap : ∀ k, Real.exp (capLog k) ≤ cap k)
    (hPrecision : ∀ k, actualForecastDataModelRequired (budget k) (Pnative k) (massLog k)
      (u k) (p k) ≤ E k)
variable
    {History : Stage → Type} [∀ k, Fintype (History k)]
    {Freq Bin Y : ∀ k, History k → Type}
    [∀ k h, Fintype (Freq k h)] [∀ k h, Fintype (Bin k h)]
    (F : ∀ k h, Freq k h → integerBox N → Y k h → ℂ)
    (netCenters : ∀ k h, Freq k h → Bin k h → Y k h → ℂ)
    {ε : ∀ k, History k → ℝ}
    (hnet : ∀ k h f x, ∃ i, ∀ y, ‖F k h f x y - netCenters k h f i y‖ ≤ ε k h)
variable
    (a : integerBox N → ℝ) (inputCap : ℝ)
    (ha : ∀ x, |a x| ≤ Real.exp inputCap)
    (hInputCap : ∀ k, inputCap ≤ p k)
variable
    (historyLog frequencyLog binLog Eres : Stage → ℝ) (stageLog : ℝ)
    (hHistory : ∀ k, (Fintype.card (History k) : ℝ) ≤ Real.exp (historyLog k))
    (hFrequency : ∀ k h, (Fintype.card (Freq k h) : ℝ) ≤ Real.exp (frequencyLog k))
    (hBin : ∀ k h, (Fintype.card (Bin k h) : ℝ) ≤ Real.exp (binLog k))
    (hStageCount : (Fintype.card Stage : ℝ) + 1 ≤ Real.exp stageLog)
    (hErrorBudget : ∀ k, historyLog k + frequencyLog k + binLog k + gainLog +
      Eres k + stageLog + 6 ≤ u k)

include hgood hproductive htest hgain hmean hModel hSliceLog hDetectorBudget hGeometry hnum
  hNative hAccuracy hCap hPrecision ha hInputCap hHistory hFrequency hBin
  hStageCount hErrorBudget in

theorem exists_preparedFiniteScheduleUniversalMaskProductiveGood :
    let input : ∀ k, ExternalHistoryMaskIndex (Freq k) (Bin k) → integerBox N → ℂ :=
      fun k => externalHistoryMaskFamily (F k) (netCenters k) (hnet k)
        (fun x => (a x : ℂ))
    let Packet := fun k => LocalMajorSliceTest (D k)
      (Sum.elim (fun _ : EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) => S.value)
        (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S))
      (sliceLog k) (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    let commonBudget := fun k => max (budget k) (3 * Pnative k + 3)
    let Qmodel := fun k => max (commonBudget k) (2 * u k + 4 * p k + max 0 (massLog k) + 20)
    let native := fun k => twistedNativeSampleFunctions (1 : Fin nX → ℕ) (degree k) (commonBudget k)
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, (fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)
        (Real.exp (commonBudget k)) (Real.exp (commonBudget k))
        ⟨Real.exp (commonBudget k), Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : Stage → (integerBox N → ℂ) → ℝ := fun k =>
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical
        (fun _ (j : Packet k) => j.slice.subtypeSites)
        (fun _ (j : Packet k) t => j.weight t.val)
    let selectedLocal : Stage → (integerBox N → ℂ) →
        (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1) → ℂ) → Prop :=
      fun k err errLocal => ∀ center z, ∃ j : Packet k, errLocal (center, z) =
        𝔼 t ∈ j.slice.subtypeSites, err (physical z t) * j.weight t.val
    ∃ models : ∀ k, ExternalHistoryMaskIndex (Freq k) (Bin k) → CenteredForecastModel (integerBox N),
      (∀ k branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        (native k) (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
        (fun f => (data k f).target) (localSeminorm k) (selectedLocal k) (input k branch)
        (Real.exp (Qmodel k + 2)) (Real.exp (-u k))
        (Real.exp (2 * Qmodel k + 2 * u k + 4 * p k + 34)) (models k branch)) ∧
      PreparedCenteredStagedModelProductiveGoodConclusion (m := m) (nX := nX) (M := M)
        prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
        physical (fun k _ (j : Packet k) => j.slice.subtypeSites)
        (fun k _ (j : Packet k) t => j.weight t.val) models Eres := by
  intro input Packet commonBudget Qmodel native localSeminorm selectedLocal
  let sides := Sum.elim
    (fun _ : EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) => S.value)
    (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)
  have hSides (i : LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) :
      0 < sides i := by
    cases i with
    | inl g => exact S.positive
    | inr j =>
      exact allocatedPrincipalSides_pos
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S j
  let : ∀ k, Nonempty (Packet k) := fun k => LocalMajorSliceTest.nonempty (D k) sides hSides
    (sliceLog k) (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    (hSliceLog k) (hDetectorBudget k) (hGeometry k)
  exact exists_preparedFiniteScheduleExternalMaskProductiveGood
    (prep := prep) (U := U) (b := b) (S := S) (bW := bW) (hb := hb) (o := o)
    (hR := hR) (hσ := hσ) (μ := μ) (poly := poly) (hm := hm) (stride := stride)
    (width := width) (bases := bases) (gainLog := gainLog) (gain := gain) (Q := Q)
    (e := e) (law := law) (N := N) (test := test) (hweight := hweight)
    (hgood := hgood) (hproductive := hproductive) (htest := htest) (hgain := hgain) (hmean := hmean)
    (Pdetect := Pdetect) (hbox := hbox) (physical := physical)
    (degree := degree) (u := u) (p := p) (cap := cap) (sliceLog := sliceLog)
    (testLog := testLog) (budget := budget) (E := E) (hModel := hModel)
    (Tests := fun k _ => Packet k) (Ldetect := fun k _ _ => L k) (dims := fun k _ _ => dims k)
    (Ddetect := fun k _ _ => D k) (Vdetect := fun k _ j => j.test)
    (slices := fun k _ j => j.slice.subtypeSites)
    (cdetect := fun k _ j i => (j.slice.start i : ℤ))
    (stepdetect := fun k _ j => j.stride) (Hdetect := fun k _ j => j.slice.length)
    (hstep := fun k _ j => j.stride_pos)
    (hSlices := fun k _ j => j.slice.subtypeSites_image_val.trans j.slice.integerPoints_eq_commonStrideBox)
    (hDense := fun k _ j => j.slice.subtypeSites_dense j.dense) (hnum := hnum)
    (hcomplex := fun k _ j => j.complexity) (hcap := fun k _ j => j.norm)
    (Pnative := Pnative) (massLog := massLog) (capLog := capLog) (Edata := Edata)
    (data := data) (hNative := hNative) (hAccuracy := hAccuracy) (hCap := hCap)
    (hPrecision := hPrecision) (F := F) (netCenters := netCenters) (hnet := hnet)
    (a := a) (inputCap := inputCap) (ha := ha) (hInputCap := hInputCap)
    (historyLog := historyLog) (frequencyLog := frequencyLog) (binLog := binLog)
    (hHistory := hHistory) (hFrequency := hFrequency) (hBin := hBin) (Eres := Eres)
    (stageLog := stageLog) (hStageCount := hStageCount) (hErrorBudget := hErrorBudget)

end

end Erdos3.VectorPolynomial

end

end OAI
