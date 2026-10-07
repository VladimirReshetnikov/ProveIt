import OAI.Combinatorics.Progressions.Estimates.FiniteFiberPMF
import OAI.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

noncomputable def containedSupportedProgressionLaw : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  (weights).fiberLaw tupleMap

omit L step c hL hsubset in
theorem principalSupportedResidue_cube_support (y : PrincipalIntegerTuples B h α H)
    (hy : (weights).weight y ≠ 0) (j : PrincipalTupleIndex B h) :
    IntegerScalarCube (H j) (fun i => (y j i : ℤ)) := by
  have hypos := lt_of_le_of_ne ((weights).nonneg y) hy.symm
  have hp := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ y).mp hypos
  have hj := FiniteProbabilityWeights.pi_weight_pos_component
    (fun j => integerScalarCubeWeights α (H j) (hH j)) y hp.2 j
  exact (mem_integerScalarCubeSet (H j) (y j)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y j)).mp hj).1

theorem containedSupportedProgressionLaw_axis_integer_law (hq : 0 < q) (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨a,b,v⟩) :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).toPMF.map
      (fun y (b : B a) (v : Fin (h a)) i => (y ⟨a,b,v⟩ i : ℤ)) =
      dependentProductPMF (fun b => (dependentProductPMF (fun v =>
        (principalSupportedAxisSources B h H hH q hq r a hsize b v).source.toPMF)).map
          (fun y v i => (if i = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (y v i : ℤ))) := by
  have hp := congrArg (fun p => p.map (fun y (b : B a) (v : Fin (h a)) i =>
      (if i = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (y b v i : ℤ)))
    (principalSupportedResidue_axis_marginal B h H hH q hq r a hsize hcell)
  rw [PMF.map_comp] at hp
  have hm := dependentProductPMF_map
    (fun b => dependentProductPMF (fun v =>
      (principalSupportedAxisSources B h H hH q hq r a hsize b v).source.toPMF))
    (fun b y v i => (if i = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (y v i : ℤ))
  refine Eq.trans ?_ (hp.trans hm)
  rw [containedSupportedProgressionLaw, FiniteProbabilityWeights.toPMF_fiberLaw, PMF.map_comp]
  apply FiniteProbabilityWeights.toPMF_map_congr_on_support
  intro y hy
  funext b v i
  exact containedProgressionCubeMap_value α (L ⟨a,b,v⟩) (H ⟨a,b,v⟩) (step ⟨a,b,v⟩)
    (c ⟨a,b,v⟩) (hL _) (hsubset _) (y ⟨a,b,v⟩)
    (principalSupportedResidue_cube_support B h H hH q r hcell y hy _) i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_jet_sum_law (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨a,b,v⟩)
    (coeff : B a → NormalizedScalarCubeSource Empty)
    (rows : Finset (Finset α)) (offset : B a → ℤ) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B h H hH q hq r a hsize
    let lower := fun (b : B a) (v : Fin (h a)) (i : Option α) => if i = none then c ⟨a,b,v⟩ else 0
    let strides := fun (b : B a) (v : Fin (h a)) (_ : Option α) => step ⟨a,b,v⟩
    (weightedModerateIntegerProductSource coeff sources).toPMF.map
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows offset shift) =
      (dependentProductPMF (fun b => (coeff b).source.toPMF.map (fun z => (z none : ℤ)))).bind
        (fun z => (law).toPMF.map (fun y => shift + ∑ b, fun t : rows =>
          (offset b + z b) * integerBooleanBlockJet (fun v i => (y ⟨a,b,v⟩ i : ℤ)) t)) := by
  intro sources lower strides
  refine (weightedAffineModerateProductSource_affine_law coeff sources lower strides rows offset shift).trans ?_
  have hp := congrArg (fun p : PMF (B a → Fin (h a) → Option α → ℤ) =>
    (dependentProductPMF (fun b => (coeff b).source.toPMF.map (fun z => (z none : ℤ)))).bind
      (fun z => p.map (fun y => shift + ∑ b, fun t : rows =>
        (offset b + z b) * integerBooleanBlockJet (y b) t)))
    (containedSupportedProgressionLaw_axis_integer_law B h L H step c hL hH hsubset q r hcell hq a hsize).symm
  simp only [PMF.map_comp, Function.comp_def] at hp
  convert hp using 1
  rfl

theorem containedSupportedProgressionLaw_unit_block_law (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨a,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B h H hH q hq r a hsize
    (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (sources b v).source))).toPMF.map
      (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet
        (fun v k => (if k = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (z b v k : ℤ)) t) =
      (law).toPMF.map (fun y => shift + ∑ b, fun t : rows =>
        integerBooleanBlockJet (fun v k => (y ⟨a,b,v⟩ k : ℤ)) t) := by
  intro sources
  have houter :
      (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (sources b v).source))).toPMF =
        dependentProductPMF (fun b => (FiniteProbabilityWeights.pi (fun v => (sources b v).source)).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi _
  have hinner (b : B a) : (FiniteProbabilityWeights.pi (fun v => (sources b v).source)).toPMF =
      dependentProductPMF (fun v => (sources b v).source.toPMF) := FiniteProbabilityWeights.toPMF_pi _
  rw [houter]
  simp_rw [hinner]
  have hm := dependentProductPMF_map
    (fun b => dependentProductPMF (fun v => (sources b v).source.toPMF))
    (fun b z v k => (if k = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (z v k : ℤ))
  have hp := congrArg (fun p : PMF (B a → Fin (h a) → Option α → ℤ) =>
    p.map (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet (z b) t))
    (containedSupportedProgressionLaw_axis_integer_law B h L H step c hL hH hsubset q r hcell hq a hsize)
  rw [← hm] at hp
  simp only [PMF.map_comp, Function.comp_def] at hp
  exact hp.symm

end Erdos3

end

end OAI
