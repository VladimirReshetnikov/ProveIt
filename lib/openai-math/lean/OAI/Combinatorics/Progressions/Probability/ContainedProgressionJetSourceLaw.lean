import OAI.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity

namespace OAI

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
variable (hsize : ∀ j, (Fintype.card α + 1) * q ≤ H j)

local notation "weights" => principalResidueWeights B h H hH q hq r hsize
local notation "law" => containedProgressionResidueLaw B h L H step c hL hH hsubset q hq r hsize

omit L step c hL hsubset in
theorem principalResidueWeights_axis_marginal (a : D) :
    (weights).toPMF.map (fun y (b : B a) (v : Fin (h a)) => y ⟨a,b,v⟩) =
      dependentProductPMF (fun b => dependentProductPMF (fun v =>
        (principalSupportedAxisSources B h H hH q hq r a (fun b v => hsize ⟨a,b,v⟩) b v).source.toPMF)) := by
  have hp := dependentProductPMF_marginal
    (fun j => (scalarCubeResidueWeights α (H j) q (hH j) (fun _ => q) (r j)
      (fun _ => hq) (fun _ => le_rfl) (hsize j)).toPMF)
    (fun t : B a × Fin (h a) => (⟨a,t⟩ : PrincipalTupleIndex B h))
    (by intro x y hxy; simpa using hxy)
  have ht := congrArg (fun p => p.map (fun x b v => x (b,v))) hp
  rw [PMF.map_comp] at ht
  have hw := FiniteProbabilityWeights.toPMF_pi
    (fun j => scalarCubeResidueWeights α (H j) q (hH j) (fun _ => q) (r j)
      (fun _ => hq) (fun _ => le_rfl) (hsize j))
  refine (congrArg (fun p : PMF (PrincipalIntegerTuples B h α H) =>
    p.map (fun y (b : B a) (v : Fin (h a)) => y ⟨a,b,v⟩)) hw).trans (ht.trans ?_)
  refine (dependentProductPMF_curry (fun (b : B a) (v : Fin (h a)) =>
    (scalarCubeResidueWeights α (H ⟨a,b,v⟩) q (hH _) (fun _ => q) (r ⟨a,b,v⟩)
      (fun _ => hq) (fun _ => le_rfl) (hsize _)).toPMF)).trans ?_
  apply congrArg (fun p : ∀ b : B a, PMF (∀ v : Fin (h a), IntegerScalarCubeBox α (H ⟨a,b,v⟩)) =>
    dependentProductPMF p)
  funext b
  apply congrArg (fun p : ∀ v : Fin (h a), PMF (IntegerScalarCubeBox α (H ⟨a,b,v⟩)) =>
    dependentProductPMF p)
  funext v
  exact (normalizedUniformCubeSource_toPMF α (H ⟨a,b,v⟩) q (hH _) (fun _ => q)
    (r ⟨a,b,v⟩) (fun _ => hq) (fun _ => le_rfl) (hsize _)).symm

theorem containedProgressionResidueLaw_axis_integer_law (a : D) :
    (law).toPMF.map (fun y (b : B a) (v : Fin (h a)) i => (y ⟨a,b,v⟩ i : ℤ)) =
      dependentProductPMF (fun b => (dependentProductPMF (fun v =>
        (principalSupportedAxisSources B h H hH q hq r a (fun b v => hsize ⟨a,b,v⟩) b v).source.toPMF)).map
          (fun y v i => (if i = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (y v i : ℤ))) := by
  have hp := congrArg (fun p => p.map (fun y (b : B a) (v : Fin (h a)) i =>
      (if i = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (y b v i : ℤ)))
    (principalResidueWeights_axis_marginal B h H hH q hq r hsize a)
  rw [PMF.map_comp] at hp
  have hm := dependentProductPMF_map
    (fun b => dependentProductPMF (fun v =>
      (principalSupportedAxisSources B h H hH q hq r a (fun b v => hsize ⟨a,b,v⟩) b v).source.toPMF))
    (fun b y v i => (if i = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (y v i : ℤ))
  refine Eq.trans ?_ (hp.trans hm)
  rw [containedProgressionResidueLaw, FiniteProbabilityWeights.toPMF_fiberLaw, PMF.map_comp]
  apply FiniteProbabilityWeights.toPMF_map_congr_on_support
  intro y hy
  funext b v i
  exact containedProgressionCubeMap_value α (L ⟨a,b,v⟩) (H ⟨a,b,v⟩) (step ⟨a,b,v⟩)
    (c ⟨a,b,v⟩) (hL _) (hsubset _) (y ⟨a,b,v⟩)
    (principalResidueWeights_cube_support B h H hH q hq r hsize y hy _) i

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
variable (hsize : ∀ j, (Fintype.card α + 1) * q ≤ H j)

local notation "weights" => principalResidueWeights B h H hH q hq r hsize
local notation "law" => containedProgressionResidueLaw B h L H step c hL hH hsubset q hq r hsize

theorem containedProgressionResidueLaw_jet_sum_law (a : D)
    (coeff : B a → NormalizedScalarCubeSource Empty)
    (rows : Finset (Finset α)) (offset : B a → ℤ) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B h H hH q hq r a (fun b v => hsize ⟨a,b,v⟩)
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
    (containedProgressionResidueLaw_axis_integer_law B h L H step c hL hH hsubset q hq r hsize a).symm
  simp only [PMF.map_comp, Function.comp_def] at hp
  convert hp using 1
  rfl

end Erdos3

end

end OAI
