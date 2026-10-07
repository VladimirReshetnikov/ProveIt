import OAI.Combinatorics.Progressions.Probability.ContainedSupportedProgressionJetLaw

namespace OAI

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem principalSupportedResidue_selected_kernels {A : Type*} [Fintype A]
    (e : A → D) (he : Function.Injective e) {Y : A → Type*}
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (k : ∀ a, (∀ b : B (e a), ∀ v : Fin (h (e a)), IntegerScalarCubeBox α (L ⟨e a, b, v⟩)) →
      PMF (Y a)) :
    (conditioned).toPMF.bind (fun y => dependentProductPMF
      (fun a => k a (fun b v => y ⟨e a, b, v⟩))) =
      dependentProductPMF (fun a => (conditioned).toPMF.bind
        (fun y => k a (fun b v => y ⟨e a, b, v⟩))) := by
  exact pmf_bind_of_finite_independent_coordinates (conditioned).toPMF
    (fun y a b v => y ⟨e a, b, v⟩)
    (fun a => principalSupportedAxisTuplePMF B h L hL q r hcell (e a))
    (principalSupportedResidue_selected_axis_law B h L hL q r hcell e he) k

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

theorem containedSupportedProgressionLaw_selected_kernels {A : Type*} [Fintype A]
    (e : A → D) (he : Function.Injective e) {Y : A → Type*}
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (k : ∀ a, (∀ b : B (e a), ∀ v : Fin (h (e a)), IntegerScalarCubeBox α (L ⟨e a,b,v⟩)) → PMF (Y a)) :
    (law).toPMF.bind (fun y => dependentProductPMF (fun a => k a (fun b v => y ⟨e a,b,v⟩))) =
      dependentProductPMF (fun a => (law).toPMF.bind (fun y => k a (fun b v => y ⟨e a,b,v⟩))) := by
  simp only [containedSupportedProgressionLaw, FiniteProbabilityWeights.toPMF_fiberLaw, PMF.bind_map]
  exact principalSupportedResidue_selected_kernels B h H hH q r hcell e he
    (fun a y => k a (fun b v => containedProgressionCubeMap α (L ⟨e a,b,v⟩) (H ⟨e a,b,v⟩)
      (step ⟨e a,b,v⟩) (c ⟨e a,b,v⟩) (hL _) (hsubset _) (y b v)))

end Erdos3

end

end OAI
