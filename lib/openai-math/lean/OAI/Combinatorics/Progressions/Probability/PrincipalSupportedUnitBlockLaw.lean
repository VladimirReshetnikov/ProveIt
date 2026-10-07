import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem principalSupportedResidue_unit_block_law
    {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
    (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
    (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)
    (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let s := principalSupportedAxisSources B h L hL q hq r a hsize
    (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (s b v).source))).toPMF.map
      (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet (fun v k => (z b v k : ℤ)) t) =
      ((principalTupleWeights (α := α) B h L hL).condition
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
          (fun y => shift + ∑ b, fun t : rows => integerBooleanBlockJet
            (fun v k => (y ⟨a, b, v⟩ k : ℤ)) t) := by
  dsimp only
  let s := principalSupportedAxisSources B h L hL q hq r a hsize
  have houter :
      (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (s b v).source))).toPMF =
        dependentProductPMF (fun b => (FiniteProbabilityWeights.pi (fun v => (s b v).source)).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi _
  have hinner (b : B a) : (FiniteProbabilityWeights.pi (fun v => (s b v).source)).toPMF =
      dependentProductPMF (fun v => (s b v).source.toPMF) := FiniteProbabilityWeights.toPMF_pi _
  rw [houter]
  simp_rw [hinner]
  have hp := principalSupportedResidue_axis_marginal B h L hL q hq r a hsize hcell
  have hmap := congrArg (fun p => p.map (fun y => shift + ∑ b, fun t : rows =>
    integerBooleanBlockJet (fun v k => (y b v k : ℤ)) t)) hp
  simp only [PMF.map_comp, Function.comp_def] at hmap
  convert hmap.symm using 1
  congr 1

end Erdos3

end

end OAI
