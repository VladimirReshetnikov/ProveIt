import GowersSzemeredi.Proofs16ColumnListIdentity

/-! The selected model lists share a Bohr domain of bounded rank. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def columnModelSpectrum {I : Type*} {N : Nat} (T : ZMod N → Finset (ZMod N))
    (anchors : I → List (ZMod N)) (J : Finset I) : Finset (ZMod N) :=
  J.biUnion (fun j => columnListSpectrum T (anchors j))

theorem columnModelSpectrum_card_le {I : Type*} {N m d : Nat}
    (T : ZMod N → Finset (ZMod N)) (anchors : I → List (ZMod N)) (J : Finset I)
    (hlen : ∀ j ∈ J, (anchors j).length ≤ m)
    (hT : ∀ j ∈ J, ∀ x ∈ anchors j, (T x).card ≤ d) :
    (columnModelSpectrum T anchors J).card ≤ J.card*m*d := by
  apply Finset.card_biUnion_le.trans
  calc (∑ j ∈ J, (columnListSpectrum T (anchors j)).card) ≤ ∑ _j ∈ J, m*d :=
      Finset.sum_le_sum fun j hj => (columnListSpectrum_card_le T (anchors j) (hT j hj)).trans
        (Nat.mul_le_mul_right d (hlen j hj))
    _ = J.card*m*d := by simp [Nat.mul_assoc]

theorem mem_columnModelSpectrum_bohr {I : Type*} {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (anchors : I → List (ZMod N)) (J : Finset I)
    (r : Real) (y : ZMod N) :
    y ∈ bohr (columnModelSpectrum T anchors J) r ↔
      ∀ j ∈ J, ∀ x ∈ anchors j, y ∈ bohr (T x) r := by
  constructor
  · intro hy j hj
    apply (mem_columnListSpectrum_bohr T (anchors j) r y).mp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro t ht
    exact (Finset.mem_filter.mp hy).2 t (Finset.mem_biUnion.mpr ⟨j,hj,ht⟩)
  · intro hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro t ht
    obtain ⟨j,hj,ht⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_filter.mp ((mem_columnListSpectrum_bohr T (anchors j) r y).mpr (hy j hj))).2 t ht

theorem column_models_freiman {I : Type*} {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (anchors : I → List (ZMod N)) (J : Finset I) (rho : Real)
    (hL : ∀ j ∈ J, ∀ x ∈ anchors j, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hz : ∀ j ∈ J, ∀ x ∈ anchors j, L x 0 = 0) :
    ∀ j ∈ J, IsFreimanLinearOn (bohr (columnModelSpectrum T anchors J) rho)
      (fun y => columnAnchorEval (fun x => L x y) (anchors j)) ∧
      columnAnchorEval (fun x => L x 0) (anchors j) = 0 := by
  intro j hj
  refine ⟨columnAnchorEval_freiman _ L (anchors j) ?_,columnAnchorEval_zero _ _ (hz j hj)⟩
  intro x hx a b c d ha hb hc hd he
  exact hL j hj x hx a b c d
    ((mem_columnModelSpectrum_bohr T anchors J rho a).mp ha j hj x hx)
    ((mem_columnModelSpectrum_bohr T anchors J rho b).mp hb j hj x hx)
    ((mem_columnModelSpectrum_bohr T anchors J rho c).mp hc j hj x hx)
    ((mem_columnModelSpectrum_bohr T anchors J rho d).mp hd j hj x hx) he

end LeanProofs.GowersSzemeredi
