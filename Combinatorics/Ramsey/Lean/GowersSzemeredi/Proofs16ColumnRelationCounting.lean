import GowersSzemeredi.Proofs16ColumnRelationSystem
import GowersSzemeredi.Proofs16ManyExactColumnQuadruples

/-! Exact column quadruples and relations between pairs are the same
finite collection under a coordinate permutation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem columnPairRelated_iff_exact {N : Nat} [NeZero N]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (p q : ZMod N × ZMod N) :
    ColumnPairRelated X T L r p q ↔ columnPairTuple p q ∈ exactColumnQuadruples X T L r := by
  constructor
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · exact h.1.1
      · exact h.2.1.2
      · exact h.1.2
      · exact h.2.1.1
    · change p.1 + q.2 = p.2 + q.1
      linear_combination h.2.2.1
    · intro y hy
      have heq := h.2.2.2 y (hy 0) (hy 2) (hy 3) (hy 1)
      change L p.1 y + L q.2 y = L p.2 y + L q.1 y
      linear_combination heq
  · intro h
    obtain ⟨_, hX, hadd, hvalues⟩ := Finset.mem_filter.mp h
    refine ⟨⟨hX 0, hX 2⟩, ⟨hX 3, hX 1⟩, ?_, ?_⟩
    · change p.1 + q.2 = p.2 + q.1 at hadd
      linear_combination hadd
    · intro y hp1 hp2 hq1 hq2
      have hy : ∀ i, y ∈ bohr (T (columnPairTuple p q i)) r := by
        intro i; fin_cases i
        · exact hp1
        · exact hq2
        · exact hp2
        · exact hq1
      have heq := hvalues y hy
      change L p.1 y + L q.2 y = L p.2 y + L q.1 y at heq
      linear_combination heq

def columnRelationPairs {N : Nat} [NeZero N] (X : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) : Finset ((ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
  Finset.univ.filter fun p => ColumnPairRelated X T L r p.1 p.2

/-- Reindexing as pairs preserves the exact quadruple count. -/
theorem columnRelationPairs_card_eq {N : Nat} [NeZero N]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) :
    (columnRelationPairs X T L r).card = (exactColumnQuadruples X T L r).card := by
  apply Finset.card_bij (fun p _ => columnPairTuple p.1 p.2)
  · intro p hp
    exact (columnPairRelated_iff_exact X T L r p.1 p.2).mp (Finset.mem_filter.mp hp).2
  · intro p hp q hq h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    exact Prod.ext (Prod.ext h0 h2) (Prod.ext h3 h1)
  · intro q hq
    let p : (ZMod N × ZMod N) × (ZMod N × ZMod N) := ((q 0, q 2), (q 3, q 1))
    have heq : columnPairTuple p.1 p.2 = q := by
      funext i; fin_cases i <;> rfl
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    exact (columnPairRelated_iff_exact X T L r p.1 p.2).mpr (heq.symm ▸ hq)

end LeanProofs.GowersSzemeredi
