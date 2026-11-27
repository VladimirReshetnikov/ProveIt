import GRHArticle.ProgressionFree.IntegerBoundaryExchangeVertices
import GRHArticle.ProgressionFree.IntegerBoundaryExchangePacking

/-!
# Checking the triples used in the exchange certificate
-/

namespace GRHArticle.ProgressionFree

/-- The supplied triple lies in the smooth search domain and has an exact
rational ratio. -/
def integerExchangeEdgeValid (e : IntegerPrefixTriple) : Bool :=
  decide (e.first < e.middle ∧ e.middle < e.last ∧ e.first*e.last = e.middle*e.middle) &&
    e.vertices.all (fun n ↦ decide (n ∣ integerExchangeBaseScale ∧ n ≤ 1000000))

private theorem exchangeBaseScale_smooth : integerExchangeBaseScale ∈ Nat.smoothNumbers 6 := by
  decide +kernel

theorem integerExchangeEdgeValid_sound {e : IntegerPrefixTriple}
    (h : integerExchangeEdgeValid e = true) :
    e.first < e.middle ∧ e.middle < e.last ∧ e.first*e.last = e.middle*e.middle ∧
      ∀ n ∈ e.vertices, n ∈ integerExchangeVertices := by
  simp only [integerExchangeEdgeValid, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, h.1.2.1, h.1.2.2, ?_⟩
  intro n hn
  obtain ⟨hd,hN⟩ := of_decide_eq_true (List.all_eq_true.mp h.2 n hn)
  exact mem_integerExchangeVertices.mpr
    ⟨Nat.mem_smoothNumbers_of_dvd exchangeBaseScale_smooth hd, hN⟩

end GRHArticle.ProgressionFree
