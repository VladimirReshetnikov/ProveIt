import GowersSzemeredi.Proofs16GlobalColumnRichness

/-! Exact quadruple counts partition over their first column. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def exactColumnAnchor {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (a : ZMod N) : Finset (Fin 4 → ZMod N) :=
  (exactColumnQuadruples B T L r).filter (fun q => q 0 = a)

theorem exactColumnQuadruples_mono {N : Nat} [NeZero N]
    {C B : Finset (ZMod N)} (hCB : C ⊆ B)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real) :
    exactColumnQuadruples C T L r ⊆ exactColumnQuadruples B T L r := by
  intro q hq
  obtain ⟨_, hC, hadd, hval⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hCB (hC i), hadd, hval⟩

theorem mixedExactColumnQuadruples_self {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) :
    mixedExactColumnQuadruples C C T L r = exactColumnQuadruples C T L r := by
  ext q
  simp only [mixedExactColumnQuadruples, Finset.union_self, Finset.mem_filter]
  constructor
  · exact And.left
  · intro h
    have hc := (Finset.mem_filter.mp h).2.1
    exact ⟨h, hc 0, hc 2, hc 1, hc 3⟩

/-- A subset's exact quadruples are bounded by ambient anchor degrees
summed only over that subset. -/
theorem exact_quadruples_le_anchor_sum {N : Nat} [NeZero N]
    {C B : Finset (ZMod N)} (hCB : C ⊆ B)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real) :
    (exactColumnQuadruples C T L r).card ≤ ∑ a ∈ C, (exactColumnAnchor B T L r a).card := by
  have heq := Finset.card_eq_sum_card_fiberwise (s := exactColumnQuadruples C T L r)
    (t := C) (f := fun q => q 0) (fun q hq => (Finset.mem_filter.mp hq).2.1 0)
  rw [heq]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqC, hqa⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨exactColumnQuadruples_mono hCB T L r hqC, hqa⟩

/-- The density-form richness statement also has a denominator-free
cardinality form. -/
theorem exact_quadruples_richness_card {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r eta : Real)
    (hrich : ∀ C ⊆ B, ∀ beta : Real, 0 ≤ beta → beta*N ≤ (C.card : Real) →
      (beta*beta*eta)^2*(N : Real)^3 ≤ ((mixedExactColumnQuadruples C C T L r).card : Real)) :
    ∀ C ⊆ B, eta^2*(C.card : Real)^4 ≤ N*((exactColumnQuadruples C T L r).card : Real) := by
  intro C hCB
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have h := hrich C hCB ((C.card : Real)/N) (by positivity) (by rw [div_mul_cancel₀ _ hn.ne'])
  rw [mixedExactColumnQuadruples_self] at h
  calc eta^2*(C.card : Real)^4 =
      N*((((C.card : Real)/N)*((C.card : Real)/N)*eta)^2*(N : Real)^3) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hn.le

end LeanProofs.GowersSzemeredi
