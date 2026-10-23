import DiophantineConsistency.SplitCarry

open DiophantineConsistency.SplitCarry
open Jones1982 Polynomial

private def weights : Fin 1 → ℕ := fun _ => 1
private theorem weights_injective : Function.Injective weights := by intro i j _; exact Subsingleton.elim _ _

example : word 8 2 8 134=8584 := by decide
example : packedMask 8 2 2 weights {1}=3127 := by decide

/-- The high word has an actual negative lower-digit borrow; the low digit is bounded. -/
example : τ 2 (word 8 2 8 134) (packedMask 8 2 2 weights {1})=0 := by
  apply (tau_word_iff weights (by intro i; change 1<2; decide) (k:=1) (t:=3)
    (by decide) (by decide) (by decide) (by decide) (by decide) 134 {1}).mpr
  constructor <;> decide

/-- A low digit equal to b is rejected even when the high word passes its mask. -/
example : τ 2 (word 8 2 16 134) (packedMask 8 2 2 weights {1})≠0 := by
  intro hz
  have h := (tau_word_iff weights (by intro i; change 1<2; decide) (k:=1) (t:=3)
    (by decide) (by decide) (by decide) (by decide) (by decide) 134 {1}).mp hz
  have hn : τ 2 16 (DiophantineConsistency.LowMaskCoding.indexedMask 8 2 2 weights)≠0 := by decide
  exact hn h.1

private noncomputable def p : ℤ[X] := X^2-1

/-- The complete polynomial/low-digit interface preserves this negative-coefficient example. -/
example : τ 2 (word 8 2 8 (2*p.eval 8+(8:ℤ))) (packedMask 8 2 2 weights {1})=0 := by
  have hp : p.natDegree<3 := by
    have hd : p.natDegree≤2 := by
      calc p.natDegree≤max ((X^2:ℤ[X]).natDegree) (1:ℤ[X]).natDegree := natDegree_sub_le _ _
           _=2 := by simp
    omega
  have hb : ∀ i<3,|p.coeff i|<(8:ℤ)/4 := by
    intro i hi
    interval_cases i <;> norm_num [p,coeff_one]
  have hJ : 0≤2*p.eval (8:ℤ)+∑ i∈({1}:Finset ℕ),(8:ℤ)^i := by norm_num [p]
  have h := tau_polynomial_iff (B:=8) (b:=2) (lowLen:=2) (highLen:=3) (g:=8) weights weights_injective (by intro i; change 1<2; decide)
    (k:=1) (t:=3) (by decide) (by decide) (by decide) (by decide) (by decide)
    {1} (by intro i hi; simp only [Finset.mem_singleton] at hi; omega) p hp hb hJ
  have hz : ∃ z : Fin 1 → ℕ,(∀ i,z i<2) ∧
      8=DiophantineConsistency.LowMaskCoding.indexedCode 8 weights z ∧
        ∀ i∈({1}:Finset ℕ),p.coeff i=0 := by
    refine ⟨fun _ => 1,by intro i; change 1<2; decide,by decide,?_⟩
    simp [p,coeff_one]
  simpa using h.mpr hz

/-- The generic block definitions admit an empty low block. -/
example : word 8 0 0 134=134 := by decide
example : packedMask 8 1 0 (Fin.elim0 : Fin 0 → ℕ) {1}=48 := by decide

#print axioms packedMask_eq
#print axioms tau_word_iff
#print axioms tau_family_iff
#print axioms eval_encoded_add_one
#print axioms highInt_eq_eval_product
#print axioms tau_product_iff_31
#print axioms calibrated_family_iff
