import DiophantineConsistency.SplitSourceExistence

open DiophantineConsistency.SplitSourceExistence
open DiophantineConsistency.SplitSourceWords
open scoped BigOperators

private def oneDigit (i : Fin 31) : ℕ := if i=0 then 1 else 0

/-- The zero tuple still has a positive proof-side cap, but no positive packed code. -/
example : cofinalCap (fun _ => 0)=2 := by simp [cofinalCap]
example (B : ℕ) (w : Fin 31 → ℕ) :
    DiophantineConsistency.LowMaskCoding.indexedCode B w (fun _ => 0)=0 := by
  simp [DiophantineConsistency.LowMaskCoding.indexedCode]

/-- A unit tuple has cap four and a positive exact code without any search. -/
example : cofinalCap oneDigit=4 := by simp [cofinalCap,oneDigit]
example : DiophantineConsistency.LowMaskCoding.indexedCode 8 Fin.val oneDigit=1 := by
  simp [DiophantineConsistency.LowMaskCoding.indexedCode,oneDigit]
example (B : ℕ) (hB : 0<B) (w : Fin 31 → ℕ) :
    0<DiophantineConsistency.LowMaskCoding.indexedCode B w oneDigit :=
  code_pos hB w oneDigit ⟨0,by decide⟩

/-- The all-zero natural tuple gives the smallest positive coordinates,
while its absorbed index remains zero. -/
example : naturalVars (fun _ => 0)=⟨1,1,1,1,1,0⟩ := rfl
example : (positiveVars (fun _ => 1)).j=0 := rfl
example (d : Parameters) (a : ℕ) :
    positiveValue d a (fun _ => 1)=naturalValue d a (fun _ => 0) := rfl

#print axioms cofinalCap
#print axioms sum_lt_cofinalCap
#print axioms code_lt_cofinalCap
#print axioms code_pos
#print axioms hasZero_iff_source
#print axioms exists_positive_zero_iff_hasZero
#print axioms exists_natural_zero_iff_hasZero
#print axioms exists_natural_zero_iff_source
#print axioms no_natural_zero_iff
