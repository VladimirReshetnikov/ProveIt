import DiophantineConsistency.QuadraticBoolean

namespace DiophantineConsistency.QuadraticBoolean
open NaturalRegisterProgram QuadraticRegisterSystem

def zeroRepresentation_short : Rep (Fin 2) (fun v => v 0 = if v 1 = 0 then 1 else 0) :=
  (System.scopedRep (a := 2) (k := 1) zeroSystem).ofIff (by
    intro v
    simp only [zero_holds_iff]
    change (∃ w : Fin 1 → ℕ, ZeroCertificate (v 0) (v 1) (w 0)) ↔ _
    simpa [Fin.exists_fin_succ_pi] using exists_zero_certificate_iff (v 0) (v 1))

def conditionalRepresentation_short : Rep (Fin 4)
    (fun v => v 0 = if v 1 = 0 then v 2 else v 3) :=
  (System.scopedRep (a := 4) (k := 2) conditionalSystem).ofIff (by
    intro v
    simp only [conditional_holds_iff]
    change (∃ w : Fin 2 → ℕ, ZeroCertificate (w 0) (v 1) (w 1) ∧
      (v 0 : ℤ) - ((w 0 : ℤ) * (v 2 : ℤ) + (1 - (w 0 : ℤ)) * (v 3 : ℤ)) = 0) ↔ _
    by_cases hn : v 1 = 0 <;>
      simp [Fin.exists_fin_succ_pi, exists_and_right, exists_zero_certificate_iff,
        hn, sub_eq_zero])

theorem zeroRepresentation_short_eq : zeroRepresentation_short = zeroRepresentation := rfl
theorem conditionalRepresentation_short_eq : conditionalRepresentation_short = conditionalRepresentation := rfl

#print axioms conditionalRepresentation_short
#print axioms zeroRepresentation_short

end DiophantineConsistency.QuadraticBoolean
