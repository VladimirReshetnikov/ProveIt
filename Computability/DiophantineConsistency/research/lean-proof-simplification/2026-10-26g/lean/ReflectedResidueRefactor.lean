import DiophantineConsistency.CurrentClause2011

/-! Direct reuse of the already stronger modulus-2048 theorem. -/
namespace DiophantineConsistency.RefactorReflectedResidue

open CurrentKernel2011

private def selectorUnit : Entry → ℕ
  | .inl _ => 2
  | .inr _ => 0

theorem reflected_mod_sixteen (e : Entry) :
    2 * weight e ≡ selectorUnit e [MOD 16] := by
  exact (CurrentClause2011.reflected_weight_mod e).of_dvd (by decide : 16 ∣ 2048)

#print axioms reflected_mod_sixteen

end DiophantineConsistency.RefactorReflectedResidue
