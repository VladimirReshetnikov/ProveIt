import CurrentMCBytes

/-! Parametric assembly of four big-endian byte lists, with no closed recipes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FourByteGeneric

def bytes (a b c d : List ℕ) : Fin 4 → List ℕ := ![a,b,c,d]
def decoded (a b c d : List ℕ) : Fin 4 → ℤ := fun j =>
  ((Nat.ofDigits 256 ((bytes a b c d j).reverse) : ℕ) : ℤ)

theorem assemble (a b c d : List ℕ) (p : Fin 4 → ℤ)
    (h0 : ((Nat.ofDigits 256 a.reverse : ℕ) : ℤ)=p 0)
    (h1 : ((Nat.ofDigits 256 b.reverse : ℕ) : ℤ)=p 1)
    (h2 : ((Nat.ofDigits 256 c.reverse : ℕ) : ℤ)=p 2)
    (h3 : ((Nat.ofDigits 256 d.reverse : ℕ) : ℤ)=p 3) :
    decoded a b c d = p := by
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

#print axioms assemble
end DiophantineConsistency.FourByteGeneric
