import Mathlib.Data.Nat.Digits.Lemmas

/-! Finite tuple mapping, proved while the four byte lists stay abstract. -/
set_option autoImplicit false
set_option Elab.async false
namespace GenericFourBytePorts

theorem map4 (a b c d : List ℕ) :
    (fun j : Fin 4 => Nat.ofDigits 256 (![a,b,c,d] j)) =
      ![Nat.ofDigits 256 a, Nat.ofDigits 256 b,
        Nat.ofDigits 256 c, Nat.ofDigits 256 d] := by
  funext j
  fin_cases j <;> rfl

theorem tuple4 (a b c d : List ℕ) (A B C D : ℕ)
    (ha : Nat.ofDigits 256 a = A) (hb : Nat.ofDigits 256 b = B)
    (hc : Nat.ofDigits 256 c = C) (hd : Nat.ofDigits 256 d = D) :
    (fun j : Fin 4 => Nat.ofDigits 256 (![a,b,c,d] j)) = ![A,B,C,D] := by
  rw [map4, ha, hb, hc, hd]

#print axioms GenericFourBytePorts.map4
#print axioms GenericFourBytePorts.tuple4
end GenericFourBytePorts
