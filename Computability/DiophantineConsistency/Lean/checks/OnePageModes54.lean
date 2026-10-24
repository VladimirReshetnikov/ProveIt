import DiophantineConsistency.OnePageModes54

open DiophantineConsistency
open OnePageModes54

namespace OnePageModes54Checks

set_option maxRecDepth 10000

example (i : Fin 457) : arithmeticRank i < 457 := arithmeticRank_lt i

example (i : Fin 457) :
    NativeModesData54.mode ⟨arithmeticRank i, arithmeticRank_lt i⟩ = unsortedMode i :=
  mode_at_arithmeticRank i

example {a b : ℕ} (ha : a < Q) (hb : b < Q) :
    (((Q+a-b-1)/Q : ℕ) : ℤ) = ((Q : ℤ)+a-b-1)/(Q : ℤ) :=
  quotient_cast ha hb

#print axioms tailMode_eq
#print axioms sorted_strict
#print axioms sorted_key_lt
#print axioms quotient_cast
#print axioms arithmeticRank_eq
#print axioms arithmeticRank_lt
#print axioms unsortedMode_eq
#print axioms mode_at_arithmeticRank

end OnePageModes54Checks
