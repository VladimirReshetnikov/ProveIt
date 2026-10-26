import Mathlib.Tactic

namespace DiophantineConsistency.Carrier66

variable {R : Type*} [CommRing R]

def drop (v : Fin 15 → R) (n : R) (j : Fin 14) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | 5 => v 6
  | 6 => v 7
  | 7 => v 8
  | 8 => v 9
  | 9 => n
  | 10 => v 11
  | 11 => v 12
  | 12 => v 13
  | _ => v 14

theorem drop_pos (v : Fin 15 → ℤ) (n : ℤ)
    (hv : ∀ j, 0 < v j) (hn : 0 < n) : ∀ j, 0 < drop v n j := by
  intro j
  fin_cases j <;> first
    | exact hn
    | exact hv _

#print axioms drop_pos

end DiophantineConsistency.Carrier66
