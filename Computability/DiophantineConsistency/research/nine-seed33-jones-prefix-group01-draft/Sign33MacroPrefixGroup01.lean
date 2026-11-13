import DiophantineConsistency.Sign33MacroPrefixFirst

/-! Candidate local prefix nodes B, q, N; no full-recipe equality. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup01
open Sign33MacroLanguage Sign33MacroPrefixes ExecutableJones

def base {R : Type*} [CommRing R] (a : Fin 9 → R) : R :=
  ((indexY Sign33MacroLanguage.seed 0 : Nat) : R) + ((1 : Int) : R) + a ⟨0, by decide⟩

theorem prefix_B {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d2.values a (Fin.last 1) = base a ^ (5 : Nat) := by
  rw [d2, Sign33MacroCuts.snoc_last]
  change (d1.values a ⟨0, by decide⟩) ^ (5 : Nat) = _
  have hb : d1.values a ⟨0, by decide⟩ = base a :=
    Sign33MacroPrefixFirst.first_prefix_value a
  rw [hb]

theorem prefix_q {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d3.values a (Fin.last 2) = (base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat) := by
  rw [d3, Sign33MacroCuts.snoc_last]
  change (d2.values a (Fin.last 1)) ^ (5 ^ 34 : Nat) = _
  rw [prefix_B]

theorem prefix_N {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d4.values a (Fin.last 3) = ((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat) := by
  rw [d4, Sign33MacroCuts.snoc_last]
  change (d3.values a (Fin.last 2)) ^ (16 : Nat) = _
  rw [prefix_q]

#print axioms prefix_B
#print axioms prefix_q
#print axioms prefix_N
end DiophantineConsistency.Sign33MacroPrefixGroup01
