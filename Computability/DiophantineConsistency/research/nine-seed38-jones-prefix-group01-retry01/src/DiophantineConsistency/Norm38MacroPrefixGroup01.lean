import DiophantineConsistency.Norm38MacroPrefixFirst

/-! Candidate local prefix nodes B, q, N; no full-recipe equality. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup01
open Norm38MacroLanguage Norm38MacroPrefixes ExecutableJones

def base {R : Type*} [CommRing R] (a : Fin 9 → R) : R :=
  ((indexY Norm38MacroLanguage.seed 0 : Nat) : R) + ((1 : Int) : R) + a ⟨0, by decide⟩

theorem prefix_B {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d2.values a (Fin.last 1) = base a ^ (5 : Nat) := by
  rw [d2, Norm38MacroCuts.snoc_last]
  change (d1.values a ⟨0, by decide⟩) ^ (5 : Nat) = _
  have hb : d1.values a ⟨0, by decide⟩ = base a :=
    Norm38MacroPrefixFirst.first_prefix_value a
  rw [hb]

theorem prefix_q {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d3.values a (Fin.last 2) = (base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat) := by
  rw [d3, Norm38MacroCuts.snoc_last]
  change (d2.values a (Fin.last 1)) ^ (5 ^ 39 : Nat) = _
  rw [prefix_B]

theorem prefix_N {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d4.values a (Fin.last 3) = ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat) := by
  rw [d4, Norm38MacroCuts.snoc_last]
  change (d3.values a (Fin.last 2)) ^ (16 : Nat) = _
  rw [prefix_q]

#print axioms prefix_B
#print axioms prefix_q
#print axioms prefix_N
end DiophantineConsistency.Norm38MacroPrefixGroup01
