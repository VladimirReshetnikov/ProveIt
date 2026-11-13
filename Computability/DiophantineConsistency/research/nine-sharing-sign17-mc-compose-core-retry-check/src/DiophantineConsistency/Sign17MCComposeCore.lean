import DiophantineConsistency.Sign17MCRadixRuns
import DiophantineConsistency.Sign17MCChunks

/-! SOURCE-ONLY: compose equal-value aligned radix/byte blocks. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MCComposeCore
open CurrentMasks2011

def aligned (digits bytes : List ℕ) : Prop :=
  digits.length = 8 ∧ bytes.length = 47 ∧
    Nat.ofDigits radix digits = Nat.ofDigits 256 bytes

theorem radix_alignment : radix ^ 8 = (256 : ℕ) ^ 47 := by
  unfold radix
  decide +kernel

theorem aligned_repeat (a b : List ℕ) (h : aligned a b) (n : ℕ) :
    List.Forall₂ aligned (List.replicate n a) (List.replicate n b) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons h ih

theorem aligned_append {as bs cs ds : List (List ℕ)}
    (h₁ : List.Forall₂ aligned as bs) (h₂ : List.Forall₂ aligned cs ds) :
    List.Forall₂ aligned (as ++ cs) (bs ++ ds) := by
  induction h₁ with
  | nil => exact h₂
  | cons h ht ih => exact .cons h ih

theorem flatten_tail {as bs : List (List ℕ)} (h : List.Forall₂ aligned as bs)
    (xs ys : List ℕ) (ht : Nat.ofDigits radix xs = Nat.ofDigits 256 ys) :
    Nat.ofDigits radix (as.flatten ++ xs) = Nat.ofDigits 256 (bs.flatten ++ ys) := by
  induction h with
  | nil => simpa using ht
  | cons hhead hrest ih =>
    rcases hhead with ⟨ha, hb, hv⟩
    simp only [Nat.ofDigits_append] at ih
    simp only [List.flatten_cons, List.append_assoc, Nat.ofDigits_append]
    rw [ha, hb, hv, radix_alignment, ih]

end DiophantineConsistency.Sign17MCComposeCore
#print axioms DiophantineConsistency.Sign17MCComposeCore.radix_alignment
#print axioms DiophantineConsistency.Sign17MCComposeCore.aligned_repeat
#print axioms DiophantineConsistency.Sign17MCComposeCore.aligned_append
#print axioms DiophantineConsistency.Sign17MCComposeCore.flatten_tail
