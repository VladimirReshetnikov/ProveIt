import DiophantineConsistency.Sign17KSentinelCollision

/-! SOURCE ONLY. Generic stream layout for the three K sentinel positions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KRadixStream
open scoped BigOperators

def prefix : List ℕ := List.replicate 18 0 ++ [1, 0]
def suffix : List ℕ := List.replicate 1014 0 ++ [1]
def block (v : Fin 986 → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin 986 => v i.rev + if i = ⟨984, by decide⟩ then 1 else 0)
def digits (v : Fin 986 → ℕ) : List ℕ := prefix ++ (block v ++ suffix)

theorem prefix_facts (r : ℕ) : prefix.length = 20 ∧ Nat.ofDigits r prefix = r ^ 18 := by
  simp [prefix, Nat.ofDigits_append, Nat.ofDigits_cons]

theorem suffix_facts (r : ℕ) : suffix.length = 1015 ∧ Nat.ofDigits r suffix = r ^ 1014 := by
  simp [suffix, Nat.ofDigits_append]

theorem block_length (v : Fin 986 → ℕ) : (block v).length = 986 := by
  simp [block]

theorem digit_value (r : ℕ) (v : Fin 986 → ℕ) :
    Nat.ofDigits r (digits v) = r ^ 18 + r ^ 1004 + r ^ 2020 +
      ∑ i : Fin 986, v i * r ^ (1005 - i.val) := by
  have hp := prefix_facts r
  have hs := suffix_facts r
  have hb := block_length v
  simp only [digits, Nat.ofDigits_append, hp.1, hp.2, hs.2, hb]
  rw [Nat.mul_add]
  change r ^ 18 + (r ^ 20 * Nat.ofDigits r (block v) +
    r ^ 20 * (r ^ 986 * r ^ 1014)) = _
  rw [show r ^ 20 * Nat.ofDigits r (block v) =
    (∑ i : Fin 986, v i * r ^ (1005 - i.val)) + r ^ 1004 by
      exact Sign17KSentinelCollision.middle_sentinel r v]
  have hpow : r ^ 20 * (r ^ 986 * r ^ 1014) = r ^ 2020 := by
    rw [← pow_add, ← pow_add]
  rw [hpow]
  omega

end DiophantineConsistency.Sign17KRadixStream
#print axioms DiophantineConsistency.Sign17KRadixStream.digit_value
