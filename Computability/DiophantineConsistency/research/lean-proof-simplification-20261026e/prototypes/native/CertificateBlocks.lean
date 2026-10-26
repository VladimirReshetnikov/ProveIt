import Mathlib.Tactic

/-!
ADD-ONLY PROPOSAL; not compiled in the review environment.
The generator/partition is untrusted. Existing per-block decide +kernel
proofs remain the actual evidence; coverage is proved once below.
-/
namespace SimplificationProposals.CertificateBlocks

def HoldsBlock (P : ℕ → Prop) (base length : ℕ) : Prop :=
  ∀ j, j < length → P (base + j)

theorem HoldsBlock.of_fin {P : ℕ → Prop} {base length : ℕ}
    (h : ∀ j : Fin length, P (base + j.val)) : HoldsBlock P base length :=
  fun j hj => h ⟨j, hj⟩

theorem HoldsBlock.to_fin {P : ℕ → Prop} {base length : ℕ}
    (h : HoldsBlock P base length) : ∀ j : Fin length, P (base + j.val) :=
  fun j => h j.val j.isLt

/-- Adjacent blocks, including a shorter final block, cover exactly the union. -/
theorem HoldsBlock.append {P : ℕ → Prop} {base n m : ℕ}
    (left : HoldsBlock P base n) (right : HoldsBlock P (base + n) m) :
    HoldsBlock P base (n + m) := by
  intro j hj
  by_cases h : j < n
  · exact left j h
  · have hr := right (j - n) (by omega)
    have he : base + n + (j - n) = base + j := by omega
    simpa only [he] using hr

/-- The last action block really has length14, not16. This wrapper can combine
26 authenticated full blocks with the final existing action_chunk_416. -/
example (P : ℕ → Prop)
    (first : ∀ j : Fin 416, P j.val)
    (last : ∀ j : Fin 14, P (416 + j.val)) :
    ∀ j : Fin 430, P j.val := by
  have hfirst : HoldsBlock P 0 416 := by
    intro j hj
    simpa using first ⟨j, hj⟩
  have hlast : HoldsBlock P (0 + 416) 14 := HoldsBlock.of_fin last
  simpa only [Nat.zero_add] using (hfirst.append hlast).to_fin

#print axioms HoldsBlock.append
end SimplificationProposals.CertificateBlocks
