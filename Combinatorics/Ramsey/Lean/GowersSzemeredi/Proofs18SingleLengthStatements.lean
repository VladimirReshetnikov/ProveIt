import GowersSzemeredi.Proofs18Consequences

/-! Single-length statements and their connection to the full final theorem.
These definitions and reductions do not require proofs of any special length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Theorem 18.2 at a single length `k`. -/
def Theorem182At (k : Nat) : Prop :=
  ∀ (delta : Real) (N : Nat), 0 < delta → delta ≤ 1 / 2 →
    szemerediThreshold delta k ≤ N →
    ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card → HasNatAP A k

/-- Corollary 18.7 at a single length `k`. -/
def Corollary187At (k : Nat) : Prop :=
  ∀ N : Nat, twoColorThreshold k ≤ N → ∀ color : Nat → Fin 2, HasMonochromaticAP N 2 color k

theorem theorem_18_2_iff_forall_length :
    theorem_18_2 ↔ ∀ k, 0 < k → Theorem182At k := by
  constructor
  · intro h k hk delta N hδ hδ2 hN A hA hc
    exact h delta k N hδ hδ2 hk hN A hA hc
  · intro h delta k N hδ hδ2 hk hN A hA hc
    exact h k hk delta N hδ hδ2 hN A hA hc

theorem corollary_18_7_iff_forall_length :
    corollary_18_7 ↔ ∀ k, 0 < k → Corollary187At k := by
  constructor
  · intro h k hk N hN color
    exact h k N hk hN color
  · intro h k N hk hN color
    exact h k hk N hN color

/-- Theorem 18.2 at a length gives Corollary 18.7 at that length. -/
theorem Theorem182At.corollary_18_7 {k : Nat} (h : Theorem182At k) : Corollary187At k :=
  corollary_18_7_at_of_half_density fun N hN A hA hc =>
    h (1 / 2) N (by norm_num) le_rfl hN A hA hc

end LeanProofs.GowersSzemeredi
