import IPRADerivations.AnalyticNumberTheory.Riemann.ERHData

/-! Imported from the packet `analytic-number-theory/riemann_hypotheses_ipra_2026-11-20`,
`MertensForms.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Supplementary standard-natural-number interpretations, for comparison with
the closed object sentences in Hypotheses. The existential constant is allowed
to depend exactly on the arguments to its left. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.MertensForms

def within (s : Int) (k c x : Nat) : Prop :=
  s.natAbs ^ (2*(k+1)) ≤ c * x ^ (k+2)

def RH : Prop := ∀ k : Nat, ∃ c : Nat, ∀ x : Nat, within (RHData.mertens x) k c x
def GRH : Prop := ∀ k : Nat, ∃ c : Nat, ∀ q a x : Nat,
  RHData.reducedClass q a = true → within (RHData.progressionMertens q a x) k c x
def ERH : Prop := ∀ f k : Nat, ∃ c : Nat, ∀ x : Nat, within (ERHData.mertens f x) k c x

theorem grh_implies_rh (h : GRH) : RH := by
  intro k
  obtain ⟨c, hc⟩ := h k
  exact ⟨c, fun x => hc 1 0 x RHData.reduced_one_zero⟩

theorem erh_implies_rh (h : ERH) : RH := by
  intro k
  obtain ⟨c, hc⟩ := h 0 k
  exact ⟨c, fun x => by simpa only [ERHData.mertens_zero_code] using hc x⟩
end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.MertensForms
