import DiophantineConsistency.ParsonsPositiveCertificate
import DiophantineConsistency.ParsonsPositiveGuard
/-! The exact existing guarded reduction preserves the positive-occurrence
certificate when its inputs and two predicate shapes are positive. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPositiveGuardCertificate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsBasePositive ParsonsPositiveRule ParsonsPositiveCertificate

@[simp] theorem positive_cast {T : Theory ℒₒᵣ} {φ ψ : Proposition ℒₒᵣ}
    (h : φ = ψ) (p : ParsonsRule.Proof T φ) :
    AllPositive (cast (congrArg (ParsonsRule.Proof T) h) p) ↔ AllPositive p := by
  cases h
  rfl

theorem three_disjunctions_positive {T : Theory ℒₒᵣ} (φ : ArithmeticSemiformula ℕ 1)
    (E : Proposition ℒₒᵣ) (t : SyntacticTerm ℒₒᵣ)
    (hφ : Positive φ) (hE : Positive E)
    (hb : ParsonsRule.Proof T (base φ ⋎ E)) (hs : ParsonsRule.Proof T (step φ ⋎ E))
    (hn : ParsonsRule.Proof T (∼(φ/[t]) ⋎ E))
    (hb' : AllPositive hb) (hs' : AllPositive hs) (hn' : AllPositive hn) :
    AllPositive (ParsonsRule.three_disjunctions φ E t (sigma hφ) (sigma hE) hb hs hn) := by
  simp [ParsonsRule.three_disjunctions, ParsonsRule.guard_result, AllPositive,
    positive_cast, positive_guard hφ hE, hs', hn']
  have he : base φ ⋎ E = base (ParsonsGuard.guard φ E) := by simp [base]
  have hc := (positive_cast he hb).mpr hb'
  convert hc using 1
  rfl
end DiophantineConsistency.ParsonsPositiveGuardCertificate
