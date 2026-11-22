import IPRADerivations.Foundations.QuantifierTransport
import IPRADerivations.Core.Order

/-!
# The constructive logical core of the Richardson reduction, inside iPRA

Packet: `foundations/Richardson_iPRA_2026-11-19`, `lean/LogicalCore.lean`: "These are constructive METATHEOREMS in
Lean's ambient logic. They are not object-language proofs in `ConciseIPRA.Prf PRAAx`." Here they are object-level
derivations, for arbitrary formulas of iPRA, with `iff A B = (A ⟶ B) ⋏ (B ⟶ A)` and `neg A = A ⟶ ⊥`:

* `neg_iff_of_dneg_iff` (`negIffOfDoubleNegIff`): `¬¬H ↔ ¬¬S` gives `¬H ↔ ¬S` ("Negative translation needs no
  positive witness extraction");
* `neg_iff_of_iff` (`negIffOfIff`), `identity_iff_no_source` (`identityIffNoSource`) and
  `negative_calibration` (`negativeCalibration`: "No step changes a double-negated existential into an
  existential");
* `witness_equivalence` (`witnessEquivalence`): explicit forward and backward witness terms with their
  correctness derivations give `∃w O(w) ↔ ∃w S(w)` (via `Foundations/QuantifierTransport.pushEx`), and
  `identity_equivalence` the corresponding absence equivalence.
-/

namespace LeanProofs.IPRA.Foundations.RichardsonLogic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.QuantifierTransport (pushEx)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `A ↔ B`. -/
def iffF (A B : Fm PTm n) : Fm PTm n := (A ⟶ B) ⋏ (B ⟶ A)

theorem neg_iff_of_iff {A B : Fm PTm n} (h : Γ ⊢[PRAAx] iffF A B) : Γ ⊢[PRAAx] iffF (neg A) (neg B) := by
  refine .andI (.impI (.impI ?_)) (.impI (.impI ?_))
  · exact .impE Prf.hyp1 (.impE h.andE₂.wk.wk Prf.hyp0)
  · exact .impE Prf.hyp1 (.impE h.andE₁.wk.wk Prf.hyp0)

theorem neg_iff_of_dneg_iff {H S : Fm PTm n} (h : Γ ⊢[PRAAx] iffF (neg (neg H)) (neg (neg S))) :
    Γ ⊢[PRAAx] iffF (neg H) (neg S) := by
  refine .andI (.impI (.impI ?_)) (.impI (.impI ?_))
  · -- context `S, ¬H`
    have dS : (S :: neg H :: Γ) ⊢[PRAAx] neg (neg S) := .impI (.impE Prf.hyp0 Prf.hyp1)
    exact .impE (.impE h.andE₂.wk.wk dS) Prf.hyp1
  · -- context `H, ¬S`
    have dH : (H :: neg S :: Γ) ⊢[PRAAx] neg (neg H) := .impI (.impE Prf.hyp0 Prf.hyp1)
    exact .impE (.impE h.andE₁.wk.wk dH) Prf.hyp1

theorem identity_iff_no_source {I O S : Fm PTm n} (idSpec : Γ ⊢[PRAAx] iffF I (neg O))
    (wSpec : Γ ⊢[PRAAx] iffF O S) : Γ ⊢[PRAAx] iffF I (neg S) := by
  refine .andI (.impI (.impI ?_)) (.impI ?_)
  · -- context `S, I`
    exact .impE (.impE idSpec.andE₁.wk.wk Prf.hyp1) (.impE wSpec.andE₂.wk.wk Prf.hyp0)
  · -- context `¬S`
    exact .impE idSpec.andE₂.wk (.impI (.impE Prf.hyp1 (.impE wSpec.andE₁.wk.wk Prf.hyp0)))

theorem negative_calibration {I O Sol H : Fm PTm n} (idSpec : Γ ⊢[PRAAx] iffF I (neg O))
    (analyticSpec : Γ ⊢[PRAAx] iffF O Sol) (translated : Γ ⊢[PRAAx] iffF (neg (neg H)) (neg (neg Sol))) :
    Γ ⊢[PRAAx] iffF I (neg H) := by
  have absent := identity_iff_no_source idSpec analyticSpec
  have negative := neg_iff_of_dneg_iff translated
  refine .andI (.impI ?_) (.impI ?_)
  · exact .impE negative.andE₂.wk (.impE absent.andE₁.wk Prf.hyp0)
  · exact .impE absent.andE₂.wk (.impE negative.andE₁.wk Prf.hyp0)

/-- Explicit witness maps give `∃w O(w) ↔ ∃w S(w)`. -/
theorem witness_equivalence {S O : Fm PTm (n + 1)} {fw bw : PTm (n + 1)}
    (forwardCorrect : Γ.map Fm.shift ⊢[PRAAx] S ⟶ O.subst (repl fw))
    (backwardCorrect : Γ.map Fm.shift ⊢[PRAAx] O ⟶ S.subst (repl bw)) :
    Γ ⊢[PRAAx] iffF (Fm.ex O) (Fm.ex S) :=
  .andI (pushEx O S bw backwardCorrect) (pushEx S O fw forwardCorrect)

/-- The absence of observations is equivalent to the absence of sources. -/
theorem identity_equivalence {S O : Fm PTm (n + 1)} {fw bw : PTm (n + 1)}
    (forwardCorrect : Γ.map Fm.shift ⊢[PRAAx] S ⟶ O.subst (repl fw))
    (backwardCorrect : Γ.map Fm.shift ⊢[PRAAx] O ⟶ S.subst (repl bw)) :
    Γ ⊢[PRAAx] iffF (neg (Fm.ex O)) (neg (Fm.ex S)) :=
  neg_iff_of_iff (witness_equivalence forwardCorrect backwardCorrect)

end LeanProofs.IPRA.Foundations.RichardsonLogic
