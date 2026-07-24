import BoundedZFCConsistency.Basic
import BoundedZFCConsistency.Choice
import FirstOrder.Compactness

/-!
# Model-relative consistency of the restricted calculus

The arithmetic counterpart of this project rules out a restricted derivation of
falsity outright, by evaluating the derivation in the standard model of
arithmetic.  Set theory admits no such unconditional argument here, so the
statements below carry a model of the axiom set as an explicit hypothesis.

That hypothesis is not vacuous and not unreachable.  Lean's type theory with
universes is stronger than ZFC and does prove that ZFC has a model; the vendored
Foundation library constructs one and checks the axioms.  What is missing is a
bridge between that model, which inhabits Foundation's own language of set
theory, and the `Form` syntax used here.  Until such a bridge exists, honesty
requires the hypothesis to stay visible.

Nothing in this file is a step toward `ZFC |- Con_n(ZFC)`.  That theorem is
proved *inside* the object theory, by reflection, and never appeals to an
external model.  These results only confirm that the restricted calculus of
`BoundedZFCConsistency.Basic` is not degenerate: relative to a model it refutes
nothing, exactly as an honest proof restriction should.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.FirstOrderCompactness

/-! ## Restricted derivations of falsity, relative to a model -/

/-- A theory with a model has no derivation of falsity whose every formula
occurrence is bounded.

The bound plays no role in the argument: erasure turns the restricted
derivation into an ordinary one, and soundness evaluates that in the given
model.  Recording the statement at every bound is nevertheless the form the
later development consumes. -/
theorem not_restrictedBProv_bot_of_hasModel {T : Form → Prop} (n : Nat)
    (hmodel : TheoryHasModel T) :
    ¬ RestrictedBProv n T [] Form.fBot := by
  intro hrestricted
  obtain ⟨Dom, m, v, hsat⟩ := hmodel
  have hordinary : BProv T [] Form.fBot := restrictedBProv_erase hrestricted
  exact soundness_BProv hordinary v hsat (by intro g hg; cases hg)

/-- The same statement for the unrestricted calculus, recorded so that the
restricted result above is visibly weaker than plain consistency rather than
independent of it. -/
theorem not_bProv_bot_of_hasModel {T : Form → Prop} (hmodel : TheoryHasModel T) :
    ¬ BProv T [] Form.fBot := by
  intro hordinary
  obtain ⟨Dom, m, v, hsat⟩ := hmodel
  exact soundness_BProv hordinary v hsat (by intro g hg; cases hg)

/-- Bounded refutations are refutations: a model-relative consistency statement
at one bound follows from ordinary consistency, never the other way round. -/
theorem not_restrictedBProv_bot_of_not_bProv_bot {T : Form → Prop} (n : Nat)
    (h : ¬ BProv T [] Form.fBot) :
    ¬ RestrictedBProv n T [] Form.fBot :=
  fun hrestricted => h (restrictedBProv_erase hrestricted)

/-! ## Specialization to the repository's ZF axioms -/

/-- No bounded ZF derivation refutes falsity, relative to a model of the ZF
axioms. -/
theorem not_restrictedZFprov_bot_of_hasModel (n : Nat)
    (hmodel : TheoryHasModel ZFax) :
    ¬ RestrictedZFprov n Form.fBot :=
  not_restrictedBProv_bot_of_hasModel n hmodel

/-! ## Specialization to ZFC -/

/-- Bounded ZFC derivations relative to the axiom set with choice. -/
def RestrictedZFCprov (n : Nat) (phi : Form) : Prop :=
  RestrictedBProv n ZFCax [] phi

/-- Erasing a bounded ZFC derivation gives an ordinary one. -/
theorem restrictedZFCprov_erase {n : Nat} {phi : Form}
    (h : RestrictedZFCprov n phi) : ZFCprov phi := by
  rcases h with ⟨L, hL, proof, _⟩
  exact ⟨L, hL, by simpa using eraseProvTree proof⟩

/-- The bound is monotone in ZFC exactly as in the generic calculus. -/
theorem restrictedZFCprov_mono {m n : Nat} (hmn : m ≤ n) {phi : Form}
    (h : RestrictedZFCprov m phi) : RestrictedZFCprov n phi :=
  restrictedBProv_mono hmn h

/-- Every ordinary ZFC derivation is bounded at some metatheoretic level.
This cofinality is the property the intended theorem actually uses: the family
of restricted consistency statements exhausts all derivations. -/
theorem restrictedZFCprov_cofinal {phi : Form} (h : ZFCprov phi) :
    ∃ n : Nat, RestrictedZFCprov n phi := by
  obtain ⟨L, hL, hprov⟩ := h
  obtain ⟨proof⟩ := provTree_complete (G := L ++ []) (by simpa using hprov)
  exact ⟨proofOccurrenceRank proof, L, hL, proof, Nat.le_refl _⟩

/-- A bounded ZF derivation is a bounded ZFC derivation. -/
theorem restrictedZFCprov_of_restrictedZFprov {n : Nat} {phi : Form}
    (h : RestrictedZFprov n phi) : RestrictedZFCprov n phi := by
  rcases h with ⟨L, hL, hrestricted⟩
  exact ⟨L, fun x hx => ZFCax_of_ZFax (hL x hx), hrestricted⟩

/-- No bounded ZFC derivation refutes falsity, relative to a model of ZFC.

This is the honest set-theoretic counterpart of the arithmetic project's
phase-one consistency theorem.  The model hypothesis is genuinely required
here; see the module header. -/
theorem not_restrictedZFCprov_bot_of_hasModel (n : Nat)
    (hmodel : TheoryHasModel ZFCax) :
    ¬ RestrictedZFCprov n Form.fBot :=
  not_restrictedBProv_bot_of_hasModel n hmodel

end BoundedZFCConsistency
end LeanProofs
