import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

/-!
All-internal proof transport from derivability of the source axioms.

The language and two Delta1 theories are fixed. Proofs, formulas, and finite
sequents are arbitrary elements of an IΣ1 model; no standard-code premise or
canonical selector is used. The source-to-target axiom-provability premise
remains explicit. This same-language substitution lemma does not supply a
relativization, interpretation, ZF/ZFC comparison, or C254 presentation adapter.
-/
namespace LeanProofs.BoundedPAConsistency.InternalAxiomProofTransport

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

/-- Substitute represented target proofs for axiom leaves of any internal
source derivation. The Sigma1 induction predicate is target Derivable at the
source's exact coded end sequent. -/
theorem derivable_of_axioms_provable
    (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    {d : V} (hd : Derivation T d) : Derivable U (fstIdx d) := by
  apply Derivation.induction1 𝚺
    (P := fun d : V => Derivable U (fstIdx d)) (by definability) hd
  · intro s hs p hp hn
    simpa only [fstIdx_axL] using Derivable.em (T := U) hs p hp hn
  · intro s hs hp
    simpa only [fstIdx_verumIntro] using Derivable.verum (T := U) hs hp
  · intro s _ p q dp dq hpq hdp hdq ihp ihq
    rw [hdp.1] at ihp
    rw [hdq.1] at ihq
    simpa only [fstIdx_andIntro] using Derivable.and_m hpq ihp ihq
  · intro s _ p q dp hpq hdp ihp
    rw [hdp.1] at ihp
    simpa only [fstIdx_orIntro] using Derivable.or_m hpq ihp
  · intro s _ p dp hp hdp ihp
    rw [hdp.1] at ihp
    simpa only [fstIdx_allIntro] using Derivable.all_m hp ihp
  · intro s _ p t dp hp ht hdp ihp
    rw [hdp.1] at ihp
    simpa only [fstIdx_exsIntro] using Derivable.ex_m hp ht ihp
  · intro s hs dp hss _ ihp
    simpa only [fstIdx_wkRule] using Derivable.wk hs hss ihp
  · intro s _ dp he _ ihp
    simpa only [fstIdx_shiftRule, he] using Derivable.shift ihp
  · intro s _ p dp dn hdp hdn ihp ihn
    rw [hdp.1] at ihp
    rw [hdn.1] at ihn
    simpa only [fstIdx_cutRule] using Derivable.cut p ihp ihn
  · intro s hs p hp hT
    have hpU : Derivable U (insert p (∅ : V)) := (hAx p (hs p hp) hT).toDerivable
    have hss : insert p (∅ : V) ⊆ s := by
      intro q hq
      have he : q = p := by simpa using hq
      simpa only [he] using hp
    simpa only [fstIdx_axm] using Derivable.wk hs hss hpU

/-- The accepted target proof may differ from the input source proof code. -/
theorem provable_of_axioms_provable
    (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    {p : V} (hp : Provable T p) : Provable U p := by
  obtain ⟨d, hd⟩ := hp.toDerivable
  apply Derivable.toProvable
  rw [← hd.1]
  exact derivable_of_axioms_provable hAx hd.2

/-- Mutual all-internal axiom derivability gives all-internal theorem
agreement, with no interpretation or semantic model construction. -/
theorem provable_iff_of_mutual_axiom_provability
    (hTU : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    (hUT : ∀ p : V, IsFormula L p → p ∈ U.Δ₁Class → Provable T p) (p : V) :
    Provable T p ↔ Provable U p :=
  ⟨provable_of_axioms_provable hTU, provable_of_axioms_provable hUT⟩

end LeanProofs.BoundedPAConsistency.InternalAxiomProofTransport
