import IPRABridge
import IPRADerivations.Core.Semiring

/-! Import the ConciseIPRA additive cancellation derivation at Foundation's
existing `PRALanguage.addCore` symbol. -/

set_option autoImplicit false

namespace IPRABridge.Checks

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open scoped LO.FirstOrder Fm
open DiophantineConsistency
open IPRAStandardTheory (standardTheory)
open IPRAOrderErasure (embed toNative)
open PRALanguage (language addCore)

private def conciseCancellation : Fm PTm 3 :=
  (PTm.var 0 + PTm.var 1 ≐ PTm.var 0 + PTm.var 2) ⟶ (PTm.var 1 ≐ PTm.var 2)

private theorem conciseCancellationProof : Prf PRAAx [] (Fm.all (Fm.all (Fm.all conciseCancellation))) := by
  refine .allI (.allI (.allI (.impI ?_)))
  exact LeanProofs.IPRA.add_left_cancel (a := PTm.var 0) Prf.hyp0

private def addCoreTerm {n : ℕ} (a b : PRATheory.TermN n) : PRATheory.TermN n :=
  PRATheory.applyCode addCore ![a, b]

private def equality {n : ℕ} (a b : PRATheory.TermN n) : Semisentenceᵢ language n :=
  .rel Language.ORing.Rel.eq ![a, b]

private theorem embed_eq {n : ℕ} (a b : PTm n) :
    embed (toFoundation (.eq a b)) =
      equality (Semiterm.lMap toNative (toFoundationTerm a))
        (Semiterm.lMap toNative (toFoundationTerm b)) := by
  change Semiformulaᵢ.rel (L := language) Language.ORing.Rel.eq _ =
    Semiformulaᵢ.rel (L := language) Language.ORing.Rel.eq _
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem embed_add {n : ℕ} (i j : Fin n) :
    Semiterm.lMap toNative (toFoundationTerm (PTm.var i + PTm.var j)) =
      addCoreTerm #i #j := by
  change Semiterm.func (L := language) addCore _ = Semiterm.func (L := language) addCore _
  congr 1
  funext k
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) k

private theorem cancellation_image :
    embed (toFoundation conciseCancellation) =
      (equality (addCoreTerm #0 #1) (addCoreTerm #0 #2) 🡒 equality #1 #2) := by
  change Semiformulaᵢ.imp (embed (toFoundation (.eq _ _)))
    (embed (toFoundation (.eq _ _))) = _
  rw [embed_eq, embed_eq, embed_add, embed_add]
  rfl

/-- Additive left cancellation for Foundation's existing recursion symbol. -/
theorem addCore_left_cancel :
    standardTheory ⊢
      (∀⁰ (∀⁰ (∀⁰ (equality (addCoreTerm #0 #1) (addCoreTerm #0 #2) 🡒
        equality #1 #2)))) := by
  have h := conciseToStandard conciseCancellationProof
  change standardTheory ⊢ ∀⁰ (∀⁰ (∀⁰ (embed (toFoundation conciseCancellation)))) at h
  rwa [cancellation_image] at h

#print axioms addCore_left_cancel

end IPRABridge.Checks
