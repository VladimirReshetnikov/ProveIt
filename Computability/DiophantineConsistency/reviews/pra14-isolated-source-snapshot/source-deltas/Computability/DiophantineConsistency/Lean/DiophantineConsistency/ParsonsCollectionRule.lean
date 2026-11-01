import DiophantineConsistency.ParsonsCollection
import DiophantineConsistency.ParsonsRuleEmbedding
import Foundation.FirstOrder.Completeness.CounterModel
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsCollectionRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsCollection
variable {L : Language} [L.ORing]

def total (D : Semiproposition L 2) : Proposition L := “∀ i, ∃ y, !D i y”
def collector (D : Semiproposition L 2) : Semiproposition L 1 :=
  “k. ∃ b, ∀ i < k, ∃ y < b, !D i y”

theorem collector_sigma (D : Semiproposition L 2) (hD : Hierarchy 𝚺 1 D) :
    Hierarchy 𝚺 1 (collector D) := by
  simp [collector, hD]

theorem collector_base_eq (D : Semiproposition L 2) :
    base (collector D) = collection D ‘0’ := by
  simp [base, collector, collection, Semiformula.ballLT, Semiformula.bexsLT, ball, bexs, ← TransitiveRewriting.comp_app]
  constructor
  · change (Rew.subst ![‘0’]).q.q (#(Fin.last 2)) = ‘0’
    simp [Rew.q, Rew.subst]
  constructor
  · change (Rew.subst ![‘0’]).q.q.q (#(Fin.castSucc (Fin.last 2))) = #(Fin.last 2)
    simp [Rew.q, Rew.subst]
  · congr 2
    ext i
    · cases i using Fin.cases <;> simp [Rew.comp_app, Rew.q, Rew.subst]
    · simp [Rew.comp_app, Rew.q, Rew.subst]

/-- The only arithmetic input for the base case: no element is below zero. -/
def zeroMin : Proposition L := ∀⁰ ∼(outerGuard ‘0’)

theorem body_zero (D : Semiproposition L 2) :
    (collectionBody D ‘0’)/[‘0’] = bounded D ‘0’ ‘0’ := by
  simp [collectionBody, bounded, Semiformula.ballLT, Semiformula.bexsLT, ball, bexs,
    ← TransitiveRewriting.comp_app]
  constructor
  · change (Rew.subst ![‘0’]).q.q (#(Fin.last 2)) = ‘0’
    simp [Rew.q, Rew.subst]
  · congr 2
    ext i
    · cases i using Fin.cases <;> simp [Rew.comp_app, Rew.q, Rew.subst]
    · simp [Rew.comp_app, Rew.q, Rew.subst]

def base_logic (D : Semiproposition L 2) : Derivation [∼zeroMin, base (collector D)] := by
  let K := outerGuard (L := L) ‘0’
  let R := witnessGuard (L := L) ‘0’
  let D' : Semiproposition L 2 := D ⇜ ![#1,#0]
  have hp : Derivation [∼(∼K).free, (leftBody K R D').free] := by
    have h : Derivation [K.free, ∼K.free, ∃⁰ (R.free ⋏ D'.free)] :=
      Derivation.close K.free (by simp) (by simp)
    have h' : Derivation [∼K.free, ∃⁰ (R.free ⋏ D'.free), K.free] := h.contra (by simp)
    simpa [leftBody, Semiformula.imp_eq, ← TransitiveRewriting.comp_app] using
      h'.or.contra (Γ := [K.free, (∼K.free) ⋎ (∃⁰ (R.free ⋏ D'.free))]) (by simp)
  have ha : Derivation [∼zeroMin, bounded D ‘0’ ‘0’] := by
    simpa [zeroMin, K, R, D', fixed_left_eq] using all_mono (∼K) (leftBody K R D') hp
  have hs : Derivation [(collectionBody D ‘0’)/[‘0’], ∼zeroMin] := by
    simpa [body_zero] using ha.contra (Γ := [bounded D ‘0’ ‘0’, ∼zeroMin]) (by simp)
  have he := hs.exs
  simpa [collector_base_eq, collection_def] using he.contra
    (Γ := [∼zeroMin, ∃⁰ collectionBody D ‘0’]) (by simp)

omit [L.ORing] in
noncomputable def zeroMin_paminus : Proof 𝗣𝗔⁻ (zeroMin (L := ℒₒᵣ)) := by
  have h : 𝗣𝗔⁻ ⊢ (“∀ i, ¬ i < 0” : ArithmeticSentence) := by
    apply Arithmetic.complete.{0}
    intro M _ _
    simp [models_iff]
  have hp := ParsonsRuleEmbedding.embedTheory h.some
  simpa [zeroMin, outerGuard] using hp

/-- The actual collection induction base over PA-minus, without assuming
an additional induction axiom. -/
noncomputable def paminus_base (D : ArithmeticSemiformula ℕ 2) :
    Proof 𝗣𝗔⁻ (base (collector D)) := by
  have h : Derivation [zeroMin (L := ℒₒᵣ) 🡒 base (collector D)] := by
    simpa [Semiformula.imp_eq] using (base_logic D).or
  exact .mp (.logical h) zeroMin_paminus

/-- Conditional assembly of the collection inference. The still-missing
uniform finite-extension proof is stated explicitly as `stepFromTotal`;
the base and Σ₁ certificate are supplied by proved constructions above. -/
noncomputable def collect_if_step (D : ArithmeticSemiformula ℕ 2)
    (hD : Hierarchy 𝚺 1 D) (hTotal : Proof 𝗣𝗔⁻ (total D))
    (stepFromTotal : Proof 𝗣𝗔⁻ (total D 🡒 step (collector D))) :
    Proof 𝗣𝗔⁻ (∀⁰ collector D) :=
  .induction (collector_sigma D hD) (paminus_base D) (.mp stepFromTotal hTotal)

end DiophantineConsistency.ParsonsCollectionRule
