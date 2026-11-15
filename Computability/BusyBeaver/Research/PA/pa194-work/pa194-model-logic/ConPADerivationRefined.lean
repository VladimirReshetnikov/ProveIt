import ConPADerivation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

/-!
# Compiling an internal derivation with the first cut premise exposed

Foundation's internal derivations of a theory `T` are elements `d` of a model `V` of `𝗜𝚺₁`;
`fstIdx d` is the sequent of `d`, a finite set of formula codes that is read as a
disjunction. This file proves, by `𝚺₁` induction on such a derivation, that a calculus
`Q : Quant V` refutes the translated sequent,

  `Pr (sseq e (fstIdx d) bot)`,

from requirements on the translation that mention one rule each. Here `tr e p` stands for
the negated translation of the formula `p` under the environment `e`, so that a derivation of
the sequent `s` becomes a derivation of `bot` from `tr e [s]`.

The requirements are the fields of `Sim`:

* `Adm e d`: the environment `e` is admissible for the derivation `d`. It must be `𝚷₁`, and
  it is inherited by the premises of every rule; the `∀` rule passes to `push e` and the shift
  rule to `pop e`. Environments are quantified below the fixed bound `bound`, which keeps the
  induction predicate `𝚺₁`.
* One theorem of the calculus per logical rule (`ruleAxL`, `ruleVerum`, `ruleAnd`, `ruleOr`,
  `ruleExs`, `ruleCut`), one per axiom of `T` (`ruleAxm`), and for the two rules that move
  free variables: `ruleAllShift`, `ruleAllFresh`, `ruleAll` and `ruleShift`.

`Sim.compile` is the induction and `Sim.proof` its instance for a proof of one formula. The
weakening rule needs no requirement. Nothing here constructs a `Sim`.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace ConPA.Sequent.CutPremise
open ConPA.Sequent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- What a translation `N` into the calculus `Q` has to satisfy for the internal derivations
of the theory `T` to be compiled. -/
structure Sim (Q : Quant V) (N : Tr V) (T : Theory L) [T.Δ₁] where
  /-- The code of falsum in the calculus. -/
  bot : V
  /-- A bound on the environments that occur. -/
  bound : V
  /-- `Adm e d`: the environment `e` is admissible for the derivation `d`. -/
  Adm : V → V → Prop
  adm_definable : 𝚷₁-Relation Adm
  /-- The environment of the premise of the `∀` rule. -/
  push : V → V
  /-- The environment of the premise of the shift rule. -/
  pop : V → V
  /-- The label that the `∀` rule generalizes. -/
  eig : V → V
  admAnd : ∀ {e s p q dp dq : V}, Adm e (andIntro s p q dp dq) → Adm e dp ∧ Adm e dq
  admOr : ∀ {e s p q d : V}, Adm e (orIntro s p q d) → Adm e d
  admAll : ∀ {e s p d : V}, Adm e (allIntro s p d) → push e ≤ bound ∧ Adm (push e) d
  admExs : ∀ {e s p t d : V}, Adm e (exsIntro s p t d) → Adm e d
  admWk : ∀ {e s d : V}, Adm e (wkRule s d) → Adm e d
  admShift : ∀ {e s d : V}, Adm e (shiftRule s d) → pop e ≤ bound ∧ Adm (pop e) d
  admCut : ∀ {e s p d₁ d₂ : V}, Adm e (cutRule s p d₁ d₂) → Adm e d₁ ∧ Adm e d₂
  ruleAxL : ∀ e s p : V, e ≤ bound → Adm e (Bootstrapping.axL s p) → IsFormulaSet L s →
    p ∈ s → neg L p ∈ s → Q.Pr (Q.imp (N.tr e p) (Q.imp (N.tr e (neg L p)) bot))
  ruleVerum : ∀ e s : V, e ≤ bound → Adm e (verumIntro s) → IsFormulaSet L s → ^⊤ ∈ s →
    Q.Pr (Q.imp (N.tr e ^⊤) bot)
  ruleAnd : ∀ e s p q dp dq : V, e ≤ bound → Adm e (andIntro s p q dp dq) →
    IsFormulaSet L s → p ^⋏ q ∈ s →
    Q.Pr (Q.imp (Q.imp (N.tr e p) bot) (Q.imp (Q.imp (N.tr e q) bot)
      (Q.imp (N.tr e (p ^⋏ q)) bot)))
  ruleOr : ∀ e s p q d : V, e ≤ bound → Adm e (orIntro s p q d) → IsFormulaSet L s →
    p ^⋎ q ∈ s →
    Q.Pr (Q.imp (Q.imp (N.tr e q) (Q.imp (N.tr e p) bot)) (Q.imp (N.tr e (p ^⋎ q)) bot))
  /-- A formula of the sequent keeps its translation when it is shifted and the environment
  is pushed. -/
  ruleAllShift : ∀ e s p d : V, e ≤ bound → Adm e (allIntro s p d) → IsFormulaSet L s →
    ^∀ p ∈ s → ∀ q ∈ s, Q.Pr (Q.imp (N.tr e q) (N.tr (push e) (shift L q)))
  /-- The generalized label is fresh for the sequent. -/
  ruleAllFresh : ∀ e s p d : V, e ≤ bound → Adm e (allIntro s p d) → IsFormulaSet L s →
    ^∀ p ∈ s → ∀ q ∈ s, Q.Pr (Q.imp (N.tr e q) (Q.all (eig e) (N.tr e q)))
  ruleAll : ∀ e s p d : V, e ≤ bound → Adm e (allIntro s p d) → IsFormulaSet L s →
    ^∀ p ∈ s →
    Q.Pr (Q.imp (Q.all (eig e) (Q.imp (N.tr (push e) (free L p)) bot))
      (Q.imp (N.tr e (^∀ p)) bot))
  ruleExs : ∀ e s p t d : V, e ≤ bound → Adm e (exsIntro s p t d) → IsFormulaSet L s →
    ^∃ p ∈ s → IsTerm L t →
    Q.Pr (Q.imp (Q.imp (N.tr e (substs1 L t p)) bot) (Q.imp (N.tr e (^∃ p)) bot))
  ruleShift : ∀ e d : V, e ≤ bound → Adm e (shiftRule (setShift L (fstIdx d)) d) →
    ∀ q ∈ fstIdx d, Q.Pr (Q.imp (N.tr e (shift L q)) (N.tr (pop e) q))
  ruleCut : ∀ e s p d₁ d₂ : V, e ≤ bound → Adm e (cutRule s p d₁ d₂) → IsFormulaSet L s →
    DerivationOf T d₁ (insert p s) →
    Q.Pr (Q.imp (Q.imp (N.tr e p) bot) (Q.imp (Q.imp (N.tr e (neg L p)) bot) bot))
  ruleAxm : ∀ e s p : V, e ≤ bound → Adm e (axm s p) → IsFormulaSet L s → p ∈ s →
    p ∈ T.Δ₁Class → Q.Pr (Q.imp (N.tr e p) bot)

attribute [instance] Sim.adm_definable

variable {Q : Quant V} {N : Tr V} {T : Theory L} [T.Δ₁]

/-- Every simulation for the original stronger interface remains a simulation
for the cut-premise interface. -/
def Sim.ofOriginal (S : ConPA.Sequent.Sim Q N T) : Sim Q N T where
  bot := S.bot
  bound := S.bound
  Adm := S.Adm
  adm_definable := S.adm_definable
  push := S.push
  pop := S.pop
  eig := S.eig
  admAnd := S.admAnd
  admOr := S.admOr
  admAll := S.admAll
  admExs := S.admExs
  admWk := S.admWk
  admShift := S.admShift
  admCut := S.admCut
  ruleAxL := S.ruleAxL
  ruleVerum := S.ruleVerum
  ruleAnd := S.ruleAnd
  ruleOr := S.ruleOr
  ruleAllShift := S.ruleAllShift
  ruleAllFresh := S.ruleAllFresh
  ruleAll := S.ruleAll
  ruleExs := S.ruleExs
  ruleShift := S.ruleShift
  ruleCut := by
    intro e s p d₁ d₂ he ha hs _
    exact S.ruleCut e s p d₁ d₂ he ha hs
  ruleAxm := S.ruleAxm

#print axioms Sim.ofOriginal

/-- The calculus refutes the translated sequent of every internal derivation, under every
admissible environment below the bound. -/
theorem Sim.compile (S : Sim Q N T) {d : V} (hd : Derivation T d) :
    ∀ e ≤ S.bound, S.Adm e d → Q.Pr (sseq Q.toCalc N e (fstIdx d) S.bot) := by
  have hP : 𝚺-[1]-Predicate (fun d : V => ∀ e ≤ S.bound, S.Adm e d →
      Q.Pr (sseq Q.toCalc N e (fstIdx d) S.bot)) := by
    simp only [sseq, setList]
    definability
  refine Derivation.induction1 𝚺 hP hd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs p hp hnp e he ha
    simp only [fstIdx_axL]
    exact sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e hnp)
      (sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e hp)
        (sseq_weaken Q.toCalc N (S.ruleAxL e s p he ha hs hp hnp) e s))
  · intro s hs h e he ha
    simp only [fstIdx_verumIntro]
    exact sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e h)
      (sseq_weaken Q.toCalc N (S.ruleVerum e s he ha hs h) e s)
  · intro s hs p q dp dq hpq hdp hdq ihp ihq e he ha
    simp only [fstIdx_andIntro]
    obtain ⟨hap, haq⟩ := S.admAnd ha
    have h1 := ihp e he hap
    rw [hdp.1] at h1
    have h2 := ihq e he haq
    rw [hdq.1] at h2
    exact sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e hpq)
      (sseq_mp Q.toCalc N ((sseq_insert_iff Q.toCalc N e q s S.bot).mp h2)
        (sseq_mp Q.toCalc N ((sseq_insert_iff Q.toCalc N e p s S.bot).mp h1)
          (sseq_weaken Q.toCalc N (S.ruleAnd e s p q dp dq he ha hs hpq) e s)))
  · intro s hs p q d hpq hd ih e he ha
    simp only [fstIdx_orIntro]
    have h1 := ih e he (S.admOr ha)
    rw [hd.1] at h1
    have h2 := (sseq_insert_iff Q.toCalc N e q s _).mp
      ((sseq_insert_iff Q.toCalc N e p (insert q s) S.bot).mp h1)
    exact sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e hpq)
      (sseq_mp Q.toCalc N h2 (sseq_weaken Q.toCalc N (S.ruleOr e s p q d he ha hs hpq) e s))
  · intro s hs p d hp hd ih e he ha
    simp only [fstIdx_allIntro]
    obtain ⟨hb, ha'⟩ := S.admAll ha
    have h1 := ih (S.push e) hb ha'
    rw [hd.1] at h1
    have h2 := (sseq_insert_iff Q.toCalc N (S.push e) (free L p) (setShift L s) S.bot).mp h1
    have h3 : Q.Pr (sseq Q.toCalc N e s (Q.imp (N.tr (S.push e) (free L p)) S.bot)) :=
      sseq_cut_rule Q.toCalc N h2 (by
        intro q' hq'
        obtain ⟨q, hq, rfl⟩ := mem_setShift_iff.mp hq'
        exact sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e hq)
          (sseq_weaken Q.toCalc N (S.ruleAllShift e s p d he ha hs hp q hq) e s))
    have h4 := sseq_gen N Q (S.eig e) h3
      (fun q hq => S.ruleAllFresh e s p d he ha hs hp q hq)
    exact sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e hp)
      (sseq_mp Q.toCalc N h4 (sseq_weaken Q.toCalc N (S.ruleAll e s p d he ha hs hp) e s))
  · intro s hs p t d hp ht hd ih e he ha
    simp only [fstIdx_exsIntro]
    have h1 := ih e he (S.admExs ha)
    rw [hd.1] at h1
    exact sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e hp)
      (sseq_mp Q.toCalc N ((sseq_insert_iff Q.toCalc N e (substs1 L t p) s S.bot).mp h1)
        (sseq_weaken Q.toCalc N (S.ruleExs e s p t d he ha hs hp ht) e s))
  · intro s hs d hsub hd ih e he ha
    simp only [fstIdx_wkRule]
    exact Q.mp (ih e he (S.admWk ha))
      (sseq_mono Q.toCalc N e (fstIdx d) s S.bot (fun p hp => subset_iff.mp hsub p hp))
  · intro s hs d hsd hd ih e he ha
    simp only [fstIdx_shiftRule]
    subst hsd
    obtain ⟨hb, ha'⟩ := S.admShift ha
    exact sseq_cut_rule Q.toCalc N (ih (S.pop e) hb ha') (fun q hq =>
      sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e (shift_mem_setShift hq))
        (sseq_weaken Q.toCalc N (S.ruleShift e d he ha q hq) e _))
  · intro s hs p d₁ d₂ h₁ h₂ ih₁ ih₂ e he ha
    simp only [fstIdx_cutRule]
    obtain ⟨ha1, ha2⟩ := S.admCut ha
    have k1 := ih₁ e he ha1
    rw [h₁.1] at k1
    have k2 := ih₂ e he ha2
    rw [h₂.1] at k2
    exact sseq_mp Q.toCalc N ((sseq_insert_iff Q.toCalc N e (neg L p) s S.bot).mp k2)
      (sseq_mp Q.toCalc N ((sseq_insert_iff Q.toCalc N e p s S.bot).mp k1)
        (sseq_weaken Q.toCalc N (S.ruleCut e s p d₁ d₂ he ha hs h₁) e s))
  · intro s hs p hp hT e he ha
    simp only [fstIdx_axm]
    exact sseq_mp Q.toCalc N (sseq_mem Q.toCalc N e hp)
      (sseq_weaken Q.toCalc N (S.ruleAxm e s p he ha hs hp hT) e s)

/-- A proof of `φ` gives a refutation of the translation of `φ`. -/
theorem Sim.proof (S : Sim Q N T) {d φ : V} (h : Proof T d φ) {e : V} (he : e ≤ S.bound)
    (ha : S.Adm e d) : Q.Pr (Q.imp (N.tr e φ) S.bot) := by
  have h1 := S.compile h.2 e he ha
  rw [h.1, singleton_eq_insert] at h1
  have h2 := (sseq_insert_iff Q.toCalc N e φ ∅ S.bot).mp h1
  simpa [emptyset_def] using h2

#print axioms Sim.compile
#print axioms Sim.proof
end model
end ConPA.Sequent.CutPremise
