import ZFCinPA.ValidatorQuantifierRules222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual C222 existential introduction from an arbitrary internally typed
source term. Its interpreted label may be zero, repeated or fallback1.
Singleton Eind-context alpha and typed vacuity discharge all extra guards.
The primitive equality witness is used only through weq→Eind. The final
object implication composes under any hypothesis without generalizing it.
No new syntax induction or arbitrary source-proof translation is used. -/
namespace LeanProofs.ZFCinPA.ValidatorExistentialRules222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open ValidatorEnvironmentAlpha222 ValidatorEnvironmentStreams222
open ValidatorEindContext222 ValidatorEnvironmentSubstitution222
open ValidatorQuantifierRules222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma ofDer {p : V} (d : D [] p) : CProv p :=
  d.sound cProv_classical (fun _ hm => absurd hm List.not_mem_nil)
private lemma ded1 {a p : V} (d : D [a] p) : CProv (wim a p) :=
  ofDer (Kalmar.deduction cProv_classical d)
private lemma ded2 {a b p : V} (d : D [b,a] p) : CProv (wim a (wim b p)) :=
  ofDer (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical d))

/-- Finite actual quantifier deduction. Only P is generalized under a
vacuity certificate; neither primitive equality nor Q is assumed vacuous. -/
lemma ex_intro_relational (x z P Q : V)
    (h : CProv (wim (weq x z) (wim P Q))) (hP : Vac x P) :
    CProv (wim P (ex x Q)) := by
  have hc : CProv (wim P (wim (weq x z) Q)) :=
    ded2 (.mp (.mp (.ax h) h0) h1)
  have hg := compose hP (all_mono x hc)
  have he : CProv (wim (wal x (wim (weq x z) Q)) (ex x Q)) :=
    ded1 (.mp (.mp (.ax (all_imp_ex x (weq x z) Q)) h0)
      (.ax (ex_equality x z)))
  exact compose hg he

private lemma stream_term {t F s : V} (ht : IsTerm ℒₛₑₜ t)
    (hs : StreamFree s F) : StreamEnv s (ValidatorEnvironmentLabels254.TermLabels.term F 0 t∷0) := by
  intro k
  exact avoid_cons (avoid_nil _) (term_label_avoids ht F 0 (s+2*k)
    (by simp) (hs k) (avoid_nil _))

/-- All singleton resources follow from typed term lookup and the original
stream. In particular no positivity or parity premise is imposed on z. -/
lemma term_fresh_pair {t : V} (ht : IsTerm ℒₛₑₜ t)
    (F s : V) (hs : StreamFree s F) :
    FreshPair F (eigen F s∷0) (ValidatorEnvironmentLabels254.TermLabels.term F 0 t∷0) (eigen F s+2) s := by
  have hr := fresh_resources F s hs
  have hn := streamFree_next hr.2.2.2.2
  refine ⟨hn,hs,?_,stream_term ht hn,?_,stream_term ht hs,?_⟩
  · intro k
    exact avoid_cons (avoid_nil _)
      (((stream_of_lt (z := eigen F s) (fresh := eigen F s+2) (by simp)) k).symm)
  · intro k
    exact avoid_cons (avoid_nil _) (hr.2.1 k).symm
  · intro i j
    rw [show (eigen F s+2)+2*i=eigen F s+2*(i+1) by ring]
    exact (alternateStart_apart F s j (i+1)).symm

section Transport

lemma instance_vac {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s : V) (hs : StreamFree s F) :
    Vac (eigen F s) (encode F (ValidatorEnvironmentLabels254.TermLabels.term F 0 t∷0) s p) := by
  have hr := fresh_resources F s hs
  exact encode_vac hp F (ValidatorEnvironmentLabels254.TermLabels.term F 0 t∷0) s (eigen F s) (by simp) hr.1
    (avoid_cons (avoid_nil _) (term_label_avoids ht F 0 (eigen F s)
      (by simp) hr.1 (avoid_nil _))) hr.2.1

/-- Reverse alpha retains precisely EC(x,z); the empty old context is
truth and is discharged by its actual checker witness. -/
lemma instance_primitive_transport {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s : V) (hs : StreamFree s F) :
    CProv (wim (weq (eigen F s) (ValidatorEnvironmentLabels254.TermLabels.term F 0 t))
      (wim (encode F (ValidatorEnvironmentLabels254.TermLabels.term F 0 t∷0) s p)
        (encode F (eigen F s∷0) (eigen F s+2) p))) := by
  have ha := encode_eq_under hp F (eigen F s∷0) (ValidatorEnvironmentLabels254.TermLabels.term F 0 t∷0)
    (eigen F s+2) s (by simp) (by simp) (term_fresh_pair ht F s hs)
  have hd := discharge_cons 0 0 (eigen F s) (ValidatorEnvironmentLabels254.TermLabels.term F 0 t) ha.2
  rw [eindContext_nil] at hd
  exact compose (Eq_Eind (eigen F s) (ValidatorEnvironmentLabels254.TermLabels.term F 0 t))
    (cProv_mp hd cProv_truth)

/-- Object implication from the actual source-term instance. All extra
freshness, singleton context and vacuity premises are discharged internally. -/
theorem ex_term_imp {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s : V) (hs : StreamFree s F) :
    CProv (wim (encode F 0 s (substs1 ℒₛₑₜ t p)) (encode F 0 s (^∃ p))) := by
  have hi := ex_intro_relational (eigen F s) (ValidatorEnvironmentLabels254.TermLabels.term F 0 t) _ _
    (instance_primitive_transport hp ht F s hs) (instance_vac hp ht F s hs)
  have he : ex (eigen F s) (encode F (eigen F s∷0) (eigen F s+2) p)=
      encode F 0 (eigen F s) (^∃ p) := (encode_exs F 0 (eigen F s) hp.isUFormula).symm
  rw [he] at hi
  have hr := encode_formula_relabel (show IsFormula ℒₛₑₜ (^∃ p) by simpa using hp)
    F (eigen F s) s (fresh_resources F s hs).2.2.2.2 hs
  rw [encode_substs1 hp ht F s]
  exact compose hi hr.1

theorem ex_term_rule {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s : V) (hs : StreamFree s F)
    (h : CProv (encode F 0 s (substs1 ℒₛₑₜ t p))) : CProv (encode F 0 s (^∃ p)) :=
  cProv_mp (ex_term_imp hp ht F s hs) h

/-- Pure composition under H: no generalization of H and no Vac H premise. -/
theorem ex_term_rule_under {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s H : V) (hs : StreamFree s F)
    (h : CProv (wim H (encode F 0 s (substs1 ℒₛₑₜ t p)))) :
    CProv (wim H (encode F 0 s (^∃ p))) := compose h (ex_term_imp hp ht F s hs)

end Transport
end LeanProofs.ZFCinPA.ValidatorExistentialRules222
