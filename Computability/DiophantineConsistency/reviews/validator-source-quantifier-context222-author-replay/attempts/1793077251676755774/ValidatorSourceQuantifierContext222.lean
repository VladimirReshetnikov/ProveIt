import ZFCinPA.ValidatorProofContext222
import ZFCinPA.ValidatorExistentialRules222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual C222 quantifier deductions through internally sized contexts.
The general vacuity-guarded fold uses explicit Π₂ induction under IΣ₂.
The source-specific fold uses a Σ₁ typed-list invariant, retaining IΣ₂ for
the previously proved encoded-formula vacuity theorem. Every source hypothesis
vacuity is derived from typing and the actual fresh-label resources. No blanket
GEN-under-hypotheses rule, source axiom image, or complete proof interpretation
is assumed. Existing R2Quant is a source-only guide and is not imported. -/
namespace LeanProofs.ZFCinPA.ValidatorSourceQuantifierContext222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorFormulaEncoder222
open ValidatorProofContext222 ValidatorEnvironmentVacuity222 ValidatorEnvironmentAlpha222
open ValidatorQuantifierRules222 ValidatorExistentialRules222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma ded2 {a b p : V} (h : D [b,a] p) : CProv (wim a (wim b p)) :=
  (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical h)).sound
    cProv_classical (fun _ hm => absurd hm List.not_mem_nil)

/-- The sole finite cons step uses the actual vacuity certificate for its head. -/
private lemma gen_cons {i a G g : V} (ha : Vac i a)
    (ih : CProv (wim (wal i (imps G g)) (imps G (wal i g)))) :
    CProv (wim (wal i (imps (a∷G) g)) (imps (a∷G) (wal i g))) := by
  simp only [imps_cons]
  exact ded2 (.mp (.ax ih)
    (.mp (.mp (.ax (all_distribution i a (imps G g))) h1) (.mp (.ax ha) h0)))

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma sigma1_to_pi2 {k : ℕ} {P : (Fin k → V) → Prop}
    (h : 𝚺₁.Definable P) : (𝚷-[2]).Definable P := by
  rcases h with ⟨φ,hφ⟩
  refine ⟨.mkPi φ.val (φ.sigma_prop.strict_mono 𝚷 (by decide)),?_⟩
  intro v
  simpa only [HierarchySymbol.Semiformula.val_mkPi] using (hφ.iff (v := v))

private instance vac_sigma1 : 𝚺₁-Relation[V] Vac := by unfold Vac; definability
private instance vac_sigma2 : 𝚺-[2]-Relation[V] Vac := by
  rcases vac_sigma1 (V := V) with ⟨φ,hφ⟩
  refine ⟨.mkSigma φ.val (φ.sigma_prop.strict_mono 𝚺 (by decide)),?_⟩
  intro v
  simpa only [HierarchySymbol.Semiformula.val_mkSigma] using (hφ.iff (v := v))
private instance cProv_pi2 : 𝚷-[2]-Predicate[V] CProv := sigma1_to_pi2 cProv_definable
private instance imps_sigma2 : 𝚺-[2]-Function₂[V] imps := imps_definable.of_sigmaOne
private instance wim_sigma2 : 𝚺-[2]-Function₂[V] wim := wim_defined.to_definable₀
private instance wal_sigma2 : 𝚺-[2]-Function₂[V] wal := wal_defined.to_definable₀
private instance len_sigma2 : 𝚺-[2]-Function₁[V] (len : V → V) :=
  len_defined.graph_delta.to_definable.of_deltaOne
private instance nth_sigma2 : 𝚺-[2]-Function₂[V] (nth : V → V → V) :=
  nth_defined.graph_delta.to_definable.of_deltaOne

private lemma gen_invariant_pi2 (i g : V) : 𝚷-[2]-Predicate[V]
    (fun G => (∀ j < len G, Vac i G.[j]) →
      CProv (wim (wal i (imps G g)) (imps G (wal i g)))) := by
  apply HierarchySymbol.Definable.imp
  · definability
  · definability

section General
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- No claim of IΣ₁ induction for a context of arbitrary Σ₁ vacuity premises. -/
theorem cProv_gen_context (i g G : V) (hG : ∀ j < len G, Vac i G.[j]) :
    CProv (wim (wal i (imps G g)) (imps G (wal i g))) := by
  have main : ∀ G : V, (∀ j < len G, Vac i G.[j]) →
      CProv (wim (wal i (imps G g)) (imps G (wal i g))) := by
    apply InductionOnHierarchy.order_induction_sigma 𝚷 2
      (P := fun G => (∀ j < len G, Vac i G.[j]) →
        CProv (wim (wal i (imps G g)) (imps G (wal i g))))
    · exact gen_invariant_pi2 i g
    · intro G ih hG
      rcases nil_or_adjoin G with (rfl | ⟨a,G,rfl⟩)
      · simpa using self_imp (wal i g)
      · have ha : Vac i a := by simpa using hG 0 (by simp)
        have ht : ∀ j < len G, Vac i G.[j] := fun j hj => by
          simpa using hG (j+1) (by simpa using hj)
        exact gen_cons ha (ih G (by simp) ht)
  exact main G hG

theorem der_gen (i : V) {G g : V} (hG : ∀ j < len G, Vac i G.[j])
    (h : Der G g) : Der G (wal i g) :=
  cProv_mp (cProv_gen_context i g G hG) (cProv_gen i h)

/-- All negative encoded source hypotheses are vacuous in the selected label.
The original stream safety includes fallback 1 and every future binder. -/
theorem negEnc_vacuous (F s L : V) (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j]) :
    ∀ j < len (negEnc F s L), Vac (eigen F s) (negEnc F s L).[j] := by
  obtain ⟨hl,hn⟩ := negEnc_len_nth F s L
  intro j hj
  have hj' : j < len L := by simpa only [hl] using hj
  rw [hn j hj']
  have hr := fresh_resources F s hs
  exact vac_neg (encode_formula_vac (hL j hj') F s (eigen F s) hr.1 hr.2.1)

theorem negEnc_member_vacuous (F s L : V) (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j]) {a : V}
    (ha : a ∈ᵥ negEnc F s L) : Vac (eigen F s) a := by
  obtain ⟨j,hj,rfl⟩ := ha
  exact negEnc_vacuous F s L hs hL j hj

/-- This fold's invariant is Σ₁: the typed-list antecedent is Δ₁.
IΣ₂ remains explicit for encoded-formula vacuity, not for this list induction. -/
theorem cProv_gen_source_context (F s g : V) (hs : StreamFree s F) : ∀ L : V,
    (∀ j < len L, IsFormula ℒₛₑₜ L.[j]) →
    CProv (wim (wal (eigen F s) (imps (negEnc F s L) g))
      (imps (negEnc F s L) (wal (eigen F s) g))) := by
  intro L
  induction L using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; simpa using self_imp (wal (eigen F s) g)
  case adjoin a L ih =>
    intro hL
    have ha : IsFormula ℒₛₑₜ a := by simpa using hL 0 (by simp)
    have ht : ∀ j < len L, IsFormula ℒₛₑₜ L.[j] := fun j hj => by
      simpa using hL (j+1) (by simpa using hj)
    have hr := fresh_resources F s hs
    have va := vac_neg (encode_formula_vac ha F s (eigen F s) hr.1 hr.2.1)
    simpa only [negEnc_cons] using gen_cons va (ih ht)

/-- ALL introduction through the unchanged base source context. -/
theorem all_intro_opened {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s L : V) (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j])
    (h : Der (negEnc F s L)
      (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p))) :
    Der (negEnc F s L) (encode F 0 s (^∀ p)) := by
  have hg : Der (negEnc F s L)
      (wal (eigen F s) (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p))) :=
    cProv_mp (cProv_gen_source_context F s _ hs L hL) (cProv_gen (eigen F s) h)
  exact der_mp (der_of (all_opened_equiv hp F s hs).1) hg

/-- Literal source shifting tails the extended free environment. -/
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] in
theorem shifted_context (F s L x : V)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j]) :
    negEnc (x∷F) s (shiftList L) = negEnc F s L := by
  have ht : ∀ p, p ∈ᵥ L → IsUFormula ℒₛₑₜ p := by
    rintro p ⟨j,hj,rfl⟩
    exact (hL j hj).isUFormula
  simpa only [ValidatorEnvironmentLabels254.tail_cons] using
    negEnc_shiftList (x∷F) s L ht

theorem all_intro_shifted {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s L : V) (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j])
    (h : Der (negEnc (eigen F s∷F) s (shiftList L))
      (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p))) :
    Der (negEnc F s L) (encode F 0 s (^∀ p)) := by
  rw [shifted_context F s L (eigen F s) hL] at h
  exact all_intro_opened hp F s L hs hL h

/-- The context is arbitrary: EXS term introduction requires no context vacuity. -/
theorem ex_intro_term {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s G : V) (hs : StreamFree s F)
    (h : Der G (encode F 0 s (substs1 ℒₛₑₜ t p))) :
    Der G (encode F 0 s (^∃ p)) :=
  der_mp (der_of (ex_term_imp hp ht F s hs)) h

end General

/-- Classical sequent recovery uses the actual numeric negative hypothesis,
not source NNF negation or a semantic truth predicate. -/
theorem seqC_cons_iff_der (F s L p : V) :
    CProv (seqC F s (p∷L)) ↔ Der (negEnc F s L) (encode F 0 s p) := by
  simp only [seqC,negEnc_cons]
  change Der (ValidatorRelationalCore222.neg (encode F 0 s p)∷negEnc F s L) 1 ↔ _
  constructor
  · exact der_byContra
  · intro h
    exact der_undeduct (der_mp (der_of (double_neg_intro _)) h)

section SourceRules
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

theorem seqC_all {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s L : V) (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j])
    (h : CProv (seqC (eigen F s∷F) s (free ℒₛₑₜ p∷shiftList L))) :
    CProv (seqC F s ((^∀ p)∷L)) :=
  (seqC_cons_iff_der F s L (^∀ p)).mpr
    (all_intro_shifted hp F s L hs hL
      ((seqC_cons_iff_der (eigen F s∷F) s (shiftList L) (free ℒₛₑₜ p)).mp h))

theorem seqC_exs {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s L : V) (hs : StreamFree s F)
    (h : CProv (seqC F s (substs1 ℒₛₑₜ t p∷L))) :
    CProv (seqC F s ((^∃ p)∷L)) :=
  (seqC_cons_iff_der F s L (^∃ p)).mpr
    (ex_intro_term hp ht F s (negEnc F s L) hs
      ((seqC_cons_iff_der F s L (substs1 ℒₛₑₜ t p)).mp h))

theorem all_context_witness {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s L : V) (hs : StreamFree s F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j])
    (h : Der (negEnc (eigen F s∷F) s (shiftList L))
      (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p))) :
    ∃ code : V, ArithmeticHistory222.value code =
      imps (negEnc F s L) (encode F 0 s (^∀ p)) + 1 :=
  all_intro_shifted hp F s L hs hL h

theorem ex_context_witness {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s G : V) (hs : StreamFree s F)
    (h : Der G (encode F 0 s (substs1 ℒₛₑₜ t p))) :
    ∃ code : V, ArithmeticHistory222.value code = imps G (encode F 0 s (^∃ p)) + 1 :=
  ex_intro_term hp ht F s G hs h

end SourceRules
end LeanProofs.ZFCinPA.ValidatorSourceQuantifierContext222
