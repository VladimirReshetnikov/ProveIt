import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorProofContext222
import ZFCinPA.ValidatorExistentialRules222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual C222 quantifier deductions through internally sized contexts.
The general vacuity-guarded fold fixes its context and uses Σ₁ order induction
over sublists drawn from it; the source-specific fold uses a Σ₁ typed-list
invariant. Everything here is proved in IΣ₁. Every source hypothesis
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

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)

/-- The sole finite cons step uses the actual vacuity certificate for its head. -/
private lemma gen_cons {i a G g : V} (ha : Vac i a)
    (ih : CProv (wim (wal i (imps G g)) (imps G (wal i g)))) :
    CProv (wim (wal i (imps (a∷G) g)) (imps (a∷G) (wal i g))) := by
  simp only [imps_cons]
  exact ded2 (.mp (.ax ih)
    (.mp (.mp (.ax (all_distribution i a (imps G g))) h1) (.mp (.ax ha) h0)))

private instance imps_sigma1 : 𝚺₁-Function₂[V] imps := imps_definable
private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
private instance wal_sigma1 : 𝚺₁-Function₂[V] wal := wal_defined.to_definable₀
private instance len_delta : 𝚫₁-Function₁[V] (len : V → V) :=
  len_defined.graph_delta.to_definable
private instance nth_delta : 𝚫₁-Function₂[V] (nth : V → V → V) :=
  nth_defined.graph_delta.to_definable

/-- The fold's invariant is Σ₁ once the vacuity premise is moved outside the
induction: the context `G` is fixed and the induction runs over every list `H`
whose entries all occur in `G`. That membership antecedent is Δ₁, and each
entry inherits its Σ₁ vacuity certificate from `G`. -/
private lemma gen_invariant_sigma1 (i g G : V) : 𝚺₁-Predicate[V]
    (fun H => (∀ j < len H, ∃ k < len G, H.[j] = G.[k]) →
      CProv (wim (wal i (imps H g)) (imps H (wal i g)))) := by
  definability

/-- Generalization through a context of vacuous hypotheses, by Σ₁ order
induction over the sublists drawn from the fixed context. -/
theorem cProv_gen_context (i g G : V) (hG : ∀ j < len G, Vac i G.[j]) :
    CProv (wim (wal i (imps G g)) (imps G (wal i g))) := by
  have main : ∀ H : V, (∀ j < len H, ∃ k < len G, H.[j] = G.[k]) →
      CProv (wim (wal i (imps H g)) (imps H (wal i g))) := by
    intro H
    induction H using ISigma1.sigma1_order_induction
    · exact gen_invariant_sigma1 i g G
    case ind H ih =>
      intro hH
      rcases nil_or_adjoin H with (rfl | ⟨a,H,rfl⟩)
      · simpa using self_imp (wal i g)
      · have ha : Vac i a := by
          obtain ⟨k,hk,he⟩ := hH 0 (by simp)
          simp only [nth_adjoin_zero] at he
          exact he ▸ hG k hk
        have ht : ∀ j < len H, ∃ k < len G, H.[j] = G.[k] := fun j hj => by
          simpa using hH (j+1) (by simpa using hj)
        exact gen_cons ha (ih H (by simp) ht)
  exact main G (fun j hj => ⟨j,hj,rfl⟩)

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

/-- Generalization through the encoded context uses its vacuity certificates. -/
theorem cProv_gen_source_context (F s g : V) (hs : StreamFree s F) : ∀ L : V,
    (∀ j < len L, IsFormula ℒₛₑₜ L.[j]) →
    CProv (wim (wal (eigen F s) (imps (negEnc F s L) g))
      (imps (negEnc F s L) (wal (eigen F s) g))) := fun L hL =>
  cProv_gen_context (eigen F s) g (negEnc F s L) (negEnc_vacuous F s L hs hL)

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

end LeanProofs.ZFCinPA.ValidatorSourceQuantifierContext222
