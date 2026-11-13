import ZFCinPA.ValidatorLabelAvoidance
import ZFCinPA.ValidatorEqualityContextVacuity254
import ZFCinPA.ValidatorEqualityCore254

import ZFCinPA.ValidatorImplicationContext

set_option autoImplicit false
noncomputable section

/-!
Source-only alpha-conversion draft. Every source formula, stack, label and
stream index is internal. The two future binder streams are explicitly apart
and avoid both old stacks and every free label, including fallback 1. This
module does not choose parity-separated streams or identify a fixed encoder.
-/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ValidatorProvability254 ValidatorQuantifierCore254
open ValidatorEqualityCore254 ValidatorEqualityContext254
open ValidatorEnvironmentLabels254 ValidatorEnvironmentVacuity254
open ValidatorEqualityContextVacuity254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def StreamEnv (s B : V) : Prop := ∀ k : V, Avoid (s+2*k) B
def StreamFree (s F : V) : Prop := ∀ k : V, FreeAvoid (s+2*k) F
def Apart (s t : V) : Prop := ∀ i j : V, s+2*i ≠ t+2*j

def FreshPair (F B B' s t : V) : Prop :=
  StreamFree s F ∧ StreamFree t F ∧
  StreamEnv s B ∧ StreamEnv s B' ∧
  StreamEnv t B ∧ StreamEnv t B' ∧ Apart s t


lemma streamFree_next {s F : V} (h : StreamFree s F) : StreamFree (s+2) F :=
  ValidatorLabelAvoidance.streamFree_next h

lemma streamEnv_cons_next {s B x : V} (h : StreamEnv s B)
    (hx : ∀ k : V, (s+2)+2*k≠x) : StreamEnv (s+2) (x∷B) :=
  ValidatorLabelAvoidance.streamEnv_cons_next h hx

lemma freshPair_next {F B B' s t : V} (h : FreshPair F B B' s t) :
    FreshPair F (s∷B) (t∷B') (s+2) (t+2) :=
  ValidatorLabelAvoidance.freshPair_next h

/-- Both cross-body vacuity arguments, with no assertion that a binder is
vacuous in its own body. The right side still has the left-to-right context. -/
lemma cross_body_vac [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ (n+1) p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (h : FreshPair F B B' s t) :
    Vac s (encode F (t∷B') (t+2) p) ∧
    Vac t (encode F (s∷B) (s+2) p) :=
  ValidatorLabelAvoidance.cross_body_vac (P := Vac) (enc := encode)
    (fun hp F B fresh z hlen hF hB hs => encode_vac hp F B fresh z hlen hF hB hs)
    hp F B B' s t hB hB' h

/-- Both directions deliberately share the same left-to-right context. -/
def EqUnder (h p q : V) : Prop :=
  CProv (wim h (wim p q)) ∧ CProv (wim h (wim q p))

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)

lemma eqUnder_refl (h p : V) : EqUnder h p p := by
  have hp : CProv (wim h (wim p p)) :=
    cProv_mp (cProv_k (wim p p) h) (Kalmar.self_imp cProv_classical p)
  exact ⟨hp,hp⟩

lemma contra_under {h p q : V} (hpq : CProv (wim h (wim p q))) :
    CProv (wim h (wim (ValidatorQuantifierCore254.neg q) (ValidatorQuantifierCore254.neg p))) :=
  ValidatorImplicationContext.contra_under CProv cProv_classical hpq

lemma eqUnder_neg {h p q : V} (he : EqUnder h p q) : EqUnder h (ValidatorQuantifierCore254.neg p) (ValidatorQuantifierCore254.neg q) :=
  ⟨contra_under he.2,contra_under he.1⟩

lemma imp_under {h p p' q q' : V}
    (hp : CProv (wim h (wim p' p))) (hq : CProv (wim h (wim q q'))) :
    CProv (wim h (wim (wim p q) (wim p' q'))) :=
  ValidatorImplicationContext.imp_under CProv cProv_classical hp hq

lemma eqUnder_imp {h p p' q q' : V} (hp : EqUnder h p p') (hq : EqUnder h q q') :
    EqUnder h (wim p q) (wim p' q') :=
  ⟨imp_under hp.2 hq.1,imp_under hp.1 hq.2⟩

lemma eqUnder_conj {h p p' q q' : V} (hp : EqUnder h p p') (hq : EqUnder h q q') :
    EqUnder h (conj p q) (conj p' q') :=
  eqUnder_neg (eqUnder_imp hp (eqUnder_neg hq))

lemma reverse_eq_premise {h r x y : V}
    (hr : CProv (wim h (wim (weq x y) r))) :
    CProv (wim h (wim (weq y x) r)) :=
  ded2 (.mp (.mp (.ax hr) h1) (.mp (.ax (eq_symm y x)) h0))

/-- Reverse transport changes the equality premise by its finite symmetry
proof; it never silently swaps the old stack context. -/
lemma eqUnder_all_of_cons (B B' p q x y : V)
    (hb : EqUnder (eqContext (x∷B) (y∷B')) p q)
    (vxh : Vac x (eqContext B B')) (vyh : Vac y (eqContext B B'))
    (vxq : Vac x q) (vyp : Vac y p) :
    EqUnder (eqContext B B') (wal x p) (wal y q) := by
  constructor
  · exact all_of_cons B B' p q x y hb.1 vxh vxq vyh (vac_all x vyp)
  · exact all_relational (eqContext B B') q p y x
      (reverse_eq_premise (discharge_cons B B' x y hb.2))
      vyh vyp vxh (vac_all y vxq)

lemma eqUnder_ex_of_cons (B B' p q x y : V)
    (hb : EqUnder (eqContext (x∷B) (y∷B')) p q)
    (vxh : Vac x (eqContext B B')) (vyh : Vac y (eqContext B B'))
    (vxq : Vac x q) (vyp : Vac y p) :
    EqUnder (eqContext B B') (ex x p) (ex y q) :=
  eqUnder_neg (eqUnder_all_of_cons B B' (ValidatorQuantifierCore254.neg p) (ValidatorQuantifierCore254.neg q) x y
    (eqUnder_neg hb) vxh vyh (vac_neg vxq) (vac_neg vyp))

lemma term_eq_under {n u : V} (hu : IsSemiterm ℒₛₑₜ n u)
    (F B B' : V) (hB : len B=n) :
    CProv (wim (eqContext B B') (weq (TermLabels.term F B u) (TermLabels.term F B' u))) :=
  ValidatorLabelAvoidance.term_labels_related
    (P := fun x y => CProv (wim (eqContext B B') (weq x y))) hu F B B' hB
    (fun i hi => eqContext_projection B B' i hi)
    (fun x => cProv_mp (cProv_k (weq x x) (eqContext B B')) (eq_refl x))

lemma atom_eq_under {n arity R terms : V} (hr : (ℒₛₑₜ).IsRel arity R)
    (ht : IsSemitermVec ℒₛₑₜ arity n terms) (F B B' s t : V) (hB : len B=n) :
    EqUnder (eqContext B B') (Formulas.atom ?[F,B,s] arity R terms)
      (Formulas.atom ?[F,B',t] arity R terms) := by
  have harity : arity=2 := ValidatorLabelAvoidance.set_relation_arity hr
  subst arity
  have coord (i : V) (hi : i<2) : CProv (wim (eqContext B B')
      (weq (TermLabels.vec F B 2 terms).[i] (TermLabels.vec F B' 2 terms).[i])) := by
    rw [TermLabels.vec_nth F B ht.isUTerm hi,TermLabels.vec_nth F B' ht.isUTerm hi]
    exact term_eq_under (ht.nth hi) F B B' hB
  have hleft := coord 0 (by simp)
  have hright := coord 1 (by simp)
  have hleft' := compose hleft (eq_symm _ _)
  have hright' := compose hright (eq_symm _ _)
  classical
  simp only [Formulas.atom,nth_adjoin_zero,nth_adjoin_one]
  by_cases hz : R=0
  · simp only [hz,if_pos]
    constructor
    · exact ded2 (.mp (.mp (.mp (.ax (eq_congr _ _ _ _))
        (.mp (.ax hleft) h1)) (.mp (.ax hright) h1)) h0)
    · exact ded2 (.mp (.mp (.mp (.ax (eq_congr _ _ _ _))
        (.mp (.ax hleft') h1)) (.mp (.ax hright') h1)) h0)
  · simp only [hz,if_neg]
    constructor
    · exact ded2 (.mp (.mp (.mp (.ax (rel_congr _ _ _ _))
        (.mp (.ax hleft) h1)) (.mp (.ax hright) h1)) h0)
    · exact ded2 (.mp (.mp (.mp (.ax (rel_congr _ _ _ _))
        (.mp (.ax hleft') h1)) (.mp (.ax hright') h1)) h0)

/-- The paired universal/existential step for the eventual formula induction. -/
lemma encoded_binder_steps [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ (n+1) p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t)
    (ih : EqUnder (eqContext (s∷B) (t∷B'))
      (encode F (s∷B) (s+2) p) (encode F (t∷B') (t+2) p)) :
    EqUnder (eqContext B B') (encode F B s (^∀ p)) (encode F B' t (^∀ p)) ∧
    EqUnder (eqContext B B') (encode F B s (^∃ p)) (encode F B' t (^∃ p)) := by
  have hv := cross_body_vac hp F B B' s t hB hB' hf
  rcases hf with ⟨_,_,hsB,hsB',htB,htB',_⟩
  have vs : Vac s (eqContext B B') := eqContext_vac B B' s (hB.trans hB'.symm)
    (by simpa using hsB 0) (by simpa using hsB' 0)
  have vt : Vac t (eqContext B B') := eqContext_vac B B' t (hB.trans hB'.symm)
    (by simpa using htB 0) (by simpa using htB' 0)
  constructor
  · rw [encode_all F B s hp.isUFormula,encode_all F B' t hp.isUFormula]
    exact eqUnder_all_of_cons B B' _ _ s t ih vs vt hv.1 hv.2
  · rw [encode_exs F B s hp.isUFormula,encode_exs F B' t hp.isUFormula]
    exact eqUnder_ex_of_cons B B' _ _ s t ih vs vt hv.1 hv.2

/-! With the free environment `F` fixed outside the induction, the
proof-existence invariant is Sigma-one: the freshness premise is Pi-one and
the conclusion is Sigma-one. The two stacks and streams grow, but every
recursive call stays below an explicit represented bound, so bounded-parameter
order induction in IΣ₁ applies. These graph interfaces keep hierarchy closure
independent of the implementation of numeric syntax. -/
private instance len_delta : 𝚫₁-Function₁[V] (len : V→V) :=
  len_defined.graph_delta.to_definable
private instance avoid_delta : 𝚫₁-Relation[V] Avoid := by unfold Avoid; definability
private instance free_delta : 𝚫₁-Relation[V] FreeAvoid := by unfold FreeAvoid; definability
private instance streamEnv_pi1 : 𝚷₁-Relation[V] StreamEnv := by unfold StreamEnv; definability
private instance streamFree_pi1 : 𝚷₁-Relation[V] StreamFree := by unfold StreamFree; definability
private instance apart_pi1 : 𝚷₁-Relation[V] Apart := by unfold Apart; definability
private instance freshPair_pi1 : 𝚷₁-Relation₅[V] FreshPair := by unfold FreshPair; definability
private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
private instance eqUnder_sigma1 : 𝚺₁-Relation₃[V] EqUnder := by
  unfold EqUnder
  definability

/-- The bounded-parameter invariant over the packed stack/stream pairs
`y = ⟪B,s⟫` and `z = ⟪B',t⟫`, with `F` fixed. -/
private lemma alpha_invariant_sigma1 (F : V) : 𝚺₁-Relation₃[V]
    (fun p y z => IsSemiformula ℒₛₑₜ (len (π₁ y)) p → len (π₁ z)=len (π₁ y) →
      FreshPair F (π₁ y) (π₁ z) (π₂ y) (π₂ z) →
      EqUnder (eqContext (π₁ y) (π₁ z)) (encode F (π₁ y) (π₂ y) p)
        (encode F (π₁ z) (π₂ z) p)) := by
  definability

/-- All-internal alpha transport, in both directions under the same represented
stack-equality context. The future-stream invariant is an explicit premise. Each
recursive call uses stacks/streams bounded by `⟪s∷B,s+2⟫` and `⟪t∷B',t+2⟫`,
so the induction is bounded-parameter order induction in IΣ₁. The binder
step and public theorem retain their IΣ₂ assumptions. -/
theorem encode_eq_under [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    EqUnder (eqContext B B') (encode F B s p) (encode F B' t p) := by
  have main : ∀ p y z : V, IsSemiformula ℒₛₑₜ (len (π₁ y)) p → len (π₁ z)=len (π₁ y) →
      FreshPair F (π₁ y) (π₁ z) (π₂ y) (π₂ z) →
      EqUnder (eqContext (π₁ y) (π₁ z)) (encode F (π₁ y) (π₂ y) p)
        (encode F (π₁ z) (π₂ z) p) := by
    refine bounded_all_sigma1_order_induction₂
      (fy := fun _ y _ => ⟪π₂ y ∷ π₁ y, π₂ y+2⟫)
      (fz := fun _ _ z => ⟪π₂ z ∷ π₁ z, π₂ z+2⟫)
      (by definability) (by definability) (alpha_invariant_sigma1 F) ?_
    intro p y z ih htyped hB' hf
    have hy : ⟪π₁ y, π₂ y⟫ ≤ ⟪π₂ y ∷ π₁ y, π₂ y+2⟫ :=
      pair_le_pair (le_of_lt (lt_adjoin' _ _)) (le_add_of_nonneg_right (Arithmetic.zero_le _))
    have hz : ⟪π₁ z, π₂ z⟫ ≤ ⟪π₂ z ∷ π₁ z, π₂ z+2⟫ :=
      pair_le_pair (le_of_lt (lt_adjoin' _ _)) (le_add_of_nonneg_right (Arithmetic.zero_le _))
    rw [pair_unpair] at hy hz
    have ih0 : ∀ q < p, IsSemiformula ℒₛₑₜ (len (π₁ y)) q →
        EqUnder (eqContext (π₁ y) (π₁ z)) (encode F (π₁ y) (π₂ y) q)
          (encode F (π₁ z) (π₂ z) q) := fun q hq hq' => ih q hq y hy z hz hq' hB' hf
    have ih1 : ∀ q < p, IsSemiformula ℒₛₑₜ (len (π₁ y)+1) q →
        EqUnder (eqContext (π₂ y ∷ π₁ y) (π₂ z ∷ π₁ z))
          (encode F (π₂ y ∷ π₁ y) (π₂ y+2) q) (encode F (π₂ z ∷ π₁ z) (π₂ z+2) q) := by
      intro q hq hq'
      simpa using ih q hq _ le_rfl _ le_rfl (by simpa using hq')
        (by simp [hB']) (by simpa using freshPair_next hf)
    clear ih hy hz
    generalize π₁ y = B at *
    generalize π₂ y = s at *
    generalize π₁ z = B' at *
    generalize π₂ z = t at *
    rcases IsSemiformula.case_iff.mp htyped with
      (⟨arity,R,terms,hr,ht,rfl⟩ | ⟨arity,R,terms,hr,ht,rfl⟩ | rfl | rfl |
        ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
    · rw [encode_rel F B s hr ht.isUTerm,encode_rel F B' t hr ht.isUTerm]
      exact atom_eq_under hr ht F B B' s t rfl
    · rw [encode_nrel F B s hr ht.isUTerm,encode_nrel F B' t hr ht.isUTerm]
      exact eqUnder_neg (atom_eq_under hr ht F B B' s t rfl)
    · simpa using eqUnder_refl (eqContext B B') (0 : V)
    · simpa using eqUnder_refl (eqContext B B') (1 : V)
    · rw [encode_and F B s hp.isUFormula hq.isUFormula,
        encode_and F B' t hp.isUFormula hq.isUFormula]
      exact eqUnder_conj (ih0 p (by simp) hp) (ih0 q (by simp) hq)
    · rw [encode_or F B s hp.isUFormula hq.isUFormula,
        encode_or F B' t hp.isUFormula hq.isUFormula]
      exact eqUnder_imp (eqUnder_neg (ih0 p (by simp) hp)) (ih0 q (by simp) hq)
    · exact (encoded_binder_steps hp F B B' s t rfl hB' hf (ih1 p (by simp) hp)).1
    · exact (encoded_binder_steps hp F B B' s t rfl hB' hf (ih1 p (by simp) hp)).2
  subst hB
  simpa using main p ⟪B,s⟫ ⟪B',t⟫ (by simpa using hp) (by simpa using hB')
    (by simpa using hf)

/-- At empty bound stacks the equality context is truth. Stream selection and
any comparison to the fixed formulaEncoder remain separate clients. -/
lemma encode_formula_alpha [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F s t : V) (hs : StreamFree s F) (ht : StreamFree t F) (hap : Apart s t) :
    CProv (wim (encode F 0 s p) (encode F 0 t p)) ∧
    CProv (wim (encode F 0 t p) (encode F 0 s p)) := by
  have hf : FreshPair F 0 0 s t :=
    ⟨hs,ht,(fun k => avoid_nil (s+2*k)),(fun k => avoid_nil (s+2*k)),
      (fun k => avoid_nil (t+2*k)),(fun k => avoid_nil (t+2*k)),hap⟩
  have he := encode_eq_under hp F 0 0 s t (by simp) (by simp) hf
  have hc : CProv (eqContext (0 : V) 0) := by simpa using (cProv_truth (V := V))
  exact ⟨cProv_mp he.1 hc,cProv_mp he.2 hc⟩

end LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254
