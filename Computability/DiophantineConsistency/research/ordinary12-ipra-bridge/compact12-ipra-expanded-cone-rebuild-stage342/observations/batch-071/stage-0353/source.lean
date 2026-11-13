import ZFCinPA.ValidatorLabelAvoidance
import ZFCinPA.ValidatorAtomicTransport222

import ZFCinPA.ValidatorImplicationContext

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Uniform all-internal alpha conversion for the actual C222 encoder.
The fixed Eind context is preserved in both directions. Future binder
streams explicitly avoid both stacks, all free labels including fallback1,
and each other. With the free environment fixed, the represented
proof-existence invariant is Σ1 with bounded growing parameters, so the
uniform theorem uses only IΣ₁. No old C254 proof, source substitution,
arbitrary proof translation or semantic seed validity is assumed. -/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open ValidatorEindContext222 ValidatorAtomicTransport222
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
lemma cross_body_vac {n p : V}
    (hp : IsSemiformula ℒₛₑₜ (n+1) p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (h : FreshPair F B B' s t) :
    Vac s (encode F (t∷B') (t+2) p) ∧
    Vac t (encode F (s∷B) (s+2) p) :=
  ValidatorLabelAvoidance.cross_body_vac (P := Vac) (enc := encode)
    (fun hp F B fresh z hlen hF hB hs => encode_vac hp F B fresh z hlen hF hB hs)
    hp F B B' s t hB hB' h

lemma contra_under {h p q : V} (hpq : CProv (wim h (wim p q))) :
    CProv (wim h (wim (ValidatorRelationalCore222.neg q) (ValidatorRelationalCore222.neg p))) :=
  ValidatorImplicationContext.contra_under CProv cProv_classical hpq

lemma eqUnder_neg {h p q : V} (he : EqUnder h p q) : EqUnder h (ValidatorRelationalCore222.neg p) (ValidatorRelationalCore222.neg q) :=
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

/-- Reverse ALL keeps the same old context and precomposes the explicit
weq(y,x)→Eind(y,x)→Eind(x,y) chain before the reverse body certificate. -/
lemma eqUnder_all_of_cons (B B' p q x y : V)
    (hb : EqUnder (eindContext (x∷B) (y∷B')) p q)
    (vxh : Vac x (eindContext B B')) (vyh : Vac y (eindContext B B'))
    (vxq : Vac x q) (vyp : Vac y p) :
    EqUnder (eindContext B B') (wal x p) (wal y q) := by
  constructor
  · exact all_of_cons B B' p q x y hb.1 vxh vxq vyh (vac_all x vyp)
  · exact all_relational (eindContext B B') q p y x
      (reverse_primitive_premise (discharge_cons B B' x y hb.2))
      vyh vyp vxh (vac_all y vxq)

lemma eqUnder_ex_of_cons (B B' p q x y : V)
    (hb : EqUnder (eindContext (x∷B) (y∷B')) p q)
    (vxh : Vac x (eindContext B B')) (vyh : Vac y (eindContext B B'))
    (vxq : Vac x q) (vyp : Vac y p) :
    EqUnder (eindContext B B') (ex x p) (ex y q) :=
  eqUnder_neg (eqUnder_all_of_cons B B' (ValidatorRelationalCore222.neg p) (ValidatorRelationalCore222.neg q) x y
    (eqUnder_neg hb) vxh vyh (vac_neg vxq) (vac_neg vyp))

/-- The paired universal/existential step for the eventual formula induction. -/
lemma encoded_binder_steps {n p : V}
    (hp : IsSemiformula ℒₛₑₜ (n+1) p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t)
    (ih : EqUnder (eindContext (s∷B) (t∷B'))
      (encode F (s∷B) (s+2) p) (encode F (t∷B') (t+2) p)) :
    EqUnder (eindContext B B') (encode F B s (^∀ p)) (encode F B' t (^∀ p)) ∧
    EqUnder (eindContext B B') (encode F B s (^∃ p)) (encode F B' t (^∃ p)) := by
  have hv := cross_body_vac hp F B B' s t hB hB' hf
  rcases hf with ⟨_,_,hsB,hsB',htB,htB',_⟩
  have vs : Vac s (eindContext B B') := eindContext_vac B B' s (hB.trans hB'.symm)
    (by simpa using hsB 0) (by simpa using hsB' 0)
  have vt : Vac t (eindContext B B') := eindContext_vac B B' t (hB.trans hB'.symm)
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
      EqUnder (eindContext (π₁ y) (π₁ z)) (encode F (π₁ y) (π₂ y) p)
        (encode F (π₁ z) (π₂ z) p)) := by
  definability

/-- All-internal alpha transport, in both directions under the same represented
Eind stack context. The future-stream invariant is an explicit premise. Each
recursive call uses stacks/streams bounded by `⟪s∷B,s+2⟫` and `⟪t∷B',t+2⟫`,
so the induction is bounded-parameter order induction in IΣ₁. -/
theorem encode_eq_under {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    EqUnder (eindContext B B') (encode F B s p) (encode F B' t p) := by
  have main : ∀ p y z : V, IsSemiformula ℒₛₑₜ (len (π₁ y)) p → len (π₁ z)=len (π₁ y) →
      FreshPair F (π₁ y) (π₁ z) (π₂ y) (π₂ z) →
      EqUnder (eindContext (π₁ y) (π₁ z)) (encode F (π₁ y) (π₂ y) p)
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
        EqUnder (eindContext (π₁ y) (π₁ z)) (encode F (π₁ y) (π₂ y) q)
          (encode F (π₁ z) (π₂ z) q) := fun q hq hq' => ih q hq y hy z hz hq' hB' hf
    have ih1 : ∀ q < p, IsSemiformula ℒₛₑₜ (len (π₁ y)+1) q →
        EqUnder (eindContext (π₂ y ∷ π₁ y) (π₂ z ∷ π₁ z))
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
    · simpa using eqUnder_refl (eindContext B B') (0 : V)
    · simpa using eqUnder_refl (eindContext B B') (1 : V)
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

/-- At empty bound stacks the Eind context is truth. Stream selection and
any comparison to the fixed formulaEncoder remain separate clients. -/
lemma encode_formula_alpha {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F s t : V) (hs : StreamFree s F) (ht : StreamFree t F) (hap : Apart s t) :
    CProv (wim (encode F 0 s p) (encode F 0 t p)) ∧
    CProv (wim (encode F 0 t p) (encode F 0 s p)) := by
  have hf : FreshPair F 0 0 s t :=
    ⟨hs,ht,(fun k => avoid_nil (s+2*k)),(fun k => avoid_nil (s+2*k)),
      (fun k => avoid_nil (t+2*k)),(fun k => avoid_nil (t+2*k)),hap⟩
  have he := encode_eq_under hp F 0 0 s t (by simp) (by simp) hf
  have hc : CProv (eindContext (0 : V) 0) := by simpa using (cProv_truth (V := V))
  exact ⟨cProv_mp he.1 hc,cProv_mp he.2 hc⟩

/-- Malformed source codes use the separate output-zero branch; no typing
or freshness is claimed for source0. -/
lemma encode_malformed_eq_under (h F B B' s t : V) {p : V}
    (hp : ¬IsUFormula ℒₛₑₜ p) :
    EqUnder h (encode F B s p) (encode F B' t p) := by
  rw [encode_of_not_formula F B s hp,encode_of_not_formula F B' t hp]
  exact eqUnder_refl h 0

/-- Both directions have actual internal numeric proof codes accepted by
History222; neither the source nor the witness is assumed standard Nat. -/
theorem encode_alpha_witnesses {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    (∃ code : V, ArithmeticHistory222.value code =
      wim (eindContext B B') (wim (encode F B s p) (encode F B' t p))+1) ∧
    (∃ code : V, ArithmeticHistory222.value code =
      wim (eindContext B B') (wim (encode F B' t p) (encode F B s p))+1) :=
  encode_eq_under hp F B B' s t hB hB' hf

end LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha222
