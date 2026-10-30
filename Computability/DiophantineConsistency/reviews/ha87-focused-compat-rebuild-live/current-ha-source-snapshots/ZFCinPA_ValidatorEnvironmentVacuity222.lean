import ZFCinPA.ValidatorLabelAvoidance
import ZFCinPA.ValidatorFormulaEncoder222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Uniform represented vacuity for the actual C222 Eind-aware encoder.
The syntax-only environment conventions and the represented induction
pattern follow the existing configurable encoder. The atom proof is new:
it uses actual C222 Eind_vac and membership vacuity, never primitive equality
vacuity. Typed terms, exact bound-stack length, free fallback1 and the whole
future binder stream are explicit. No positivity, pairwise distinctness,
self-vacuity, seed truth or arbitrary Lean-predicate induction is assumed.
The uniform result uses bounded-parameter order induction in IΣ₁. -/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorEnvironmentLabels254 (freeLabel)
open ValidatorFormulaEncoder222 ValidatorRelationalCore222 ValidatorProvability222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Avoid every stored label; all indices and the vector length are internal. -/
def Avoid (z env : V) : Prop := ∀ i<len env, z≠env.[i]
/-- The finite free vector has the additional fallback label 1. -/
def FreeAvoid (z env : V) : Prop := z≠1 ∧ Avoid z env
/-- Avoid all labels that the encoder may allocate below a binder. -/
def StreamAvoid (z fresh : V) : Prop := ∀ k : V, z≠fresh+2*k

lemma avoid_nil (z : V) : Avoid z (0 : V) := ValidatorLabelAvoidance.avoid_nil z
lemma avoid_cons {z env x : V} (he : Avoid z env) (hx : z≠x) : Avoid z (x∷env) :=
  ValidatorLabelAvoidance.avoid_cons he hx
lemma free_label_avoids {z env : V} (he : FreeAvoid z env) (i : V) :
    z≠freeLabel env i := ValidatorLabelAvoidance.free_label_avoids he i
lemma stream_head {z fresh : V} (h : StreamAvoid z fresh) : z≠fresh :=
  ValidatorLabelAvoidance.stream_head h
lemma stream_next {z fresh : V} (h : StreamAvoid z fresh) : StreamAvoid z (fresh+2) :=
  ValidatorLabelAvoidance.stream_next h
lemma stream_of_lt {z fresh : V} (h : z<fresh) : StreamAvoid z fresh :=
  ValidatorLabelAvoidance.stream_of_lt h

lemma term_label_avoids {n t : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (F B z : V) (hlen : len B=n) (hF : FreeAvoid z F) (hB : Avoid z B) :
    z≠ValidatorEnvironmentLabels254.TermLabels.term F B t :=
  ValidatorLabelAvoidance.term_label_avoids ht F B z hlen hF hB

lemma atom_vac {n arity R terms : V} (hr : (ℒₛₑₜ).IsRel arity R)
    (ht : IsSemitermVec ℒₛₑₜ arity n terms)
    (F B fresh z : V) (hlen : len B=n) (hF : FreeAvoid z F) (hB : Avoid z B) :
    Vac z (atom ?[F,B,fresh] arity R terms) := by
  have harity : arity=2 := ValidatorLabelAvoidance.set_relation_arity hr
  subst arity
  have hlabel (i : V) (hi : i<2) :
      z≠(ValidatorEnvironmentLabels254.TermLabels.vec F B 2 terms).[i] := by
    rw [ValidatorEnvironmentLabels254.TermLabels.vec_nth F B ht.isUTerm hi]
    exact term_label_avoids (ht.nth hi) F B z hlen hF hB
  classical
  simp only [atom,nth_adjoin_zero,nth_adjoin_one]
  split
  · exact ValidatorEind222.Eind_vac _ _ z (hlabel 0 (by simp)) (hlabel 1 (by simp))
  · exact vac_rel _ _ z (hlabel 0 (by simp)) (hlabel 1 (by simp))

/-! The invariant is Sigma-one once the free environment and the target label
are fixed outside the induction: the binder stack and the fresh-label stream
grow, but every recursive call's values are bounded by an explicit represented
function, so bounded-parameter order induction in IΣ₁ applies. -/
private instance len_delta : 𝚫₁-Function₁[V] (len : V→V) :=
  len_defined.graph_delta.to_definable
private instance avoid_delta : 𝚫₁-Relation[V] Avoid := by unfold Avoid; definability
private instance stream_pi1 : 𝚷₁-Relation[V] StreamAvoid := by unfold StreamAvoid; definability
private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
private instance wal_sigma1 : 𝚺₁-Function₂[V] wal := wal_defined.to_definable₀
private instance vac_sigma1 : 𝚺₁-Relation[V] Vac := by
  unfold Vac
  definability

/-- The bounded-parameter invariant, with the free environment `F` and the
target label `z` held fixed. -/
private lemma vac_invariant_sigma1 (F z : V) : 𝚺₁-Relation₃[V]
    (fun p B fresh => IsSemiformula ℒₛₑₜ (len B) p → Avoid z B →
      StreamAvoid z fresh → Vac z (encode F B fresh p)) := by
  definability

/-- Uniform vacuity for every internal encoded formula. The binder stack and
fresh-label stream vary through the recursion, but every recursive call uses
values bounded by `fresh ∷ B` and `fresh+2`, so bounded-parameter order
induction in IΣ₁ suffices. -/
theorem encode_vac {n p : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (F B fresh z : V) (hlen : len B=n) (hF : FreeAvoid z F)
    (hB : Avoid z B) (hs : StreamAvoid z fresh) : Vac z (encode F B fresh p) := by
  have main : ∀ p B fresh : V, IsSemiformula ℒₛₑₜ (len B) p → Avoid z B →
      StreamAvoid z fresh → Vac z (encode F B fresh p) := by
    refine bounded_all_sigma1_order_induction₂
      (fy := fun _ B fresh => fresh ∷ B) (fz := fun _ _ fresh => fresh+2)
      (by definability) (by definability) (vac_invariant_sigma1 F z) ?_
    intro p B fresh ih htyped hB hs
    have hB' : B ≤ fresh ∷ B := le_of_lt (lt_adjoin' _ _)
    have hf' : fresh ≤ fresh+2 := le_add_of_nonneg_right (Arithmetic.zero_le _)
    rcases IsSemiformula.case_iff.mp htyped with
      (⟨arity,R,terms,hr,ht,rfl⟩ | ⟨arity,R,terms,hr,ht,rfl⟩ | rfl | rfl |
        ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
    · rw [encode_rel F B fresh hr ht.isUTerm]
      exact atom_vac hr ht F B fresh z rfl hF hB
    · rw [encode_nrel F B fresh hr ht.isUTerm]
      exact vac_neg (atom_vac hr ht F B fresh z rfl hF hB)
    · simpa using vac_truth z
    · simpa using vac_falsum z
    · rw [encode_and F B fresh hp.isUFormula hq.isUFormula]
      exact vac_neg (vac_imp (ih p (by simp) B hB' fresh hf' hp hB hs)
        (vac_neg (ih q (by simp) B hB' fresh hf' hq hB hs)))
    · rw [encode_or F B fresh hp.isUFormula hq.isUFormula]
      exact vac_imp (vac_neg (ih p (by simp) B hB' fresh hf' hp hB hs))
        (ih q (by simp) B hB' fresh hf' hq hB hs)
    · rw [encode_all F B fresh hp.isUFormula]
      exact vac_all fresh (ih p (by simp) (fresh∷B) le_rfl (fresh+2) le_rfl
        (by simpa using hp) (avoid_cons hB (stream_head hs)) (stream_next hs))
    · rw [encode_exs F B fresh hp.isUFormula]
      exact vac_neg (vac_all fresh (vac_neg
        (ih p (by simp) (fresh∷B) le_rfl (fresh+2) le_rfl
          (by simpa using hp) (avoid_cons hB (stream_head hs)) (stream_next hs))))
  subst hlen
  exact main p B fresh hp hB hs

/-- Closed-bound-context client, with the same explicit free/binder avoidance. -/
lemma encode_formula_vac {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F fresh z : V) (hF : FreeAvoid z F) (hs : StreamAvoid z fresh) :
    Vac z (encode F 0 fresh p) :=
  encode_vac hp F 0 fresh z (by simp) hF (avoid_nil z) hs

/-- The same result exposes a numeric proof accepted by the actual represented
C222 history, uniformly over every internal well-typed source formula. -/
theorem encode_vac_witness {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B fresh z : V) (hlen : len B=n)
    (hF : FreeAvoid z F) (hB : Avoid z B) (hs : StreamAvoid z fresh) :
    ∃ code : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value code =
      wim (encode F B fresh p) (wal z (encode F B fresh p)) + 1 :=
  encode_vac hp F B fresh z hlen hF hB hs

/-- Malformed sources use the separate fixed truth-output branch. This is
not a claim that source zero is a well-formed formula. -/
theorem encode_malformed_vac (F B fresh z : V) {p : V}
    (hp : ¬IsUFormula ℒₛₑₜ p) : Vac z (encode F B fresh p) := by
  rw [encode_of_not_formula F B fresh hp]
  exact vac_truth z

end LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity222
