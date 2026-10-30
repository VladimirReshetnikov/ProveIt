import ZFCinPA.ValidatorLabelAvoidance
import ZFCinPA.ValidatorEindContext222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Finite atomic transport for the actual C222 Eind-aware encoder.
All formula labels, source terms and environment entries are internal.
No primitive-equality vacuity, inverse Eind-to-weq, or semantic equality
identification is used. This is the IΣ1 atomic checkpoint; uniform source
formula alpha conversion and its IΣ2 invariant remain separate. -/
namespace LeanProofs.ZFCinPA.ValidatorAtomicTransport222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorFormulaEncoder222 ValidatorEindContext222
open ValidatorEnvironmentLabels254 (freeLabel)
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "h2" => (ValidatorImplicationContext.h2 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)
local notation "ded3" => (ValidatorImplicationContext.ded3 CProv cProv_classical)

lemma eind_refl (a : V) : CProv (Eind a a) :=
  cProv_mp (Eq_Eind a a) (ValidatorEqualityCore222.cProv_refl a)

lemma eind_symm (a b : V) : CProv (wim (Eind a b) (Eind b a)) :=
  ded1 (.mp (.mp (.ax (Eind_euclid b a a)) h0) (.ax (eind_refl a)))

lemma eind_trans (a b c : V) :
    CProv (wim (Eind a b) (wim (Eind b c) (Eind a c))) :=
  ded2 (.mp (.mp (.ax (Eind_euclid a c b)) (.mp (.ax (eind_symm a b)) h1)) h0)

/-- No restrictions on the four labels or on their internal auxiliary codes. -/
lemma eind_congr (a a' b b' : V) :
    CProv (wim (Eind a a') (wim (Eind b b') (wim (Eind a b) (Eind a' b')))) := by
  apply ded3
  have ha : D [Eind a b,Eind b b',Eind a a'] (Eind a' a) :=
    .mp (.ax (eind_symm a a')) h2
  have hab : D [Eind a b,Eind b b',Eind a a'] (Eind a' b) :=
    .mp (.mp (.ax (eind_trans a' a b)) ha) h0
  exact .mp (.mp (.ax (eind_trans a' b b')) hab) h1

lemma rel_congr (a a' b b' : V) :
    CProv (wim (Eind a a') (wim (Eind b b') (wim (wel a b) (wel a' b')))) :=
  ded3 (.mp (.mp (.ax (Eind_el_r b b' a')) h1)
    (.mp (.mp (.ax (Eind_el_l a' b a)) h2) h0))

/-- Both implications retain precisely the same outer context. -/
def EqUnder (h p q : V) : Prop :=
  CProv (wim h (wim p q)) ∧ CProv (wim h (wim q p))

lemma eqUnder_refl (h p : V) : EqUnder h p p := by
  have hp : CProv (wim h (wim p p)) :=
    cProv_mp (cProv_k (wim p p) h) (Kalmar.self_imp cProv_classical p)
  exact ⟨hp,hp⟩

/-- Reverse the relation premise, not the old environment context. -/
lemma reverse_eind_premise {h r x y : V}
    (hr : CProv (wim h (wim (Eind x y) r))) :
    CProv (wim h (wim (Eind y x) r)) :=
  ded2 (.mp (.mp (.ax hr) h1) (.mp (.ax (eind_symm y x)) h0))

/-- The chain is weq(y,x)→Eind(y,x)→Eind(x,y), followed by the original
body certificate under h. No converse equality identification is asserted. -/
lemma reverse_primitive_premise {h r x y : V}
    (hr : CProv (wim h (wim (Eind x y) r))) :
    CProv (wim h (wim (weq y x) r)) :=
  ValidatorEindContext222.primitive_premise (reverse_eind_premise hr)

/-- Typed set-language terms are bound/free variables only. The right
stack lookup is total; its length is not needed for this finite projection. -/
lemma term_eind_under {n u : V} (hu : IsSemiterm ℒₛₑₜ n u)
    (F B B' : V) (hB : len B=n) :
    CProv (wim (eindContext B B')
      (Eind (ValidatorEnvironmentLabels254.TermLabels.term F B u)
        (ValidatorEnvironmentLabels254.TermLabels.term F B' u))) :=
  ValidatorLabelAvoidance.term_labels_related
    (P := fun x y => CProv (wim (eindContext B B') (Eind x y))) hu F B B' hB
    (fun i hi => eindContext_projection B B' i hi)
    (fun x => cProv_mp (cProv_k (Eind x x) (eindContext B B')) (eind_refl x))

/-- Actual equality atoms use Eind, membership atoms use wel. The typing
guard forces both argument accesses to lie within an arity-two vector. -/
lemma atom_eq_under {n arity R terms : V} (hr : (ℒₛₑₜ).IsRel arity R)
    (ht : IsSemitermVec ℒₛₑₜ arity n terms) (F B B' s t : V) (hB : len B=n) :
    EqUnder (eindContext B B') (atom ?[F,B,s] arity R terms)
      (atom ?[F,B',t] arity R terms) := by
  have harity : arity=2 := ValidatorLabelAvoidance.set_relation_arity hr
  subst arity
  have coord (i : V) (hi : i<2) : CProv (wim (eindContext B B')
      (Eind (ValidatorEnvironmentLabels254.TermLabels.vec F B 2 terms).[i]
        (ValidatorEnvironmentLabels254.TermLabels.vec F B' 2 terms).[i])) := by
    rw [ValidatorEnvironmentLabels254.TermLabels.vec_nth F B ht.isUTerm hi,
      ValidatorEnvironmentLabels254.TermLabels.vec_nth F B' ht.isUTerm hi]
    exact term_eind_under (ht.nth hi) F B B' hB
  have hleft := coord 0 (by simp)
  have hright := coord 1 (by simp)
  have hleft' := compose hleft (eind_symm _ _)
  have hright' := compose hright (eind_symm _ _)
  classical
  simp only [atom,nth_adjoin_zero,nth_adjoin_one]
  by_cases hz : R=0
  · simp only [hz,if_pos]
    constructor
    · exact ded2 (.mp (.mp (.mp (.ax (eind_congr _ _ _ _))
        (.mp (.ax hleft) h1)) (.mp (.ax hright) h1)) h0)
    · exact ded2 (.mp (.mp (.mp (.ax (eind_congr _ _ _ _))
        (.mp (.ax hleft') h1)) (.mp (.ax hright') h1)) h0)
  · simp only [hz]
    constructor
    · exact ded2 (.mp (.mp (.mp (.ax (rel_congr _ _ _ _))
        (.mp (.ax hleft) h1)) (.mp (.ax hright) h1)) h0)
    · exact ded2 (.mp (.mp (.mp (.ax (rel_congr _ _ _ _))
        (.mp (.ax hleft') h1)) (.mp (.ax hright') h1)) h0)

/-- Expose an actual internal checker witness for the forward atomic map. -/
lemma atom_forward_witness {n arity R terms : V} (hr : (ℒₛₑₜ).IsRel arity R)
    (ht : IsSemitermVec ℒₛₑₜ arity n terms) (F B B' s t : V) (hB : len B=n) :
    ∃ code : V, ArithmeticHistory222.value code =
      wim (eindContext B B')
        (wim (atom ?[F,B,s] arity R terms) (atom ?[F,B',t] arity R terms))+1 :=
  (atom_eq_under hr ht F B B' s t hB).1

end LeanProofs.ZFCinPA.ValidatorAtomicTransport222
