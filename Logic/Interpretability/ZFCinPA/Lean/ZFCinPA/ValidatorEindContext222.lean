import ZFCinPA.ValidatorEnvironmentVacuity222
import ZFCinPA.ValidatorPrefixContext

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-!
A represented conjunction of coordinate indiscernibilities for internal bound stacks.
The prefix iterator prepends its newest Eind, so its conjunction order is
reversed. Finite propositional certificates give the ordinary head-cons law
up to CProv implications in both directions. All recursion and indices are
internal; no source-formula induction or accepted-proof renaming is assumed.
-/
namespace LeanProofs.ZFCinPA.ValidatorEindContext222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ValidatorProvability222 ValidatorRelationalCore222
open ValidatorEind222 ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open scoped LO.FirstOrder.Arithmetic

namespace Prefix

def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “out left right. out = 0”
  succ := .mkSigma “out previous time left right.
    ∃ a, !nthDef a left time ∧ ∃ b, !nthDef b right time ∧
    ∃ atom, !eindDef atom a b ∧ ∃ np, !wimDef np previous 1 ∧
    ∃ mid, !wimDef mid atom np ∧ !wimDef out mid 1”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def construction : PR.Construction V blueprint where
  zero _ := 0
  succ env time previous := conj (Eind (env 0).[time] (env 1).[time]) previous
  zero_defined := .mk fun e => by simp [blueprint]
  succ_defined := .mk fun e => by simp [blueprint,ValidatorRelationalCore222.conj,ValidatorRelationalCore222.neg]

end Prefix

/-- Graph argument order: output, prefix length, left stack, right stack. -/
def prefixContextDef : 𝚺₁.Semisentence 4 := Prefix.blueprint.resultDef

def eindContextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out left right. ∃ n, !lenDef n left ∧ !prefixContextDef out n left right”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def prefixContext (n B B' : V) : V :=
  Prefix.construction.result ![B,B'] n
noncomputable def eindContext (B B' : V) : V := prefixContext (len B) B B'

instance prefixContext_defined : 𝚺₁-Function₃[V] prefixContext via prefixContextDef :=
  .mk fun e => by
    have hparams : (fun i : Fin 2 => e i.succ.succ) = ![e 2,e 3] :=
      Matrix.fun_eq_vec_two (fun i : Fin 2 => e i.succ.succ)
    simpa [prefixContextDef,prefixContext,Matrix.comp_vecCons',Matrix.comp_vecCons'',hparams]
      using (Prefix.construction (V := V)).result_defined.defined e
instance prefixContext_delta : 𝚫₁-Function₃[V] prefixContext :=
  prefixContext_defined.graph_delta.to_definable
instance eindContext_defined : 𝚺₁-Function₂[V] eindContext via eindContextDef :=
  .mk fun e => by simp [eindContextDef,eindContext]
instance eindContext_delta : 𝚫₁-Function₂[V] eindContext :=
  eindContext_defined.graph_delta.to_definable

lemma eindContext_graph (out B B' : V) :
    V ⊧/![out,B,B'] eindContextDef.val ↔ out=eindContext B B' :=
  (eindContext_defined (V := V)).df ![out,B,B']
lemma eindContext_total_unique (B B' : V) :
    ∃! out : V, V ⊧/![out,B,B'] eindContextDef.val := by
  refine ⟨eindContext B B', (eindContext_graph _ _ _).mpr rfl, ?_⟩
  intro out h
  exact (eindContext_graph _ _ _).mp h

/- Use the fixed arithmetic graphs in induction predicates. The Defined
instances alone do not register general definability for these functions. -/
private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
private instance eind_sigma1 : 𝚺₁-Function₂[V] Eind := eind_defined.to_definable₀
private instance prefixContext_sigma1 : 𝚺₁-Function₃[V] prefixContext :=
  prefixContext_defined.to_definable
private instance conj_sigma1 : 𝚺₁-Function₂[V] conj := by
  unfold conj ValidatorRelationalCore222.neg
  definability

@[simp] lemma prefixContext_zero (B B' : V) : prefixContext 0 B B'=0 := by
  simp [prefixContext,Prefix.construction]
@[simp] lemma prefixContext_succ (n B B' : V) :
    prefixContext (n+1) B B'=conj (Eind B.[n] B'.[n]) (prefixContext n B B') := by
  simp [prefixContext,Prefix.construction]
@[simp] lemma eindContext_nil (B' : V) : eindContext (0 : V) B'=0 := by
  simp [eindContext]

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)

lemma conj_intro_imp (a b : V) : CProv (wim a (wim b (conj a b))) :=
  ValidatorPrefixContext.conj_intro_imp CProv cProv_classical a b
lemma conj_under {h a b : V} (ha : CProv (wim h a)) (hb : CProv (wim h b)) :
    CProv (wim h (conj a b)) :=
  ValidatorPrefixContext.conj_under CProv cProv_classical ha hb
lemma conj_mono_right (a : V) {b c : V} (h : CProv (wim b c)) :
    CProv (wim (conj a b) (conj a c)) :=
  ValidatorPrefixContext.conj_mono_right CProv cProv_classical a h
lemma conj_interchange (a b c : V) :
    CProv (wim (conj a (conj b c)) (conj b (conj a c))) :=
  ValidatorPrefixContext.conj_interchange CProv cProv_classical a b c

/-- A bounded family of Sigma1 proof witnesses, so IΣ1 induction suffices.
No equal-length hypothesis is needed: the raw nth operation is total. -/
lemma prefix_projection (n B B' : V) :
    ∀ i<n, CProv (wim (prefixContext n B B') (Eind B.[i] B'.[i])) :=
  ValidatorPrefixContext.projection CProv Eind prefixContext prefixContext_succ
    conj_left conj_right (fun h₁ h₂ => compose h₁ h₂) n B B'

lemma eindContext_projection (B B' i : V) (hi : i<len B) :
    CProv (wim (eindContext B B') (Eind B.[i] B'.[i])) :=
  prefix_projection (len B) B B' i hi

/-- Prepended coordinates commute through the reversed prefix conjunction by
finite classical proofs. Both proof-existence claims are Sigma1. -/
lemma prefix_cons_equiv (n B B' x y : V) :
    CProv (wim (prefixContext (n+1) (x∷B) (y∷B'))
      (conj (Eind x y) (prefixContext n B B'))) ∧
    CProv (wim (conj (Eind x y) (prefixContext n B B'))
      (prefixContext (n+1) (x∷B) (y∷B'))) :=
  ValidatorPrefixContext.cons_equiv CProv Eind prefixContext prefixContext_zero prefixContext_succ
    (fun h₁ h₂ => compose h₁ h₂) (Kalmar.self_imp cProv_classical)
    (fun a {_b _c} h => conj_mono_right a h) conj_interchange n B B' x y

lemma eindContext_cons_forward (B B' x y : V) :
    CProv (wim (eindContext (x∷B) (y∷B')) (conj (Eind x y) (eindContext B B'))) := by
  simpa only [eindContext,len_adjoin] using (prefix_cons_equiv (len B) B B' x y).1
lemma eindContext_cons_backward (B B' x y : V) :
    CProv (wim (conj (Eind x y) (eindContext B B')) (eindContext (x∷B) (y∷B'))) := by
  simpa only [eindContext,len_adjoin] using (prefix_cons_equiv (len B) B B' x y).2
lemma eindContext_cons_head (B B' x y : V) :
    CProv (wim (eindContext (x∷B) (y∷B')) (Eind x y)) :=
  compose (eindContext_cons_forward B B' x y) (conj_left _ _)
lemma eindContext_cons_tail (B B' x y : V) :
    CProv (wim (eindContext (x∷B) (y∷B')) (eindContext B B')) :=
  compose (eindContext_cons_forward B B' x y) (conj_right _ _)

/-- Turn the pushed-context body IH into the curried premises required by
`all_relational`; the old context is discharged before the new Eind premise. -/
lemma discharge_cons (B B' x y : V) {p : V}
    (h : CProv (wim (eindContext (x∷B) (y∷B')) p)) :
    CProv (wim (eindContext B B') (wim (Eind x y) p)) :=
  ded2 (.mp (.ax h) (.mp (.ax (eindContext_cons_backward B B' x y))
    (.mp (.mp (.ax (conj_intro_imp (Eind x y) (eindContext B B'))) h0) h1)))

lemma under_cons (B B' x y : V) {p : V}
    (h : CProv (wim (eindContext B B') (wim (Eind x y) p))) :
    CProv (wim (eindContext (x∷B) (y∷B')) p) :=
  ded1 (.mp (.mp (.ax h) (.mp (.ax (eindContext_cons_tail B B' x y)) h0))
    (.mp (.ax (eindContext_cons_head B B' x y)) h0))

/-- Contexts do not acquire a primitive-equality vacuity axiom. The actual
primitive implication weq→Eind is only precomposed with the body certificate. -/
lemma primitive_premise {h x y r : V}
    (hr : CProv (wim h (wim (Eind x y) r))) :
    CProv (wim h (wim (weq x y) r)) :=
  ded2 (.mp (.mp (.ax hr) h1) (.mp (.ax (Eq_Eind x y)) h0))

/-- Direct quantifier client. The old context is unchanged, and all four
vacuity resources remain explicit. No Eind→weq implication is used. -/
lemma all_of_cons (B B' p q x y : V)
    (hbody : CProv (wim (eindContext (x∷B) (y∷B')) (wim p q)))
    (vxh : Vac x (eindContext B B')) (vxq : Vac x q)
    (vyh : Vac y (eindContext B B')) (vyall : Vac y (wal x p)) :
    CProv (wim (eindContext B B') (wim (wal x p) (wal y q))) :=
  all_relational (eindContext B B') p q x y
    (primitive_premise (discharge_cons B B' x y hbody)) vxh vxq vyh vyall

private instance wal_sigma1 : 𝚺₁-Function₂[V] wal := wal_defined.to_definable₀
private instance vac_sigma1 : 𝚺₁-Relation[V] Vac := by
  unfold Vac
  definability

/-- A bounded endpoint-avoidance predicate, not an arbitrary-binder rule
for primitive equality. Eind_vac also handles collision with its auxiliary. -/
lemma prefixContext_vac (n B B' z : V) :
    (∀ i<n, z≠B.[i]) → (∀ i<n, z≠B'.[i]) → Vac z (prefixContext n B B') :=
  ValidatorPrefixContext.vac Eind prefixContext prefixContext_zero prefixContext_succ Vac
    vac_truth Eind_vac vac_conj n B B' z

lemma eindContext_vac (B B' z : V) (hlen : len B=len B')
    (hB : Avoid z B) (hB' : Avoid z B') : Vac z (eindContext B B') :=
  prefixContext_vac (len B) B B' z hB (fun i hi => hB' i (by rwa [← hlen]))

/-- Every diagonal context is an actual C222 theorem, including zero labels
and total out-of-range vector lookups in arbitrary prefix lengths. -/
lemma prefixContext_diagonal (n B : V) : CProv (prefixContext n B B) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using (cProv_truth (V := V))
  case succ n ih =>
    rw [prefixContext_succ]
    exact conj_intro (cProv_mp (Eq_Eind _ _) (ValidatorEqualityCore222.cProv_refl _)) ih

lemma eindContext_diagonal (B : V) : CProv (eindContext B B) :=
  prefixContext_diagonal (len B) B

/-- Avoidance supplies the old-context resources only; both body resources
remain caller obligations. All numeric labels may be zero or repeated. -/
lemma all_of_cons_avoiding_context (B B' p q x y : V) (hlen : len B=len B')
    (hbody : CProv (wim (eindContext (x∷B) (y∷B')) (wim p q)))
    (hxB : Avoid x B) (hxB' : Avoid x B')
    (hyB : Avoid y B) (hyB' : Avoid y B')
    (vxq : Vac x q) (vyall : Vac y (wal x p)) :
    CProv (wim (eindContext B B') (wim (wal x p) (wal y q))) :=
  all_of_cons B B' p q x y hbody
    (eindContext_vac B B' x hlen hxB hxB') vxq
    (eindContext_vac B B' y hlen hyB hyB') vyall

/-- Numeric witnesses from the actual represented checker, not an external
standard-Nat proof predicate or a semantic formula-validity assumption. -/
lemma projection_witness (B B' i : V) (hi : i<len B) :
    ∃ code : V, ArithmeticHistory222.value code =
      wim (eindContext B B') (Eind B.[i] B'.[i])+1 :=
  eindContext_projection B B' i hi

end LeanProofs.ZFCinPA.ValidatorEindContext222
