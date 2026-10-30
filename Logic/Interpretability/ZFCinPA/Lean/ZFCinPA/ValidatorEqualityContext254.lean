import ZFCinPA.ValidatorQuantifierCore254
import ZFCinPA.ValidatorPrefixContext
import ZFCinPA.ValidatorEnvironmentLabels254

set_option autoImplicit false
noncomputable section

/-!
A represented conjunction of coordinate equalities for internal bound stacks.
The prefix iterator prepends its newest equality, so its conjunction order is
reversed. Finite propositional certificates give the ordinary head-cons law
up to CProv implications in both directions. All recursion and indices are
internal; no source-formula induction or accepted-proof renaming is assumed.
-/
namespace LeanProofs.ZFCinPA.ValidatorEqualityContext254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ValidatorProvability254 ValidatorQuantifierCore254
open scoped LO.FirstOrder.Arithmetic

namespace Prefix

def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “out left right. out = 0”
  succ := .mkSigma “out previous time left right.
    ∃ a, !nthDef a left time ∧ ∃ b, !nthDef b right time ∧
    ∃ atom, !weqDef atom a b ∧ ∃ np, !wimDef np previous 1 ∧
    ∃ mid, !wimDef mid atom np ∧ !wimDef out mid 1”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def construction : PR.Construction V blueprint where
  zero _ := 0
  succ env time previous := conj (weq (env 0).[time] (env 1).[time]) previous
  zero_defined := .mk fun e => by simp [blueprint]
  succ_defined := .mk fun e => by simp [blueprint,ValidatorQuantifierCore254.conj,ValidatorQuantifierCore254.neg]

end Prefix

/-- Graph argument order: output, prefix length, left stack, right stack. -/
def prefixContextDef : 𝚺₁.Semisentence 4 := Prefix.blueprint.resultDef

def eqContextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out left right. ∃ n, !lenDef n left ∧ !prefixContextDef out n left right”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def prefixContext (n B B' : V) : V :=
  Prefix.construction.result ![B,B'] n
noncomputable def eqContext (B B' : V) : V := prefixContext (len B) B B'

instance prefixContext_defined : 𝚺₁-Function₃[V] prefixContext via prefixContextDef :=
  .mk fun e => by
    have hparams : (fun i : Fin 2 => e i.succ.succ) = ![e 2,e 3] :=
      Matrix.fun_eq_vec_two (fun i : Fin 2 => e i.succ.succ)
    simpa [prefixContextDef,prefixContext,Matrix.comp_vecCons',Matrix.comp_vecCons'',hparams]
      using (Prefix.construction (V := V)).result_defined.defined e
instance prefixContext_delta : 𝚫₁-Function₃[V] prefixContext :=
  prefixContext_defined.graph_delta.to_definable
instance eqContext_defined : 𝚺₁-Function₂[V] eqContext via eqContextDef :=
  .mk fun e => by simp [eqContextDef,eqContext]
instance eqContext_delta : 𝚫₁-Function₂[V] eqContext :=
  eqContext_defined.graph_delta.to_definable

/- Use the fixed arithmetic graphs in induction predicates. The Defined
instances alone do not register general definability for these functions. -/
private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
private instance weq_sigma1 : 𝚺₁-Function₂[V] weq := weq_defined.to_definable₀
private instance prefixContext_sigma1 : 𝚺₁-Function₃[V] prefixContext :=
  prefixContext_defined.to_definable
private instance conj_sigma1 : 𝚺₁-Function₂[V] conj := by
  unfold conj ValidatorQuantifierCore254.neg
  definability

@[simp] lemma prefixContext_zero (B B' : V) : prefixContext 0 B B'=0 := by
  simp [prefixContext,Prefix.construction]
@[simp] lemma prefixContext_succ (n B B' : V) :
    prefixContext (n+1) B B'=conj (weq B.[n] B'.[n]) (prefixContext n B B') := by
  simp [prefixContext,Prefix.construction]
@[simp] lemma eqContext_nil (B' : V) : eqContext (0 : V) B'=0 := by
  simp [eqContext]

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
No equality-length hypothesis is needed: the raw nth operation is total. -/
lemma prefix_projection (n B B' : V) :
    ∀ i<n, CProv (wim (prefixContext n B B') (weq B.[i] B'.[i])) :=
  ValidatorPrefixContext.projection CProv weq prefixContext prefixContext_succ
    conj_left conj_right (fun h₁ h₂ => compose h₁ h₂) n B B'

lemma eqContext_projection (B B' i : V) (hi : i<len B) :
    CProv (wim (eqContext B B') (weq B.[i] B'.[i])) :=
  prefix_projection (len B) B B' i hi

/-- Prepended coordinates commute through the reversed prefix conjunction by
finite classical proofs. Both proof-existence claims are Sigma1. -/
lemma prefix_cons_equiv (n B B' x y : V) :
    CProv (wim (prefixContext (n+1) (x∷B) (y∷B'))
      (conj (weq x y) (prefixContext n B B'))) ∧
    CProv (wim (conj (weq x y) (prefixContext n B B'))
      (prefixContext (n+1) (x∷B) (y∷B'))) :=
  ValidatorPrefixContext.cons_equiv CProv weq prefixContext prefixContext_zero prefixContext_succ
    (fun h₁ h₂ => compose h₁ h₂) (Kalmar.self_imp cProv_classical)
    (fun a {_b _c} h => conj_mono_right a h) conj_interchange n B B' x y

lemma eqContext_cons_forward (B B' x y : V) :
    CProv (wim (eqContext (x∷B) (y∷B')) (conj (weq x y) (eqContext B B'))) := by
  simpa only [eqContext,len_adjoin] using (prefix_cons_equiv (len B) B B' x y).1
lemma eqContext_cons_backward (B B' x y : V) :
    CProv (wim (conj (weq x y) (eqContext B B')) (eqContext (x∷B) (y∷B'))) := by
  simpa only [eqContext,len_adjoin] using (prefix_cons_equiv (len B) B B' x y).2
lemma eqContext_cons_head (B B' x y : V) :
    CProv (wim (eqContext (x∷B) (y∷B')) (weq x y)) :=
  compose (eqContext_cons_forward B B' x y) (conj_left _ _)
lemma eqContext_cons_tail (B B' x y : V) :
    CProv (wim (eqContext (x∷B) (y∷B')) (eqContext B B')) :=
  compose (eqContext_cons_forward B B' x y) (conj_right _ _)

/-- Turn the pushed-context body IH into the curried premises required by
`all_relational`; the old context is discharged before the new equality. -/
lemma discharge_cons (B B' x y : V) {p : V}
    (h : CProv (wim (eqContext (x∷B) (y∷B')) p)) :
    CProv (wim (eqContext B B') (wim (weq x y) p)) :=
  ded2 (.mp (.ax h) (.mp (.ax (eqContext_cons_backward B B' x y))
    (.mp (.mp (.ax (conj_intro_imp (weq x y) (eqContext B B'))) h0) h1)))

lemma under_cons (B B' x y : V) {p : V}
    (h : CProv (wim (eqContext B B') (wim (weq x y) p))) :
    CProv (wim (eqContext (x∷B) (y∷B')) p) :=
  ded1 (.mp (.mp (.ax h) (.mp (.ax (eqContext_cons_tail B B' x y)) h0))
    (.mp (.ax (eqContext_cons_head B B' x y)) h0))

/-- Direct quantifier client for the paired-stack induction hypothesis. -/
lemma all_of_cons (B B' p q x y : V)
    (hbody : CProv (wim (eqContext (x∷B) (y∷B')) (wim p q)))
    (vxh : Vac x (eqContext B B')) (vxq : Vac x q)
    (vyh : Vac y (eqContext B B')) (vyall : Vac y (wal x p)) :
    CProv (wim (eqContext B B') (wim (wal x p) (wal y q))) :=
  all_relational (eqContext B B') p q x y
    (discharge_cons B B' x y hbody) vxh vxq vyh vyall

end LeanProofs.ZFCinPA.ValidatorEqualityContext254
