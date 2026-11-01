import ZFCinPA.Instances
import BusyBeaver.ZFC.ArithmeticCode254

set_option autoImplicit false
noncomputable section

/-!
A fixed Sigma1 translation of internal set-language syntax into the literal
numeric formula coding. On typed inputs, label 0 is reserved: source free j
has label 2*j+1, and bound i<m at depth m has label 2*(m-i). Quantifiers use
label 2*(m+1). UformulaRec1 changes its internal depth parameter under binders.
This file supplies syntax graphs and constructor equations, not a proof-code
compiler, preservation of the ZF axioms, or a consistency implication.
-/
namespace LeanProofs.ZFCinPA.ValidatorFormulaEncoder254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open scoped LO.FirstOrder.Arithmetic

namespace Labels

/-- Numeric outputs are arbitrary V-values; they need not be HFS term codes.
The function-symbol branch is immaterial for the actual function-free language. -/
def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “out index depth. ∃ diff, !subDef diff depth index ∧ out = 2*diff”
  fvar := .mkSigma “out index depth. out = 2*index+1”
  func := .mkSigma “out k f oldArgs newArgs depth. out = 0”

/-- Argument order: output, depth, source term. -/
noncomputable def termDef : 𝚺₁.Semisentence 3 :=
  (blueprint.result ℒₛₑₜ).rew (Rew.subst ![#0,#2,#1])
/-- Argument order: output vector, depth, arity, source argument vector. -/
noncomputable def vecDef : 𝚺₁.Semisentence 4 :=
  (blueprint.resultVec ℒₛₑₜ).rew (Rew.subst ![#0,#2,#3,#1])

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar parameters index := 2*(parameters 0-index)
  fvar _ index := 2*index+1
  func _ _ _ _ _ := 0
  bvar_defined := .mk fun e => by simp [blueprint]
  fvar_defined := .mk fun e => by simp [blueprint]
  func_defined := .mk fun e => by simp [blueprint]

noncomputable def term (depth t : V) : V := construction.result ℒₛₑₜ ![depth] t
noncomputable def vec (depth k terms : V) : V := construction.resultVec ℒₛₑₜ ![depth] k terms

instance term_defined : 𝚺₁-Function₂[V] term via termDef := .mk fun e => by
  simpa [termDef,term,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
    using (construction.result_defined (L := ℒₛₑₜ)).defined ![e 0,e 2,e 1]
instance vec_defined : 𝚺₁-Function₃[V] vec via vecDef := .mk fun e => by
  simpa [vecDef,vec,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
    using (construction.resultVec_defined (L := ℒₛₑₜ)).defined ![e 0,e 2,e 3,e 1]

@[simp] lemma term_bvar (depth index : V) : term depth (^#index) = 2*(depth-index) := by
  simp [term,construction]
@[simp] lemma term_fvar (depth index : V) : term depth (^&index) = 2*index+1 := by
  simp [term,construction]
lemma vec_length (depth : V) {k terms : V} (ht : IsUTermVec ℒₛₑₜ k terms) :
    len (vec depth k terms) = k := construction.resultVec_lh ℒₛₑₜ ![depth] ht
lemma vec_nth (depth : V) {k terms index : V}
    (ht : IsUTermVec ℒₛₑₜ k terms) (hi : index<k) :
    (vec depth k terms).[index] = term depth terms.[index] :=
  construction.nth_resultVec ℒₛₑₜ ![depth] ht hi

end Labels

/-- All graph syntax below is selected before the ambient model. Actual
set-language atom symbols are 0 (equality) and 1 (membership), both binary. -/
noncomputable def atomDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out depth k symbol terms. ∃ args, !Labels.vecDef args depth k terms ∧
    ∃ left, !nthDef left args 0 ∧ ∃ right, !nthDef right args 1 ∧
    ((symbol = 0 ∧ !weqDef out left right) ∨
     (symbol ≠ 0 ∧ !welDef out left right))”

namespace Formulas

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := atomDef
  nrel := .mkSigma “out depth k symbol terms.
    ∃ atom, !atomDef atom depth k symbol terms ∧ !wimDef out atom 1”
  verum := .mkSigma “out depth. out = 0”
  falsum := .mkSigma “out depth. out = 1”
  and := .mkSigma “out depth p q left right.
    ∃ nr, !wimDef nr right 1 ∧ ∃ mid, !wimDef mid left nr ∧ !wimDef out mid 1”
  or := .mkSigma “out depth p q left right.
    ∃ nl, !wimDef nl left 1 ∧ !wimDef out nl right”
  all := .mkSigma “out depth p body. !walDef out (2*(depth+1)) body”
  exs := .mkSigma “out depth p body.
    ∃ neg, !wimDef neg body 1 ∧ ∃ univ, !walDef univ (2*(depth+1)) neg ∧
    !wimDef out univ 1”
  allChanges := .mkSigma “next depth. next = depth+1”
  exsChanges := .mkSigma “next depth. next = depth+1”

end Formulas

/-- One fixed graph for arbitrary internal source depth and source formula. -/
noncomputable def encodeDef : 𝚺₁.Semisentence 3 := Formulas.blueprint.result ℒₛₑₜ

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def atom (depth k symbol terms : V) : V := by
  classical
  let args := Labels.vec depth k terms
  exact if symbol=0 then weq args.[0] args.[1] else wel args.[0] args.[1]
instance atom_defined : 𝚺₁-Function₄[V] atom via atomDef := .mk fun e => by
  classical
  by_cases h : e 3=0 <;> simp [atomDef,atom,h]

namespace Formulas

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel := atom
  nrel depth k symbol terms := wim (atom depth k symbol terms) 1
  verum _ := 0
  falsum _ := 1
  and _ _ _ left right := wim (wim left (wim right 1)) 1
  or _ _ _ left right := wim (wim left 1) right
  all depth _ body := wal (2*(depth+1)) body
  exs depth _ body := wim (wal (2*(depth+1)) (wim body 1)) 1
  allChanges depth := depth+1
  exsChanges depth := depth+1
  rel_defined := atom_defined
  nrel_defined := .mk fun e => by simp [blueprint]
  verum_defined := .mk fun e => by simp [blueprint]
  falsum_defined := .mk fun e => by simp [blueprint]
  and_defined := .mk fun e => by simp [blueprint]
  or_defined := .mk fun e => by simp [blueprint]
  all_defined := .mk fun e => by simp [blueprint]
  exs_defined := .mk fun e => by simp [blueprint]
  allChanges_defined := .mk fun e => by simp [blueprint]
  exChanges_defined := .mk fun e => by simp [blueprint]

end Formulas

noncomputable def encode (depth source : V) : V :=
  Formulas.construction.result ℒₛₑₜ depth source
instance encode_defined : 𝚺₁-Function₂[V] encode via encodeDef :=
  Formulas.construction.result_defined
instance encode_definable : 𝚫₁-Function₂[V] encode :=
  encode_defined.graph_delta.to_definable

lemma encode_of_not_formula (depth : V) {p : V} (hp : ¬IsUFormula ℒₛₑₜ p) :
    encode depth p=0 := Formulas.construction.result_prop_not depth hp
@[simp] lemma encode_verum (depth : V) : encode depth (^⊤ : V)=0 := by
  simp [encode,Formulas.construction]
@[simp] lemma encode_falsum (depth : V) : encode depth (^⊥ : V)=1 := by
  simp [encode,Formulas.construction]
lemma encode_rel (depth : V) {k symbol terms : V}
    (hr : (ℒₛₑₜ).IsRel k symbol) (ht : IsUTermVec ℒₛₑₜ k terms) :
    encode depth (^rel k symbol terms)=atom depth k symbol terms := by
  simp [encode,Formulas.construction,hr,ht]
lemma encode_nrel (depth : V) {k symbol terms : V}
    (hr : (ℒₛₑₜ).IsRel k symbol) (ht : IsUTermVec ℒₛₑₜ k terms) :
    encode depth (^nrel k symbol terms)=wim (atom depth k symbol terms) 1 := by
  simp [encode,Formulas.construction,hr,ht]
lemma encode_and (depth : V) {p q : V}
    (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    encode depth (p ^⋏ q)=wim (wim (encode depth p) (wim (encode depth q) 1)) 1 := by
  simp [encode,Formulas.construction,hp,hq]
lemma encode_or (depth : V) {p q : V}
    (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    encode depth (p ^⋎ q)=wim (wim (encode depth p) 1) (encode depth q) := by
  simp [encode,Formulas.construction,hp,hq]
lemma encode_all (depth : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    encode depth (^∀ p)=wal (2*(depth+1)) (encode (depth+1) p) := by
  simp [encode,Formulas.construction,hp]
lemma encode_exs (depth : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    encode depth (^∃ p)=wim (wal (2*(depth+1)) (wim (encode (depth+1) p) 1)) 1 := by
  simp [encode,Formulas.construction,hp]

end LeanProofs.ZFCinPA.ValidatorFormulaEncoder254
