import ZFCinPA.ValidatorFormulaEncoder254

set_option autoImplicit false
noncomputable section

/-!
Finite internal variable environments for a later configurable encoder.
Free labels outside the stored vector use the positive fallback label 1.
The exact cons/tail laws therefore require no source free-variable bound.
Bound labels are looked up in a separate internal vector. This is variable
computation, not CProv alpha conversion or an internal proof compiler.
-/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic

def freeLabelDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out env index. ∃ length, !lenDef length env ∧
    ((index < length ∧ !nthDef out env index) ∨
     (length ≤ index ∧ out = 1))”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def freeLabel (env index : V) : V := by
  classical
  exact if index<len env then env.[index] else 1
instance freeLabel_defined : 𝚺₁-Function₂[V] freeLabel via freeLabelDef :=
  .mk fun e => by
    classical
    by_cases hi : e 2<len (e 1)
    · simp [freeLabelDef,freeLabel,hi,not_le.mpr hi]
    · simp [freeLabelDef,freeLabel,hi,le_of_not_gt hi]
instance freeLabel_delta : 𝚫₁-Function₂[V] freeLabel :=
  freeLabel_defined.graph_delta.to_definable

@[simp] lemma freeLabel_nil (index : V) : freeLabel (0 : V) index=1 := by
  simp [freeLabel]
@[simp] lemma freeLabel_cons_zero (x env : V) : freeLabel (x∷env) 0=x := by
  simp [freeLabel]
@[simp] lemma freeLabel_cons_succ (x env index : V) :
    freeLabel (x∷env) (index+1)=freeLabel env index := by
  classical
  by_cases hi : index<len env
  · simp [freeLabel,hi]
  · simp [freeLabel,hi]

/-- The actual HFS vector tail, including the empty-vector case. -/
noncomputable def tail (env : V) : V := sndIdx env
@[simp] lemma tail_nil : tail (0 : V)=0 := by simp [tail,sndIdx,pi₂_zero]
@[simp] lemma tail_cons (x env : V) : tail (x∷env)=env := by simp [tail]
lemma freeLabel_tail (env index : V) :
    freeLabel env (index+1)=freeLabel (tail env) index := by
  rcases nil_or_adjoin env with (rfl | ⟨x,env,rfl⟩)
  · simp
  · simp

def Positive (env : V) : Prop := ∀ j<len env, 0<env.[j]
def Below (env next : V) : Prop := 1<next ∧ ∀ j<len env, env.[j]<next

lemma positive_label {env : V} (he : Positive env) (j : V) : 0<freeLabel env j := by
  classical
  by_cases hj : j<len env
  · simpa [freeLabel,hj] using he j hj
  · simp [freeLabel,hj]
lemma below_label {env next : V} (he : Below env next) (j : V) :
    freeLabel env j<next := by
  classical
  by_cases hj : j<len env
  · simpa [freeLabel,hj] using he.2 j hj
  · simpa [freeLabel,hj] using he.1
private lemma all_nth_cons {P : V → Prop} {env x : V}
    (he : ∀ j<len env, P env.[j]) (hx : P x) :
    ∀ j<len (x∷env), P (x∷env).[j] := by
  intro j hj
  rcases zero_or_succ j with (rfl | ⟨j,rfl⟩)
  · simpa using hx
  · simpa using he j (by simpa using hj)

lemma positive_cons {env x : V} (he : Positive env) (hx : 0<x) : Positive (x∷env) :=
  all_nth_cons (P := fun v => 0<v) he hx
lemma below_cons {env x next : V} (he : Below env next) (hx : x<next) :
    Below (x∷env) next :=
  ⟨he.1, all_nth_cons (P := fun v => v<next) he.2 hx⟩

namespace TermLabels

private instance termShift_delta : 𝚫₁-Function₁[V] (termShift ℒₛₑₜ) :=
  termShift.defined.graph_delta.to_definable

/-- Parameter order: free environment, bound environment. -/
def blueprint : Language.TermRec.Blueprint 2 where
  bvar := .mkSigma “out index free bound. !nthDef out bound index”
  fvar := .mkSigma “out index free bound. !freeLabelDef out free index”
  func := .mkSigma “out k symbol oldArgs newArgs free bound. out = 0”

def construction : Language.TermRec.Construction V blueprint where
  bvar parameters index := (parameters 1).[index]
  fvar parameters index := freeLabel (parameters 0) index
  func _ _ _ _ _ := 0
  bvar_defined := .mk fun e => by simp [blueprint]
  fvar_defined := .mk fun e => by simp [blueprint]
  func_defined := .mk fun e => by simp [blueprint]

noncomputable def term (free bound source : V) : V :=
  construction.result ℒₛₑₜ ![free,bound] source
noncomputable def vec (free bound arity terms : V) : V :=
  construction.resultVec ℒₛₑₜ ![free,bound] arity terms

/-- Graph order: output, free environment, bound environment, source term. -/
def termDef : 𝚺₁.Semisentence 4 :=
  (blueprint.result ℒₛₑₜ).rew (Rew.subst ![#0,#3,#1,#2])
/-- Graph order: output vector, free/bound environments, arity, source vector. -/
def vecDef : 𝚺₁.Semisentence 5 :=
  (blueprint.resultVec ℒₛₑₜ).rew (Rew.subst ![#0,#3,#4,#1,#2])
instance term_defined : 𝚺₁-Function₃[V] term via termDef := .mk fun e => by
  simpa [termDef,term,Matrix.comp_vecCons',Matrix.comp_vecCons'']
    using (construction.result_defined (L := ℒₛₑₜ)).defined ![e 0,e 3,e 1,e 2]
instance vec_defined : 𝚺₁-Function₄[V] vec via vecDef := .mk fun e => by
  simpa [vecDef,vec,Matrix.comp_vecCons',Matrix.comp_vecCons'']
    using (construction.resultVec_defined (L := ℒₛₑₜ)).defined ![e 0,e 3,e 4,e 1,e 2]
instance term_delta : 𝚫₁-Function₃[V] term := term_defined.graph_delta.to_definable
instance vec_delta : 𝚫₁-Function₄[V] vec := vec_defined.graph_delta.to_definable

@[simp] lemma term_bvar (free bound index : V) : term free bound (^#index)=bound.[index] := by
  simp [term,construction]
@[simp] lemma term_fvar (free bound index : V) :
    term free bound (^&index)=freeLabel free index := by simp [term,construction]
lemma term_func (free bound : V) {arity symbol terms : V}
    (hf : (ℒₛₑₜ).IsFunc arity symbol) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    term free bound (^func arity symbol terms)=0 := by simp [term,construction,hf,ht]
lemma vec_length (free bound : V) {arity terms : V} (ht : IsUTermVec ℒₛₑₜ arity terms) :
    len (vec free bound arity terms)=arity := construction.resultVec_lh ℒₛₑₜ ![free,bound] ht
lemma vec_nth (free bound : V) {arity terms i : V}
    (ht : IsUTermVec ℒₛₑₜ arity terms) (hi : i<arity) :
    (vec free bound arity terms).[i]=term free bound terms.[i] :=
  construction.nth_resultVec ℒₛₑₜ ![free,bound] ht hi

/-- This is syntax transport over all internal terms, not theorem renaming. -/
lemma term_shift {source : V} (ht : IsUTerm ℒₛₑₜ source) :
    ∀ free bound : V, term free bound (termShift ℒₛₑₜ source)=term (tail free) bound source := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ source ht
  · unfold tail; definability
  · intro index free bound; simp
  · intro index free bound
    simpa only [termShift_fvar,term_fvar] using freeLabel_tail free index
  · intro arity symbol terms hf hv _ih free bound
    rw [termShift_func hf hv,term_func free bound hf hv.termShiftVec,
      term_func (tail free) bound hf hv]

lemma vec_shift (free bound : V) {arity terms : V} (ht : IsUTermVec ℒₛₑₜ arity terms) :
    vec free bound arity (termShiftVec ℒₛₑₜ arity terms)=vec (tail free) bound arity terms := by
  apply nth_ext' arity
  · exact vec_length free bound ht.termShiftVec
  · exact vec_length (tail free) bound ht
  · intro i hi
    rw [vec_nth free bound ht.termShiftVec hi,nth_termShiftVec ht hi,
      vec_nth (tail free) bound ht hi]
    exact term_shift (ht.nth hi) free bound

end TermLabels

/-- The recursion state is the actual HFS vector [free,bound,fresh]. -/
def nextStateDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out state. ∃ free, !nthDef free state 0 ∧
    ∃ bound, !nthDef bound state 1 ∧ ∃ fresh, !nthDef fresh state 2 ∧
    ∃ newBound, !adjoinDef newBound fresh bound ∧
    ∃ tail, !mkVec₂Def tail newBound (fresh+2) ∧ !adjoinDef out free tail”
noncomputable def nextState (state : V) : V :=
  ?[state.[0],state.[2]∷state.[1],state.[2]+2]
instance nextState_defined : 𝚺₁-Function₁[V] nextState via nextStateDef :=
  .mk fun e => by simp [nextStateDef,nextState]

def atomDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out state arity symbol terms. ∃ free, !nthDef free state 0 ∧
    ∃ bound, !nthDef bound state 1 ∧
    ∃ args, !TermLabels.vecDef args free bound arity terms ∧
    ∃ left, !nthDef left args 0 ∧ ∃ right, !nthDef right args 1 ∧
    ((symbol = 0 ∧ !ArithmeticCode254.weqDef out left right) ∨
     (symbol ≠ 0 ∧ !ArithmeticCode254.welDef out left right))”

namespace Formulas
open _root_.SetTheory.BusyBeaver.ZFC

def blueprint : UformulaRec1.Blueprint where
  rel := atomDef
  nrel := .mkSigma “out state arity symbol terms.
    ∃ atom, !atomDef atom state arity symbol terms ∧ !ArithmeticCode254.wimDef out atom 1”
  verum := .mkSigma “out state. out = 0”
  falsum := .mkSigma “out state. out = 1”
  and := .mkSigma “out state p q left right.
    ∃ nr, !ArithmeticCode254.wimDef nr right 1 ∧
    ∃ mid, !ArithmeticCode254.wimDef mid left nr ∧ !ArithmeticCode254.wimDef out mid 1”
  or := .mkSigma “out state p q left right.
    ∃ nl, !ArithmeticCode254.wimDef nl left 1 ∧ !ArithmeticCode254.wimDef out nl right”
  all := .mkSigma “out state p body.
    ∃ fresh, !nthDef fresh state 2 ∧ !ArithmeticCode254.walDef out fresh body”
  exs := .mkSigma “out state p body.
    ∃ fresh, !nthDef fresh state 2 ∧
    ∃ neg, !ArithmeticCode254.wimDef neg body 1 ∧
    ∃ univ, !ArithmeticCode254.walDef univ fresh neg ∧ !ArithmeticCode254.wimDef out univ 1”
  allChanges := nextStateDef
  exsChanges := nextStateDef

noncomputable def atom (state arity symbol terms : V) : V := by
  classical
  let args := TermLabels.vec state.[0] state.[1] arity terms
  exact if symbol=0 then ArithmeticCode254.weq args.[0] args.[1]
    else ArithmeticCode254.wel args.[0] args.[1]
instance atom_defined : 𝚺₁-Function₄[V] atom via atomDef := .mk fun e => by
  classical
  by_cases hr : e 3=0 <;> simp [atomDef,atom,hr]

def construction : UformulaRec1.Construction V blueprint where
  rel := atom
  nrel state arity symbol terms := ArithmeticCode254.wim (atom state arity symbol terms) 1
  verum _ := 0
  falsum _ := 1
  and _ _ _ left right := ArithmeticCode254.wim
    (ArithmeticCode254.wim left (ArithmeticCode254.wim right 1)) 1
  or _ _ _ left right := ArithmeticCode254.wim (ArithmeticCode254.wim left 1) right
  all state _ body := ArithmeticCode254.wal state.[2] body
  exs state _ body := ArithmeticCode254.wim
    (ArithmeticCode254.wal state.[2] (ArithmeticCode254.wim body 1)) 1
  allChanges := nextState
  exsChanges := nextState
  rel_defined := atom_defined
  nrel_defined := .mk fun e => by simp [blueprint]
  verum_defined := .mk fun e => by simp [blueprint]
  falsum_defined := .mk fun e => by simp [blueprint]
  and_defined := .mk fun e => by simp [blueprint]
  or_defined := .mk fun e => by simp [blueprint]
  all_defined := .mk fun e => by simp [blueprint]
  exs_defined := .mk fun e => by simp [blueprint]
  allChanges_defined := nextState_defined
  exChanges_defined := nextState_defined
end Formulas

def encodeStateDef : 𝚺₁.Semisentence 3 := Formulas.blueprint.result ℒₛₑₜ
def encodeDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out free bound fresh source. ∃ tail, !mkVec₂Def tail bound fresh ∧
    ∃ state, !adjoinDef state free tail ∧ !encodeStateDef out state source”
noncomputable def encodeState (state source : V) : V :=
  Formulas.construction.result ℒₛₑₜ state source
noncomputable def encode (free bound fresh source : V) : V :=
  encodeState ?[free,bound,fresh] source
instance encodeState_defined : 𝚺₁-Function₂[V] encodeState via encodeStateDef :=
  Formulas.construction.result_defined
instance encode_defined : 𝚺₁-Function₄[V] encode via encodeDef :=
  .mk fun e => by simp [encodeDef,encode]
instance encode_delta : 𝚫₁-Function₄[V] encode := encode_defined.graph_delta.to_definable

open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
lemma encode_of_not_formula (free bound fresh : V) {p : V} (hp : ¬IsUFormula ℒₛₑₜ p) :
    encode free bound fresh p=0 := Formulas.construction.result_prop_not _ hp
@[simp] lemma encode_verum (free bound fresh : V) :
    encode free bound fresh (^⊤ : V)=0 := by simp [encode,encodeState,Formulas.construction]
@[simp] lemma encode_falsum (free bound fresh : V) :
    encode free bound fresh (^⊥ : V)=1 := by simp [encode,encodeState,Formulas.construction]
lemma encode_rel (free bound fresh : V) {arity symbol terms : V}
    (hr : (ℒₛₑₜ).IsRel arity symbol) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    encode free bound fresh (^rel arity symbol terms)=
      Formulas.atom ?[free,bound,fresh] arity symbol terms := by
  simp [encode,encodeState,Formulas.construction,hr,ht]
lemma encode_nrel (free bound fresh : V) {arity symbol terms : V}
    (hr : (ℒₛₑₜ).IsRel arity symbol) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    encode free bound fresh (^nrel arity symbol terms)=
      wim (Formulas.atom ?[free,bound,fresh] arity symbol terms) 1 := by
  simp [encode,encodeState,Formulas.construction,hr,ht]
lemma encode_and (free bound fresh : V) {p q : V}
    (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    encode free bound fresh (p ^⋏ q)=
      wim (wim (encode free bound fresh p) (wim (encode free bound fresh q) 1)) 1 := by
  simp [encode,encodeState,Formulas.construction,hp,hq]
lemma encode_or (free bound fresh : V) {p q : V}
    (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    encode free bound fresh (p ^⋎ q)=
      wim (wim (encode free bound fresh p) 1) (encode free bound fresh q) := by
  simp [encode,encodeState,Formulas.construction,hp,hq]
lemma encode_all (free bound fresh : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    encode free bound fresh (^∀ p)=
      wal fresh (encode free (fresh∷bound) (fresh+2) p) := by
  simp [encode,encodeState,Formulas.construction,nextState,hp]
lemma encode_exs (free bound fresh : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    encode free bound fresh (^∃ p)=
      wim (wal fresh (wim (encode free (fresh∷bound) (fresh+2) p) 1)) 1 := by
  simp [encode,encodeState,Formulas.construction,nextState,hp]

private instance shift_delta : 𝚫₁-Function₁[V] (shift ℒₛₑₜ) :=
  shift.defined.graph_delta.to_definable

lemma atom_shift (free bound fresh : V) {arity symbol terms : V}
    (ht : IsUTermVec ℒₛₑₜ arity terms) :
    Formulas.atom ?[free,bound,fresh] arity symbol (termShiftVec ℒₛₑₜ arity terms)=
      Formulas.atom ?[tail free,bound,fresh] arity symbol terms := by
  simp only [Formulas.atom,nth_adjoin_zero,nth_adjoin_one,
    TermLabels.vec_shift free bound ht]

/-- Exact internal SHIFT law. The free environment tails while the bound
environment and next binder label stay fixed, including at nested binders. -/
lemma encode_shift {source : V} (hp : IsUFormula ℒₛₑₜ source) :
    ∀ free bound fresh : V,
      encode free bound fresh (shift ℒₛₑₜ source)=encode (tail free) bound fresh source := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source hp
  · unfold tail; definability
  · intro arity symbol terms hR ht free bound fresh
    rw [shift_rel hR ht,encode_rel free bound fresh hR ht.termShiftVec,
      encode_rel (tail free) bound fresh hR ht]
    exact atom_shift free bound fresh ht
  · intro arity symbol terms hR ht free bound fresh
    rw [shift_nrel hR ht,encode_nrel free bound fresh hR ht.termShiftVec,
      encode_nrel (tail free) bound fresh hR ht,atom_shift free bound fresh ht]
  · intro free bound fresh; simp
  · intro free bound fresh; simp
  · intro p q hp hq ihp ihq free bound fresh
    rw [shift_and hp hq,encode_and free bound fresh hp.shift hq.shift,
      encode_and (tail free) bound fresh hp hq,ihp,ihq]
  · intro p q hp hq ihp ihq free bound fresh
    rw [shift_or hp hq,encode_or free bound fresh hp.shift hq.shift,
      encode_or (tail free) bound fresh hp hq,ihp,ihq]
  · intro p hp ih free bound fresh
    rw [shift_all hp,encode_all free bound fresh hp.shift,
      encode_all (tail free) bound fresh hp,ih]
  · intro p hp ih free bound fresh
    rw [shift_exs hp,encode_exs free bound fresh hp.shift,
      encode_exs (tail free) bound fresh hp,ih]

end LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
