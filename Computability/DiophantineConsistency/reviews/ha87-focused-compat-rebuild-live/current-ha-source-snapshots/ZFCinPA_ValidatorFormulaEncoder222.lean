import ZFCinPA.ValidatorEnvironmentLabels254
import ZFCinPA.ValidatorEind222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! A represented set-language encoder with actual C222 indiscernibility at
equality atoms. The existing term-label interpreter, HFS state and generic
formula recursion are reused. No C254 provability or equality-vacuity rule
is imported. All syntax graphs are fixed before the ambient arithmetic model.
This IΣ1 checkpoint asserts syntax identities, not semantic seed validity,
uniform proof translation, or the later IΣ2 vacuity theorem. -/
namespace LeanProofs.ZFCinPA.ValidatorFormulaEncoder222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ArithmeticTemplates254
open ValidatorEind222
open scoped LO.FirstOrder.Arithmetic

private def bi (x y : Circuit) : Circuit := .conj (.im x y) (.im y x)
def eindCircuit : Circuit :=
  .conj (.al .input2 (bi (.el .input2 .input0) (.el .input2 .input1)))
    (.al .input2 (bi (.el .input0 .input2) (.el .input1 .input2)))
def eindDef : 𝚺₀.Semisentence 3 := .mkSigma
  “out a b. !(eindCircuit.graph) out a b (a+b+1) 0”

/-- The unchanged syntax-only interpreter determines every argument label. -/
def atomDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out state arity symbol terms. ∃ free, !nthDef free state 0 ∧
    ∃ bound, !nthDef bound state 1 ∧
    ∃ args, !ValidatorEnvironmentLabels254.TermLabels.vecDef args free bound arity terms ∧
    ∃ left, !nthDef left args 0 ∧ ∃ right, !nthDef right args 1 ∧
    ((symbol = 0 ∧ !eindDef out left right) ∨
     (symbol ≠ 0 ∧ !ArithmeticCode254.welDef out left right))”

/-- Only the two atomic branches change; every other syntax clause and the
literal HFS binder-state update is the accepted existing blueprint. -/
def blueprint : UformulaRec1.Blueprint :=
  { ValidatorEnvironmentLabels254.Formulas.blueprint with
    rel := atomDef
    nrel := .mkSigma “out state arity symbol terms.
      ∃ atom, !atomDef atom state arity symbol terms ∧
        !ArithmeticCode254.wimDef out atom 1” }

def encodeStateDef : 𝚺₁.Semisentence 3 := blueprint.result ℒₛₑₜ
def encodeDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out free bound fresh source. ∃ tail, !mkVec₂Def tail bound fresh ∧
    ∃ state, !adjoinDef state free tail ∧ !encodeStateDef out state source”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance eind_defined : 𝚺₀-Function₂[V] Eind via eindDef := .mk fun e => by
  simp [eindDef, eindCircuit, bi, Eind, aux, Ev, Bin, Bout, biff,
    Circuit.conj, Circuit.neg,
    ValidatorRelationalCore222.conj, ValidatorRelationalCore222.neg]

noncomputable def atom (state arity symbol terms : V) : V := by
  classical
  let args := ValidatorEnvironmentLabels254.TermLabels.vec state.[0] state.[1] arity terms
  exact if symbol=0 then Eind args.[0] args.[1] else wel args.[0] args.[1]

instance atom_defined : 𝚺₁-Function₄[V] atom via atomDef := .mk fun e => by
  classical
  by_cases hr : e 3=0 <;> simp [atomDef, atom, hr]

def construction : UformulaRec1.Construction V blueprint where
  rel := atom
  nrel state arity symbol terms := wim (atom state arity symbol terms) 1
  verum := ValidatorEnvironmentLabels254.Formulas.construction.verum
  falsum := ValidatorEnvironmentLabels254.Formulas.construction.falsum
  and := ValidatorEnvironmentLabels254.Formulas.construction.and
  or := ValidatorEnvironmentLabels254.Formulas.construction.or
  all := ValidatorEnvironmentLabels254.Formulas.construction.all
  exs := ValidatorEnvironmentLabels254.Formulas.construction.exs
  allChanges := ValidatorEnvironmentLabels254.nextState
  exsChanges := ValidatorEnvironmentLabels254.nextState
  rel_defined := atom_defined
  nrel_defined := .mk fun e => by simp [blueprint]
  verum_defined := ValidatorEnvironmentLabels254.Formulas.construction.verum_defined
  falsum_defined := ValidatorEnvironmentLabels254.Formulas.construction.falsum_defined
  and_defined := ValidatorEnvironmentLabels254.Formulas.construction.and_defined
  or_defined := ValidatorEnvironmentLabels254.Formulas.construction.or_defined
  all_defined := ValidatorEnvironmentLabels254.Formulas.construction.all_defined
  exs_defined := ValidatorEnvironmentLabels254.Formulas.construction.exs_defined
  allChanges_defined := ValidatorEnvironmentLabels254.nextState_defined
  exChanges_defined := ValidatorEnvironmentLabels254.nextState_defined

noncomputable def encodeState (state source : V) : V :=
  construction.result ℒₛₑₜ state source
noncomputable def encode (free bound fresh source : V) : V :=
  encodeState ?[free,bound,fresh] source

instance encodeState_defined : 𝚺₁-Function₂[V] encodeState via encodeStateDef :=
  construction.result_defined
instance encode_defined : 𝚺₁-Function₄[V] encode via encodeDef :=
  .mk fun e => by simp [encodeDef, encode]
instance encode_delta : 𝚫₁-Function₄[V] encode := encode_defined.graph_delta.to_definable

theorem encode_graph (out F B s p : V) :
    V ⊧/![out,F,B,s,p] encodeDef.val ↔ out=encode F B s p :=
  (encode_defined (V := V)).df ![out,F,B,s,p]

theorem encode_total_unique (F B s p : V) :
    ∃! out : V, V ⊧/![out,F,B,s,p] encodeDef.val := by
  refine ⟨encode F B s p, (encode_graph _ _ _ _ _).mpr rfl, ?_⟩
  intro out h
  exact (encode_graph _ _ _ _ _).mp h

theorem encode_of_not_formula (F B s : V) {p : V} (hp : ¬IsUFormula ℒₛₑₜ p) :
    encode F B s p=0 := construction.result_prop_not _ hp

/-- Source zero is malformed; valid source truth is a distinct code. -/
@[simp] theorem encode_zero (F B s : V) : encode F B s 0=0 :=
  encode_of_not_formula F B s IsUFormula.not_zero
@[simp] theorem encode_verum (F B s : V) : encode F B s (^⊤ : V)=0 := by
  simp [encode, encodeState, construction, ValidatorEnvironmentLabels254.Formulas.construction]
@[simp] theorem encode_falsum (F B s : V) : encode F B s (^⊥ : V)=1 := by
  simp [encode, encodeState, construction, ValidatorEnvironmentLabels254.Formulas.construction]

theorem encode_rel (F B s : V) {arity symbol terms : V}
    (hr : (ℒₛₑₜ).IsRel arity symbol) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    encode F B s (^rel arity symbol terms)=atom ?[F,B,s] arity symbol terms := by
  simp [encode, encodeState, construction, hr, ht]
theorem encode_nrel (F B s : V) {arity symbol terms : V}
    (hr : (ℒₛₑₜ).IsRel arity symbol) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    encode F B s (^nrel arity symbol terms)=wim (atom ?[F,B,s] arity symbol terms) 1 := by
  simp [encode, encodeState, construction, hr, ht]
theorem encode_and (F B s : V) {p q : V} (hp : IsUFormula ℒₛₑₜ p)
    (hq : IsUFormula ℒₛₑₜ q) :
    encode F B s (p ^⋏ q)=wim (wim (encode F B s p) (wim (encode F B s q) 1)) 1 := by
  simp [encode, encodeState, construction, ValidatorEnvironmentLabels254.Formulas.construction, hp, hq]
theorem encode_or (F B s : V) {p q : V} (hp : IsUFormula ℒₛₑₜ p)
    (hq : IsUFormula ℒₛₑₜ q) :
    encode F B s (p ^⋎ q)=wim (wim (encode F B s p) 1) (encode F B s q) := by
  simp [encode, encodeState, construction, ValidatorEnvironmentLabels254.Formulas.construction, hp, hq]
theorem encode_all (F B s : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    encode F B s (^∀ p)=wal s (encode F (s∷B) (s+2) p) := by
  simp [encode, encodeState, construction, ValidatorEnvironmentLabels254.Formulas.construction,
    ValidatorEnvironmentLabels254.nextState, hp]
theorem encode_exs (F B s : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    encode F B s (^∃ p)=wim (wal s (wim (encode F (s∷B) (s+2) p) 1)) 1 := by
  simp [encode, encodeState, construction, ValidatorEnvironmentLabels254.Formulas.construction,
    ValidatorEnvironmentLabels254.nextState, hp]

private instance shift_delta : 𝚫₁-Function₁[V] (shift ℒₛₑₜ) :=
  shift.defined.graph_delta.to_definable

theorem atom_shift (F B s : V) {arity symbol terms : V}
    (ht : IsUTermVec ℒₛₑₜ arity terms) :
    atom ?[F,B,s] arity symbol (termShiftVec ℒₛₑₜ arity terms)=
      atom ?[ValidatorEnvironmentLabels254.tail F,B,s] arity symbol terms := by
  simp only [atom, nth_adjoin_zero, nth_adjoin_one,
    ValidatorEnvironmentLabels254.TermLabels.vec_shift F B ht]

/-- Uniform syntax identity. The bound stack and binder stream are unchanged;
only the free environment tails, including below nested quantifiers. -/
theorem encode_shift {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    ∀ F B s : V, encode F B s (shift ℒₛₑₜ p)=
      encode (ValidatorEnvironmentLabels254.tail F) B s p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · unfold ValidatorEnvironmentLabels254.tail; definability
  · intro arity symbol terms hr ht F B s
    rw [shift_rel hr ht, encode_rel F B s hr ht.termShiftVec,
      encode_rel (ValidatorEnvironmentLabels254.tail F) B s hr ht]
    exact atom_shift F B s ht
  · intro arity symbol terms hr ht F B s
    rw [shift_nrel hr ht, encode_nrel F B s hr ht.termShiftVec,
      encode_nrel (ValidatorEnvironmentLabels254.tail F) B s hr ht, atom_shift F B s ht]
  · intro F B s; simp
  · intro F B s; simp
  · intro p q hp hq ihp ihq F B s
    rw [shift_and hp hq, encode_and F B s hp.shift hq.shift,
      encode_and (ValidatorEnvironmentLabels254.tail F) B s hp hq, ihp, ihq]
  · intro p q hp hq ihp ihq F B s
    rw [shift_or hp hq, encode_or F B s hp.shift hq.shift,
      encode_or (ValidatorEnvironmentLabels254.tail F) B s hp hq, ihp, ihq]
  · intro p hp ih F B s
    rw [shift_all hp, encode_all F B s hp.shift,
      encode_all (ValidatorEnvironmentLabels254.tail F) B s hp, ih]
  · intro p hp ih F B s
    rw [shift_exs hp, encode_exs F B s hp.shift,
      encode_exs (ValidatorEnvironmentLabels254.tail F) B s hp, ih]

end LeanProofs.ZFCinPA.ValidatorFormulaEncoder222
