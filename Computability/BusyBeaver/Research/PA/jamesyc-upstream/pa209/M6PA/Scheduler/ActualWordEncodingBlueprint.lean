module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCommandEncodingInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualWordEncodingBlueprint
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCommandEncodingInternal
attribute [local irreducible] spliceGraph

/-- Fold a Foundation HFS vector of command atoms into the exact source
Cantor command-tail encoding. The two coding conventions remain explicit. -/
noncomputable def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “z. z=0”
  adjoin := .mkSigma “z atom xs ih. ∃ tail, !spliceGraph tail atom ih ∧ z=tail+1”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def construction : VecRec.Construction V blueprint where
  nil := fun _ => 0
  adjoin := fun _ atom _ ih => spliceValue atom ih+1
  nil_defined := .mk fun v => by simp [blueprint]
  adjoin_defined := .mk fun v => by simp [blueprint,splice_graph]

noncomputable def encodeValue (xs : V) : V := construction.result ![] xs
noncomputable def encodeGraph : 𝚺ᴬ₁.Semisentence 2 := blueprint.resultDef

@[simp] theorem encode_zero : encodeValue (0 : V)=0 := by simp [encodeValue,construction]
@[simp] theorem encode_adjoin (atom xs : V) :
    encodeValue (atom ∷ xs)=spliceValue atom (encodeValue xs)+1 := by
  simp [encodeValue,construction]

instance encode_defined : 𝚺ᴬ₁-Function₁ (encodeValue : V → V) via encodeGraph :=
  construction.result_defined

theorem encode_graph (z xs : V) : encodeGraph.val.Evalb ![z,xs] ↔ z=encodeValue xs :=
  encode_defined.iff

theorem encode_total_unique (xs : V) : ∃! z,encodeGraph.val.Evalb ![z,xs] :=
  ⟨encodeValue xs,(encode_graph _ _).mpr rfl,fun _ hz => (encode_graph _ _).mp hz⟩

theorem encode_standard (xs : List Nat) :
    encodeValue (ActualWordCoding.encode xs)=M6.Source.CommandAtomEncoding.encodeAtoms xs := by
  induction xs with
  | nil => simp [M6.Source.CommandAtomEncoding.encodeAtoms]
  | cons atom xs ih =>
      rw [ActualWordCoding.encode_cons,encode_adjoin,ih,splice_standard]
      rfl

#print axioms encode_graph
#print axioms encode_standard
end M6.PA.ActualWordEncodingBlueprint

