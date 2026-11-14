import PA194RelationalEncoding
import M6.Logic.NativeDecode

/-! A concrete failure of naive unrestricted semantic correspondence for the
existing relational numeric encoding and the pinned total native decoder. -/
namespace PA194SemanticCollision
open M6.PA.NativeCalculus

def alwaysRelated (_ _ : Unit) : Prop := True
def assignment (_ : Nat) : Unit := ()
def source : Named := .imp .truth (.mem 0 0)

theorem source_true : source.eval alwaysRelated Eq assignment := by
  simp [source,Named.eval,alwaysRelated]

theorem numeric_collision (z : Nat) :
    PA194Logic.Relational.relationalCode z source = M6.PA.NativeCalculus.wn 0 := by
  simp only [source, PA194Logic.Relational.relationalCode, PA194Logic.wim, PA194Logic.wel,
    M6.PA.NativeCalculus.wn, M6.PA.NativeCalculus.wim, M6.Source.Cantor.implication]
  rfl

theorem decoded_translation_false (z : Nat) :
    ¬ (NumericDecode.decode (PA194Logic.Relational.relationalCode z source)).eval
      alwaysRelated Eq assignment := by
  rw [numeric_collision,NumericDecode.decode_neg,NumericDecode.decode_zero]
  simp [Named.eval]

#print axioms source_true
#print axioms numeric_collision
#print axioms decoded_translation_false
end PA194SemanticCollision
