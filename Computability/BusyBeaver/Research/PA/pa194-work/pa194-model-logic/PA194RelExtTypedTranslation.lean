import PA194RelationalEncoding
import PA194SourceSyntax
import Foundation.FirstOrder.Basic.Eq

/-! Exact standard typed-Foundation binary membership equality-axiom translation. -/
namespace PA194RelExtTypedTranslation
open LO LO.FirstOrder M6.PA.RelationalSource M6.PA.NativeCalculus
local instance sourceRelExtLanguageEq : Language.Eq M6.PA.RelationalSource.language := ⟨Relation.eq⟩

def sourceRelExt : Sentence M6.PA.RelationalSource.language :=
  Theory.Eq.relExt (L := M6.PA.RelationalSource.language) Relation.mem

def expectedNamed (lo : Nat) : Named :=
  let x₀ := lo
  let x₁ := lo+1
  let x₂ := (lo+1)+1
  let x₃ := ((lo+1)+1)+1
  .all x₀ (.all x₁ (.all x₂ (.all x₃
    (.imp (.neg (.imp (.neg (.neg (.eq x₃ x₁)))
      (.imp (.neg (.neg (.eq x₂ x₀))) (.mem 0 0))))
      (.imp (.neg (.neg (.mem x₂ x₃))) (.mem x₀ x₁))))))

theorem relExt_toNamed (lo : Nat) :
    M6.PA.RelationalSource.toNamed sourceRelExt Fin.elim0 Empty.elim lo = expectedNamed lo := by
  rfl

theorem relExt_relationalCode (lo z : Nat) :
    PA194Logic.Relational.relationalCode z
      (M6.PA.RelationalSource.toNamed sourceRelExt Fin.elim0 Empty.elim lo) =
    PA194Logic.Relational.relationalCode z (expectedNamed lo) := by
  rw [relExt_toNamed]

def expectedNumeric (lo z : Nat) : Nat :=
  let x₀ := lo
  let x₁ := lo+1
  let x₂ := (lo+1)+1
  let x₃ := ((lo+1)+1)+1
  let e₁ := PA194Logic.neighborhood x₃ x₁ z
  let e₂ := PA194Logic.neighborhood x₂ x₀ z
  let old := PA194Logic.wel x₂ x₃
  let new := PA194Logic.wel x₀ x₁
  let antecedent := PA194Logic.wn (PA194Logic.wim (PA194Logic.wn (PA194Logic.wn e₁))
    (PA194Logic.wim (PA194Logic.wn (PA194Logic.wn e₂)) (PA194Logic.wel 0 0)))
  PA194Logic.wal x₀ (PA194Logic.wal x₁ (PA194Logic.wal x₂ (PA194Logic.wal x₃
    (PA194Logic.wim antecedent (PA194Logic.wim (PA194Logic.wn (PA194Logic.wn old)) new)))))

theorem relExt_numeric_expanded (lo z : Nat) :
    PA194Logic.Relational.relationalCode z
      (M6.PA.RelationalSource.toNamed sourceRelExt Fin.elim0 Empty.elim lo) = expectedNumeric lo z := by
  rw [relExt_toNamed]
  rfl

#print axioms relExt_numeric_expanded
#print axioms relExt_toNamed
#print axioms relExt_relationalCode
end PA194RelExtTypedTranslation
