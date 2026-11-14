import PA194SourceEquality
import PA194RelationalPointed
namespace M6.PA.RelationalSource
open LO LO.FirstOrder
def emptyFormula : Proposition language := .exs (.all (notMemAtom 1 0))
end M6.PA.RelationalSource
noncomputable section

namespace PA194Logic.Relational.Source
open LO LO.FirstOrder
open M6.PA.RelationalSource
open M6.PA.RelationalSource
open PA194Logic PA194Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open LO LO.FirstOrder  PA194Logic.Relational

def emptyAt (b z : Nat) : PA194Logic.Derivation
    (wex (PA194Logic.Relational.relationalCode z (paddedProperty 0 b z (.mem 0 0)))
      (wal b (wn (wel (PA194Logic.Relational.relationalCode z (paddedProperty 0 b z (.mem 0 0))) b)))) := by
  let c := PA194Logic.Relational.relationalCode z (paddedProperty 0 b z (.mem 0 0))
  let a := wim (wel 0 b) (wim 1 (wel c b))
  let bb := wn (wel c b)
  let cc := wim 1 (wel c b)
  let proj : PA194Logic.Derivation (wim (wa a bb) bb) :=
    (Context.andRight (Context.assumption (Γ := [wa a bb]) (a := wa a bb) (by simp))).deduction.empty
  let h : Context [wa (wal b (wa a bb)) cc] (wa (wal b (wa a bb)) cc) :=
    .assumption (by simp)
  let pr : PA194Logic.Derivation (wim (wa (wal b (wa a bb)) cc) (wal b bb)) :=
    (h.andLeft.forallMP b (.closed (.all b proj))).deduction.empty
  let raw := pointedPropertyProof 0 b z (.mem 0 0)
  exact .mp raw (existentialMonotonicity c pr)
#print axioms emptyAt
end PA194Logic.Relational.Source

namespace PA194Logic.Relational.Source
open LO LO.FirstOrder
open M6.PA.RelationalSource
open M6.PA.RelationalSource
open PA194Logic PA194Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open LO LO.FirstOrder  PA194Logic.Relational

def emptySupplier (f : Nat → Nat) (lo z : Nat) (hz : lo+1 < z) :
    PA194Logic.Derivation (PA194Logic.Relational.Source.code emptyFormula f lo z) := by
  let b := lo+1
  let c := PA194Logic.Relational.relationalCode z (paddedProperty 0 b z (.mem 0 0))
  have hc : z < c := (paddedCode_bounds 0 b z (.mem 0 0)).2.2
  let body : Named := .all b (.neg (.mem c b))
  let ha := relationalUniversalAlpha (.neg body) z c lo (by omega)
    (by simp [body,M6.PA.NativeCalculus.Named.names]; omega) (by omega) (by omega)
    (by simp [body,M6.PA.NativeCalculus.Named.binders]; omega)
    (by simp [body,M6.PA.NativeCalculus.Named.names]; dsimp [b]; omega)
  let hx := (Bi.neg ha).1
  change PA194Logic.Derivation (wex lo (wal (lo+1) (wn (wel lo (lo+1)))))
  simpa only [body,M6.PA.NativeCalculus.Named.replace,PA194Logic.Relational.relationalCode,renameLabel,ite_true,b,wex,
    if_neg (show b ≠ c by omega)] using PA194DerivationCompiler.Derivation.mp (PA194Logic.Relational.Source.emptyAt b z) hx
#print axioms emptySupplier
end PA194Logic.Relational.Source
end
