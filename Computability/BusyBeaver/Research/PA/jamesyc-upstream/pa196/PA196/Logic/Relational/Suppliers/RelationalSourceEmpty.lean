module
public import M6PA.Calibration.RelationalSourceEmpty
public import PA196.Logic.Relational.Encoding
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceIntersection
@[expose] public section

/-! New PA196 certificates for the original finite source proof templates.
Only native supplier outputs are retargeted; source formulas, Foundation LK
derivations and numeric resource bounds are imported unchanged. -/
noncomputable section

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder  PA196.Logic.Relational

def emptyAt (b z : Nat) : PA196.Logic.Derivation
    (wex (PA196.Logic.Relational.relationalCode z (paddedProperty 0 b z (.mem 0 0)))
      (wal b (wn (wel (PA196.Logic.Relational.relationalCode z (paddedProperty 0 b z (.mem 0 0))) b)))) := by
  let c := PA196.Logic.Relational.relationalCode z (paddedProperty 0 b z (.mem 0 0))
  let a := wim (wel 0 b) (wim 1 (wel c b))
  let bb := wn (wel c b)
  let cc := wim 1 (wel c b)
  let proj : PA196.Logic.Derivation (wim (wa a bb) bb) :=
    (Context.andRight (Context.assumption (Γ := [wa a bb]) (a := wa a bb) (by simp))).deduction.empty
  let h : Context [wa (wal b (wa a bb)) cc] (wa (wal b (wa a bb)) cc) :=
    .assumption (by simp)
  let pr : PA196.Logic.Derivation (wim (wa (wal b (wa a bb)) cc) (wal b bb)) :=
    (h.andLeft.forallMP b (.closed (.all b proj))).deduction.empty
  let raw := pointedPropertyProof 0 b z (.mem 0 0)
  exact .mp raw (existentialMonotonicity c pr)
#print axioms emptyAt
end PA196.Logic.Relational.Source

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder  PA196.Logic.Relational

def emptySupplier (f : Nat → Nat) (lo z : Nat) (hz : lo+1 < z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code emptyFormula f lo z) := by
  let b := lo+1
  let c := PA196.Logic.Relational.relationalCode z (paddedProperty 0 b z (.mem 0 0))
  have hc : z < c := (paddedCode_bounds 0 b z (.mem 0 0)).2.2
  let body : Named := .all b (.neg (.mem c b))
  let ha := relationalUniversalAlpha (.neg body) z c lo (by omega)
    (by simp [body,M6.PA.NativeCalculus.Named.names]; omega) (by omega) (by omega)
    (by simp [body,M6.PA.NativeCalculus.Named.binders]; omega)
    (by simp [body,M6.PA.NativeCalculus.Named.names]; dsimp [b]; omega)
  let hx := (Bi.neg ha).1
  change PA196.Logic.Derivation (wex lo (wal (lo+1) (wn (wel lo (lo+1)))))
  simpa only [body,M6.PA.NativeCalculus.Named.replace,PA196.Logic.Relational.relationalCode,renameLabel,ite_true,b,wex,
    if_neg (show b ≠ c by omega)] using PA196.Logic.Derivation.mp (PA196.Logic.Relational.Source.emptyAt b z) hx
#print axioms emptySupplier
end PA196.Logic.Relational.Source
end
