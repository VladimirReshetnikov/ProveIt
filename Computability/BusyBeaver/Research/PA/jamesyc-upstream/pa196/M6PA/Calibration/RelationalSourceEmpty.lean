module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceEquality
@[expose] public section

/-! A concrete nonlogical finite-set axiom supplier: empty-set existence,
constructed from the exact actual pointed bundle, not assumed from a theory
interpretation. Output-name relocation is a finite actual-basis alpha proof. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder NativeCalculus NativeCalculus.ActualBasis

def emptyFormula : Proposition language := .exs (.all (notMemAtom 1 0))

def emptyAt (b z : Nat) : Proof
    (wex (relationalCode z (paddedProperty 0 b z (.mem 0 0)))
      (wal b (wn (wel (relationalCode z (paddedProperty 0 b z (.mem 0 0))) b)))) := by
  let c := relationalCode z (paddedProperty 0 b z (.mem 0 0))
  let a := wim (wel 0 b) (wim 1 (wel c b))
  let bb := wn (wel c b)
  let cc := wim 1 (wel c b)
  let proj : Proof (wim (wa a bb) bb) :=
    (Context.andRight (Context.assumption (Γ := [wa a bb]) (a := wa a bb) (by simp))).deduction.empty
  let h : Context [wa (wal b (wa a bb)) cc] (wa (wal b (wa a bb)) cc) :=
    .assumption (by simp)
  let pr : Proof (wim (wa (wal b (wa a bb)) cc) (wal b bb)) :=
    (h.andLeft.forallMP b (.closed (.all b proj))).deduction.empty
  let raw := pointedPropertyProof 0 b z (.mem 0 0)
  exact .mp raw (existentialMonotonicity c pr)

def emptySupplier (f : Nat → Nat) (lo z : Nat) (hz : lo+1 < z) :
    Proof (code emptyFormula f lo z) := by
  let b := lo+1
  let c := relationalCode z (paddedProperty 0 b z (.mem 0 0))
  have hc : z < c := (paddedCode_bounds 0 b z (.mem 0 0)).2.2
  let body : Named := .all b (.neg (.mem c b))
  let ha := relationalUniversalAlpha (.neg body) z c lo (by omega)
    (by simp [body,Named.names]; omega) (by omega) (by omega)
    (by simp [body,Named.binders]; omega)
    (by simp [body,Named.names]; dsimp [b]; omega)
  let hx := (Bi.neg ha).1
  change Proof (wex lo (wal (lo+1) (wn (wel lo (lo+1)))))
  simpa only [body,Named.replace,relationalCode,renameLabel,ite_true,b,wex,
    if_neg (show b ≠ c by omega)] using Proof.mp (emptyAt b z) hx

#print axioms emptyAt
#print axioms emptySupplier
end M6.PA.RelationalSource

