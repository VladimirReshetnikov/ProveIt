module
public import PA196.Logic.Relational.SourceSeparation
public import M6PA.Calibration.RelationalSourceWeakAdjunction
@[expose] public section

namespace PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)

def weakOutput (a b z : Nat) := relationalCode z (paddedProperty a b z .truth)

def actualWeakAdjunction (a b z : Nat) :
    Proof (wex (weakOutput a b z)
      (wa (wal b (wim (wel a b) (wel (weakOutput a b z) b))) (wel (weakOutput a b z) b))) := by
  let d := weakOutput a b z
  let ma := wel a b
  let md := wel d b
  let clause := wa (wim ma (wim 0 md)) (wim md 0)
  let hma : Context [ma,clause] ma := .assumption (by simp)
  let hcl : Context [ma,clause] clause := .assumption (by simp)
  let proj : Proof (wim clause (wim ma md)) :=
    (Context.mp (.closed truthProof) (.mp hma hcl.andLeft)).deduction.deduction.empty
  let frame : Context [wa (wal b clause) (wim 0 md)]
      (wa (wal b clause) (wim 0 md)) := .assumption (by simp)
  let hp : Context [wa (wal b clause) (wim 0 md)] md := .mp (.closed truthProof) frame.andRight
  let hi := frame.andLeft.forallMP b (.closed (.all b proj))
  let out := (Context.andIntro hi hp).deduction.empty
  exact .mp (pointedPropertyProof a b z .truth) (existentialMonotonicity d out)

def weakAdjunctionAtName (a b c m z : Nat)
    (ha : a < z) (hb : b < z) (hc : c < z) (hm : m < z)
    (hab : a ≠ b) (hma : m ≠ a) (hmb : m ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hcm : c ≠ m) :
    Proof (wex c (wa (wal m (wim (wel a m) (wel c m))) (wel c b))) := by
  let d := weakOutput a b z
  have hd : z < d := (paddedCode_bounds a b z .truth).2.2
  let member := relationalUniversalAlpha (.imp (.mem a b) (.mem d b)) z b m (Ne.symm hmb)
    (by simp [M6.PA.NativeCalculus.Named.names]; omega) (by omega) (by omega) rfl
    (by simp [M6.PA.NativeCalculus.Named.names,hma,hmb]; omega)
  have member' : Bi (wal b (wim (wel a b) (wel d b))) (wal m (wim (wel a m) (wel d m))) := by
    simpa only [M6.PA.NativeCalculus.Named.replace,relationalCode,renameLabel,ite_true,if_neg hab,
      if_neg (show d ≠ b by omega)] using member
  let first := PA196.Logic.Derivation.mp (actualWeakAdjunction a b z) ((member'.and (Bi.refl (wel d b))).exs d).1
  let body : Named := namedAnd (.all m (.imp (.mem a m) (.mem d m))) (.mem d b)
  let output := relationalUniversalAlpha (.neg body) z d c (by omega)
    (by simp [body,namedAnd,M6.PA.NativeCalculus.Named.names]; omega) (by omega) (by omega)
    (by simp [body,namedAnd,M6.PA.NativeCalculus.Named.binders]; omega)
    (by simp [body,namedAnd,M6.PA.NativeCalculus.Named.names,hca,hcb,hcm]; omega)
  simpa only [body,namedAnd,M6.PA.NativeCalculus.Named.replace,relationalCode,renameLabel,ite_true,
    if_neg (show a ≠ d by omega),if_neg (show b ≠ d by omega),if_neg (show m ≠ d by omega),
    wa,wex] using PA196.Logic.Derivation.mp first (Bi.neg output).1
end PA196.Logic.Relational

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA196.Logic PA196.Logic.Relational

def weakAdjunctionSupplier (f : Nat → Nat) (lo z : Nat) (hz : lo+3 < z) :
    Proof (code weakAdjunctionFormula f lo z) := by
  let a := lo
  let b := lo+1
  let c := lo+1+1
  let m := lo+1+1+1
  let raw := weakAdjunctionAtName a b c m z
    (by dsimp [a]; omega) (by dsimp [b]; omega) (by dsimp [c]; omega) (by dsimp [m]; omega)
    (by dsimp [a,b]; omega) (by dsimp [a,m]; omega) (by dsimp [b,m]; omega)
    (by dsimp [a,c]; omega) (by dsimp [b,c]; omega) (by dsimp [c,m]; omega)
  let env : Fin 4 → Nat := Fin.cases m (Fin.cases c (Fin.cases b (Fin.cases a Fin.elim0)))
  let hn := sourceImplyNormalization (memAtom 3 0) (memAtom 1 0) env f (lo+1+1+1+1) z
  have hn' : Bi (relationalCode z (toNamed (sourceImply (memAtom 3 0) (memAtom 1 0))
      env f (lo+1+1+1+1))) (wim (wel a m) (wel c m)) := by
    simp only [toNamed,relationalCode,memAtom,atomNamed,termLabel,Matrix.cons_val_zero,
      Matrix.cons_val_one] at hn
    exact hn
  exact .mp (.all a (.all b raw)) (((((hn'.all m).and (Bi.refl (wel c b))).exs c).all b).all a).2

#print axioms actualWeakAdjunction
#print axioms weakAdjunctionAtName
#print axioms weakAdjunctionSupplier
end PA196.Logic.Relational.Source
