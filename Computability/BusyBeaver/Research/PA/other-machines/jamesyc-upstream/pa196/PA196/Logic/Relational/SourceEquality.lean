module
public import PA196.Logic.Relational.SourceLK
public import M6PA.Calibration.RelationalSourceEquality
@[expose] public section

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA196.Logic PA196.Logic.Relational

def reflexivitySupplier (f : Nat → Nat) (lo z : Nat) :
    Proof (code reflexivityFormula f lo z) :=
  .all lo (neighborhoodReflexivity lo z)

def symmetrySupplier (f : Nat → Nat) (lo z : Nat) :
    Proof (code symmetryFormula f lo z) :=
  .all lo (.all (lo+1) (implicationCompose
    (doubleNegationElimination (neighborhoodEquality lo (lo+1) z))
    (neighborhoodSymmetry lo (lo+1) z)))

def transitivitySupplier (f : Nat → Nat) (lo z : Nat) :
    Proof (code transitivityFormula f lo z) := by
  let a := neighborhoodEquality lo (lo+1) z
  let b := neighborhoodEquality (lo+1) (lo+1+1) z
  let c := neighborhoodEquality lo (lo+1+1) z
  let h : Bi (wim (wn (wn a)) (wim (wn (wn b)) c)) (wim a (wim b c)) :=
    (Bi.doubleNeg a).symm.imp ((Bi.doubleNeg b).symm.imp (Bi.refl c))
  exact .all lo (.all (lo+1) (.all (lo+1+1)
    (.mp (neighborhoodTransitivity lo (lo+1) (lo+1+1) z) h.2)))

def congruenceSupplier (f : Nat → Nat) (lo z : Nat) (hz : lo+3 < z) :
    Proof (code congruenceFormula f lo z) := by
  let a := neighborhoodEquality lo (lo+1+1) z
  let b := neighborhoodEquality (lo+1) (lo+1+1+1) z
  let c := wel (lo+1) lo
  let d := wel (lo+1+1+1) (lo+1+1)
  let h : Bi (wim (wn (wn a)) (wim (wn (wn b)) (wim (wn (wn c)) d)))
      (wim a (wim b (wim c d))) :=
    (Bi.doubleNeg a).symm.imp ((Bi.doubleNeg b).symm.imp
      ((Bi.doubleNeg c).symm.imp (Bi.refl d)))
  exact .all lo (.all (lo+1) (.all (lo+1+1) (.all (lo+1+1+1)
    (.mp (neighborhoodBothCongruence lo (lo+1+1) (lo+1) (lo+1+1+1) z
      (by omega) (by omega) (by omega) (by omega)) h.2))))

def irSupplier (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo) (hz : lo < z) :
    Proof (code irFormula f lo z) := by
  let raw : Proof (wal 0 (wn 1)) := .all 0 (identity 1)
  let ha := relationalUniversalAlpha (.neg (.mem 0 0)) z 0 lo (by omega)
    (by simp [M6.PA.NativeCalculus.Named.names]; omega) (by omega) (by omega) rfl
    (by simp [M6.PA.NativeCalculus.Named.names]; omega)
  change Proof (wal lo (wn (wel lo lo)))
  simpa only [M6.PA.NativeCalculus.Named.replace,relationalCode,renameLabel,ite_true] using PA196.Logic.Derivation.mp raw ha.1

#print axioms reflexivitySupplier
#print axioms symmetrySupplier
#print axioms transitivitySupplier
#print axioms congruenceSupplier
#print axioms irSupplier
end PA196.Logic.Relational.Source

