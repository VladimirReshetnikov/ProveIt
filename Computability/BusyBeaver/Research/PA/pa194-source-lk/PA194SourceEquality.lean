import PA194SourceLK
namespace M6.PA.RelationalSource
open LO LO.FirstOrder
def eqAtom {n : Nat} (a b : Fin n) : Semiformula language Nat n :=
  .rel .eq ![.bvar a,.bvar b]
def notEqAtom {n : Nat} (a b : Fin n) : Semiformula language Nat n :=
  .nrel .eq ![.bvar a,.bvar b]
def memAtom {n : Nat} (a b : Fin n) : Semiformula language Nat n :=
  .rel .mem ![.bvar b,.bvar a]
def notMemAtom {n : Nat} (a b : Fin n) : Semiformula language Nat n :=
  .nrel .mem ![.bvar b,.bvar a]

def reflexivityFormula : Proposition language := .all (eqAtom 0 0)
def symmetryFormula : Proposition language :=
  .all (.all (.or (notEqAtom 1 0) (eqAtom 0 1)))
def transitivityFormula : Proposition language :=
  .all (.all (.all (.or (notEqAtom 2 1) (.or (notEqAtom 1 0) (eqAtom 2 0)))))
def congruenceFormula : Proposition language :=
  .all (.all (.all (.all (.or (notEqAtom 3 1)
    (.or (notEqAtom 2 0) (.or (notMemAtom 2 3) (memAtom 0 1)))))))
def irFormula : Proposition language := .all (notMemAtom 0 0)


end M6.PA.RelationalSource

namespace PA194Logic.Relational.Source
open LO LO.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA194Logic PA194Logic.Relational

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
  simpa only [M6.PA.NativeCalculus.Named.replace,relationalCode,renameLabel,ite_true] using PA194DerivationCompiler.Derivation.mp raw ha.1

#print axioms reflexivitySupplier
#print axioms symmetrySupplier
#print axioms transitivitySupplier
#print axioms congruenceSupplier
#print axioms irSupplier
end PA194Logic.Relational.Source

