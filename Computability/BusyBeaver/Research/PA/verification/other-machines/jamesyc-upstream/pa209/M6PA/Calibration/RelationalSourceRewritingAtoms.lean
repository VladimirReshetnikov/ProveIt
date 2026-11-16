module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceND
@[expose] public section
/-! Explicit arity-two vector normalization for literal source atoms. These
are syntax equalities, not logical or semantic axiom additions. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder

@[simp] theorem app_eq_rewAux {n m : Nat} (ω : Rew language Nat n Nat m)
    (p : Semiproposition language n) :
    Rewriting.app (F := Semiproposition language) (G := Semiproposition language) ω p =
      Semiformula.rewAux ω p := rfl

@[simp] theorem substRel2 {n m : Nat} (r : language.Rel 2)
    (a b : Semiterm language Nat n) (v : Fin n → Semiterm language Nat m) :
    (Semiformula.rel r ![a,b] : Semiproposition language n) ⇜ v =
      Semiformula.rel r ![Rew.subst v a,Rew.subst v b] := by
  change Semiformula.rel _ _ = Semiformula.rel _ _
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

@[simp] theorem substNRel2 {n m : Nat} (r : language.Rel 2)
    (a b : Semiterm language Nat n) (v : Fin n → Semiterm language Nat m) :
    (Semiformula.nrel r ![a,b] : Semiproposition language n) ⇜ v =
      Semiformula.nrel r ![Rew.subst v a,Rew.subst v b] := by
  change Semiformula.nrel _ _ = Semiformula.nrel _ _
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

@[simp] theorem appRel2 {n m : Nat} (ω : Rew language Nat n Nat m)
    (r : language.Rel 2) (a b : Semiterm language Nat n) :
    Rewriting.app (F := Semiproposition language) (G := Semiproposition language) ω
      (Semiformula.rel r ![a,b]) = Semiformula.rel r ![ω a,ω b] := by
  change Semiformula.rel _ _ = Semiformula.rel _ _
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

@[simp] theorem appNRel2 {n m : Nat} (ω : Rew language Nat n Nat m)
    (r : language.Rel 2) (a b : Semiterm language Nat n) :
    Rewriting.app (F := Semiproposition language) (G := Semiproposition language) ω
      (Semiformula.nrel r ![a,b]) = Semiformula.nrel r ![ω a,ω b] := by
  change Semiformula.nrel _ _ = Semiformula.nrel _ _
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

#print axioms substRel2
#print axioms substNRel2
end M6.PA.RelationalSource

