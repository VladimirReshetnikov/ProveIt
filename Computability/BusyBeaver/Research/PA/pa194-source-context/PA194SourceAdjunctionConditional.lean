import PA194SourceWeakAdjunction
import PA194SourceContext
namespace M6.PA.RelationalSource
open LO LO.FirstOrder
namespace ND
abbrev Term := Semiterm language Nat 0
abbrev Form := Proposition language
def mem (a x : Semiterm language Nat n) : Semiproposition language n := .rel .mem ![x,a]
def eq (x y : Semiterm language Nat n) : Semiproposition language n := .rel .eq ![x,y]
def property (a b x : Semiterm language Nat n) := Semiformula.or (mem a x) (eq x b)
def separationInstance (a b w c : Semiterm language Nat n) : Semiproposition language n :=
  .all (sourceIff (mem (Rew.bShift c) (.bvar 0))
    (.and (mem (Rew.bShift w) (.bvar 0)) (property (Rew.bShift a) (Rew.bShift b) (.bvar 0))))
def adjunctionInstance (a b c : Semiterm language Nat n) : Semiproposition language n :=
  .all (sourceIff (mem (Rew.bShift c) (.bvar 0)) (property (Rew.bShift a) (Rew.bShift b) (.bvar 0)))
def separationAll (a b : Semiterm language Nat n) : Semiproposition language n :=
  .all (.exs (separationInstance (Rew.bShift (Rew.bShift a)) (Rew.bShift (Rew.bShift b)) (.bvar 1) (.bvar 0)))
def adjunctionExists (a b : Semiterm language Nat n) : Semiproposition language n :=
  .exs (adjunctionInstance (Rew.bShift a) (Rew.bShift b) (.bvar 0))
def adjunctionAxioms (a b : Term) : List Form :=
  [weakAdjunctionFormula,separationAll a b,reflexivityFormula,symmetryFormula,congruenceFormula]
end ND
def adjunctionFormula : Proposition language :=
  .all (.all (.exs (.all (sourceIff (memAtom 1 0) (.or (memAtom 3 0) (eqAtom 0 2))))))
def adjunctionProperty : Semiproposition language 1 :=
  .or (ND.mem (.fvar 0) (.bvar 0)) (ND.eq (.bvar 0) (.fvar 1))
def adjunctionEnvironment (lo i : Nat) : Nat := if i=0 then lo else if i=1 then lo+1 else 0
end M6.PA.RelationalSource

namespace PA194Logic.Relational.Source
open LO LO.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA194Logic PA194Logic.Relational

def adjunctionPremises (lo z : Nat) (hlo : 0 < lo) (hz : lo+6 < z)
    (p : Proposition language) (hp : p ∈ ND.adjunctionAxioms (.fvar 0) (.fvar 1)) :
    Proof (code p (adjunctionEnvironment lo) (lo+2) z) := by
  by_cases hw : p = weakAdjunctionFormula
  · subst p; exact weakAdjunctionSupplier _ _ _ (by omega)
  by_cases hs : p = ND.separationAll (.fvar 0) (.fvar 1)
  · subst p
    have sep := separationSupplier adjunctionProperty (adjunctionEnvironment lo) (lo+2) z
      (by omega) (by intro i; simp [adjunctionEnvironment]; split <;> (try split) <;> omega)
      (by simp [adjunctionProperty,ND.mem,ND.eq,depth]; omega)
    exact sep
  by_cases hr : p = reflexivityFormula
  · subst p; exact reflexivitySupplier _ _ _
  by_cases hy : p = symmetryFormula
  · subst p; exact symmetrySupplier _ _ _
  by_cases hc : p = congruenceFormula
  · subst p; exact congruenceSupplier _ _ _ (by omega)
  exact False.elim (by simpa [ND.adjunctionAxioms,hw,hs,hr,hy,hc] using hp)
noncomputable def adjunctionSupplierConditional (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo)
    (hz : lo+6 < z)
    (d : SourceLK (((ND.adjunctionAxioms (.fvar 0) (.fvar 1)).map Semiformula.neg : Multiset _) + ⦃ND.adjunctionExists (.fvar 0) (.fvar 1)⦄))
    (hbudget : lo+2+lkBudget d ≤ z) : Proof (code adjunctionFormula f lo z) := by
  let p := compileContext (ND.adjunctionAxioms (.fvar 0) (.fvar 1))
    (ND.adjunctionExists (.fvar 0) (.fvar 1)) d (adjunctionEnvironment lo) (lo+2) z
    (by omega) (by intro i; simp [adjunctionEnvironment]; split <;> (try split) <;> omega)
    hbudget (adjunctionPremises lo z hlo hz)
  exact .all lo (.all (lo+1) p)
#print axioms adjunctionPremises
#print axioms adjunctionSupplierConditional
end PA194Logic.Relational.Source
