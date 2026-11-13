module
public import PA196.Logic.Relational.SourceWeakAdjunction
public import PA196.Logic.Relational.SourceContext
public import M6PA.Calibration.RelationalSourceAdjunction
@[expose] public section

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA196.Logic PA196.Logic.Relational

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

def adjunctionSupplier (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo)
    (hz : lo+6 < z) (hbudget : lo+2+lkBudget adjunctionDerivation ≤ z) :
    Proof (code adjunctionFormula f lo z) := by
  let p := compileContext (ND.adjunctionAxioms (.fvar 0) (.fvar 1))
    (ND.adjunctionExists (.fvar 0) (.fvar 1)) adjunctionDerivation (adjunctionEnvironment lo) (lo+2) z
    (by omega) (by intro i; simp [adjunctionEnvironment]; split <;> (try split) <;> omega)
    hbudget (adjunctionPremises lo z hlo hz)
  exact .all lo (.all (lo+1) p)

#print axioms adjunctionPremises
#print axioms adjunctionSupplier
end PA196.Logic.Relational.Source
