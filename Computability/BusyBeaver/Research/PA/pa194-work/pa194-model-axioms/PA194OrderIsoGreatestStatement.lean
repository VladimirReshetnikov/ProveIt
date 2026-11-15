import PA194OrderIsoExtrema
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def greatestImageAxioms : List Form :=
  [reflexivityFormula, symmetryFormula, congruenceFormula, transitivityFormula]

def greatestImageStatement : Form :=
  orderBijection (.fvar 0) (.fvar 1) (.fvar 2) 🡒
  Ordinal.greatest (.fvar 1) (.fvar 3) 🡒
  edge (.fvar 0) (.fvar 3) (.fvar 4) 🡒 Ordinal.greatest (.fvar 2) (.fvar 4)

def greatestImageStatementProof : ND.Proof greatestImageAxioms greatestImageStatement := by
  let j : Form := orderBijection (.fvar 0) (.fvar 1) (.fvar 2)
  let k : Form := Ordinal.greatest (.fvar 1) (.fvar 3)
  let e : Form := edge (.fvar 0) (.fvar 3) (.fvar 4)
  let Γ : List Form := e :: k :: j :: greatestImageAxioms
  have E : FormulaEquality Γ := ⟨⟨assumption (by simp [Γ,greatestImageAxioms]),
    assumption (by simp [Γ,greatestImageAxioms]), assumption (by simp [Γ,greatestImageAxioms])⟩,
    assumption (by simp [Γ,greatestImageAxioms])⟩
  have hj : ND.Proof Γ j := assumption (by simp [Γ])
  have hk : ND.Proof Γ k := assumption (by simp [Γ])
  have he : ND.Proof Γ e := assumption (by simp [Γ])
  have out := greatestImage E 0 1 2 3 4 hj hk he
  have h := impIntro (impIntro (impIntro out))
  convert h using 1 <;> (try rfl)

def greatestImageStatementDerivation : LO.FirstOrder.Derivation
    (greatestImageAxioms.map Semiformula.neg ++ [greatestImageStatement]) :=
  greatestImageStatementProof.contra (by simp [ND.Proof])

#print axioms greatestImageStatementProof
#print axioms greatestImageStatementDerivation
end M6.PA.RelationalSource.PairGraph
