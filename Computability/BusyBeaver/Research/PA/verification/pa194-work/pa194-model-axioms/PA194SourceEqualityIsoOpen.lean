import PA194FoundationFormulaCongruence
import PA194OrderIsoRew
import PA194ForwardReflContext
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194SourceEqualityIso
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open M6.PA.RelationalSource.Ordinal

/-- At arbitrary standard free variables, two domain elements equal to the same object are isomorphic. -/
def eqIsoAt {Γ : List Form} (E : FormulaEquality Γ)
    (hr : ND.Proof Γ orderIsoReflexivityStatement) (a b c : Nat) :
    ND.Proof Γ (Ordinal.domain (.fvar b) 🡒 Ordinal.domain (.fvar c) 🡒
      eq (.fvar b) (.fvar a) 🡒 eq (.fvar c) (.fvar a) 🡒 orderIso (.fvar b) (.fvar c)) := by
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  let Δ : List Form := [eq (.fvar c) (.fvar a),eq (.fvar b) (.fvar a),
    Ordinal.domain (.fvar c),Ordinal.domain (.fvar b)] ++ Γ
  change ND.Proof Δ _
  have inc : ∀ p, p ∈ Γ → p ∈ Δ := by intro p hp; simp [Δ,hp]
  have E' := E.weaken inc
  have hr' : ND.Proof Δ orderIsoReflexivityStatement := ND.weaken hr inc
  have hdb : ND.Proof Δ (Ordinal.domain (.fvar b)) := ND.assumption (by simp [Δ])
  have hba : ND.Proof Δ (eq (.fvar b) (.fvar a)) := ND.assumption (by simp [Δ])
  have hca : ND.Proof Δ (eq (.fvar c) (.fvar a)) := ND.assumption (by simp [Δ])
  have hbc : ND.Proof Δ (eq (.fvar b) (.fvar c)) := E'.transitivityOf hba (E'.symmetryOf hca)
  have hrr : ND.Proof Δ (Ordinal.domain (.fvar b) 🡒 orderIso (.fvar b) (.fvar b)) := by
    have h := ND.allElim _ (.fvar b) hr'
    convert h using 1
    change _ = Semiformula.rewAux _ _
    simp only [Semiformula.imp_eq,Semiformula.neg_eq,Semiformula.rewAux]
    all_goals isoSyntax
  have hbb : ND.Proof Δ (orderIso (.fvar b) (.fvar b)) := ND.mp hdb hrr
  let P : Semiproposition language 1 := orderIso (.fvar b) (.bvar 0)
  have hP : ND.Proof Δ (Semiformula.rewAux (Rew.subst ![.fvar b]) P) := by
    have hsyntax : (Semiformula.rewAux (Rew.subst ![.fvar b]) P : Form) = orderIso (.fvar b) (.fvar b) := by
      dsimp only [P]
      rw [orderIso_rew]
      rfl
    exact hbb.cast (congrArg (fun q : Form => q :: Δ.map Semiformula.neg) hsyntax.symm)
  have hout := E'.substituteOne P (.fvar b) (.fvar c) hbc hP
  have hsyntax : (Semiformula.rewAux (Rew.subst ![.fvar c]) P : Form) = orderIso (.fvar b) (.fvar c) := by
    dsimp only [P]
    rw [orderIso_rew]
    rfl
  exact hout.cast (congrArg (fun q : Form => q :: Δ.map Semiformula.neg) hsyntax)

#print axioms eqIsoAt
end PA194SourceEqualityIso
