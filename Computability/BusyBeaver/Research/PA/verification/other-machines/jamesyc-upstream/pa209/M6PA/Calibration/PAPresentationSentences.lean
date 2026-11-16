module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationClosure
public import M6PA.Calibration.PAPresentationInductionTheorem
@[expose] public section

/-! Exact sentence-level compatibility, so translated closed Foundation
axioms are not replaced by an informal 'equivalent closure'. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

@[simp] theorem translateRew_emb {n : Nat} :
    translateRew (Rew.emb : Rew ℒₒᵣ Empty n Nat n) =
      (Rew.emb : Rew language Empty n Nat n) := by
  apply Rew.ext
  · intro i; rfl
  · intro i; exact Empty.elim i

theorem formula_emb {n : Nat} (p : ArithmeticSemisentence n) :
    formula (Semiformula.rewAux (Rew.emb : Rew ℒₒᵣ Empty n Nat n) p) =
      Semiformula.rewAux (Rew.emb : Rew language Empty n Nat n) (formula p) := by
  rw [formula_rew,translateRew_emb]

theorem formula_univCl (p : ArithmeticProposition) :
    formula p.univCl = (formula p).univCl := by
  apply (Semiformula.coe_inj _ _).mp
  change Semiformula.rewAux (Rew.emb : Rew language Empty 0 Nat 0) (formula p.univCl) = _
  rw [←formula_emb]
  change formula (Rewriting.emb p.univCl : ArithmeticProposition) = _
  rw [Semiformula.coe_univCl_eq_univCl',formula_univCl',Semiformula.coe_univCl_eq_univCl']

def foundationInductionSentenceProof (p : ArithmeticSemiproposition 1) :
    ordinaryPAeq.Proof (formula (Arithmetic.succInd p).univCl) := by
  rw [formula_univCl]
  exact foundationInductionImageProof p

#print axioms formula_univCl
#print axioms foundationInductionSentenceProof
end M6.PA.Presentation
