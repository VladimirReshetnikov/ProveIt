import ConPADerivationRefined
import ConPADerivationValidity
import PA194ModelSimNegation

/-! The validity-only cut interface implies the derivation-premise interface. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace ConPA.Sequent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {Q : Quant V} {N : Tr V} {T : Theory L} [T.Δ₁]

def CutPremise.Sim.ofValidity (S : CutValidity.Sim Q N T) : CutPremise.Sim Q N T where
  bot := S.bot
  bound := S.bound
  Adm := S.Adm
  adm_definable := S.adm_definable
  push := S.push
  pop := S.pop
  eig := S.eig
  admAnd := S.admAnd
  admOr := S.admOr
  admAll := S.admAll
  admExs := S.admExs
  admWk := S.admWk
  admShift := S.admShift
  admCut := S.admCut
  ruleAxL := S.ruleAxL
  ruleVerum := S.ruleVerum
  ruleAnd := S.ruleAnd
  ruleOr := S.ruleOr
  ruleAllShift := S.ruleAllShift
  ruleAllFresh := S.ruleAllFresh
  ruleAll := S.ruleAll
  ruleExs := S.ruleExs
  ruleShift := S.ruleShift
  ruleCut := by
    intro e s p d₁ d₂ he ha hs hd
    exact S.ruleCut e s p d₁ d₂ he ha hs ((IsFormulaSet.insert_iff.mp hd.isFormulaSet).1.isUFormula)
  ruleAxm := S.ruleAxm

#print axioms CutPremise.Sim.ofValidity
end model
end ConPA.Sequent
