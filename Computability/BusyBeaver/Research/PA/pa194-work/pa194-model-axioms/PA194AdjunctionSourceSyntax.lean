import PA194FoundationOrdinalInductionUniform
import PA194ModelWeakAdjunctionAxiom
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND
open scoped LO.FirstOrder
open M6.PA.RelationalSource PA194ModelLogic

def swappedAdjunctionProperty : Formula 1 :=
  ND.mem (.fvar 1) (.bvar 0) ⋎ ND.eq (.bvar 0) (.fvar 0)

theorem swapped_separation :
    ND.separationAll (.fvar 1) (.fvar 0) = separationFormula swappedAdjunctionProperty := by
  dsimp [separationFormula, swappedAdjunctionProperty, liftMember, memAtom]
  sourceSyntaxEq

theorem weak_adjunction_syntax :
    (sourceWeakAdjunction : Proposition M6.PA.RelationalSource.language) = weakAdjunctionFormula := by
  change Semiformula.rewAux Rew.emb sourceWeakAdjunction = _
  simp [sourceWeakAdjunction, weakAdjunctionFormula, sourceImply, Semiformula.rewAux,
    Semiformula.neg,memAtom,Function.comp_def]
  finishSourceSyntax

def swappedAdjunctionDerivation : LO.FirstOrder.Derivation
    ((ND.adjunctionAxioms (.fvar 1) (.fvar 0)).map Semiformula.neg ++
      [ND.adjunctionExists (.fvar 1) (.fvar 0)]) := by
  apply (ND.exactAdjunctionFromAxioms (.fvar 1) (.fvar 0)).contra

#print axioms swapped_separation
#print axioms weak_adjunction_syntax
#print axioms swappedAdjunctionDerivation
end M6.PA.RelationalSource.Ordinal
