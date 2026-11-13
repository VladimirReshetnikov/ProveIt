module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseBijectionEntries
public import M6PA.Calibration.RelationalIsoInverseBijectionLaws
public import M6PA.Calibration.RelationalIsoInverseBijectionTotal
@[expose] public section

/-! All seven order-bijection clauses for a constructed full inverse prefix. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def inverseBijection {Γ : List Form} (E : FormulaEquality Γ) (g a b h : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hh : ND.Proof Γ (inversePrefix (.fvar g) (.fvar a) (.fvar h))) :
    ND.Proof Γ (orderBijection (.fvar h) (.fvar b) (.fvar a)) := by
  have ht := andLeft (andRight hg)
  have hr := andLeft (andRight (andRight (andRight hg)))
  have hf := andLeft (andRight (andRight (andRight (andRight hg))))
  have hi := andLeft (andRight (andRight (andRight (andRight (andRight hg)))))
  have ho := andRight (andRight (andRight (andRight (andRight (andRight hg)))))
  have hc := andLeft (andRight hh)
  have hv := andRight (andRight hh)
  exact andIntro (inverseBijectionEntries g a b h ht (andLeft hh))
    (andIntro (inverseTyped g a b h ht hc)
      (andIntro (inverseLeftTotal E g a b h ht hf hr hv)
        (andIntro (inverseRightTotal g a h hv)
          (andIntro (inverseFunctional g a h hi hc)
            (andIntro (inverseInjective g a h hf hc) (inverseOrder g a h ho hc))))))

#print axioms inverseBijection
end M6.PA.RelationalSource.PairGraph
