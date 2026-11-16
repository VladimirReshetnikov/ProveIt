module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionBijectionEntries
public import M6PA.Calibration.RelationalIsoCompositionBijectionLaws
public import M6PA.Calibration.RelationalIsoCompositionBijectionTotal
@[expose] public section

/-! All seven order-bijection clauses for the actual constructed composition. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionBijection {Γ : List Form} (E : FormulaEquality Γ) (g h a b c k : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hh : ND.Proof Γ (orderBijection (.fvar h) (.fvar b) (.fvar c)))
    (hk : ND.Proof Γ (compositionPrefix (.fvar g) (.fvar h) (.fvar a) (.fvar k))) :
    ND.Proof Γ (orderBijection (.fvar k) (.fvar a) (.fvar c)) := by
  have tg := andLeft (andRight hg)
  have th := andLeft (andRight hh)
  have rg := andLeft (andRight (andRight (andRight hg)))
  have rh := andLeft (andRight (andRight (andRight hh)))
  have fg := andLeft (andRight (andRight (andRight (andRight hg))))
  have fh := andLeft (andRight (andRight (andRight (andRight hh))))
  have ig := andLeft (andRight (andRight (andRight (andRight (andRight hg)))))
  have ih := andLeft (andRight (andRight (andRight (andRight (andRight hh)))))
  have og := andRight (andRight (andRight (andRight (andRight (andRight hg)))))
  have oh := andRight (andRight (andRight (andRight (andRight (andRight hh)))))
  have cc := andLeft (andRight hk)
  have cv := andRight (andRight hk)
  exact andIntro (compositionBijectionEntries g h a b c k th (andLeft hk))
    (andIntro (compositionTyped g h a b c k tg th cc)
      (andIntro (compositionLeftTotal g h a k cv)
        (andIntro (compositionRightTotal E g h a b c k tg th fg fh rg rh cv)
          (andIntro (compositionFunctional E g h a k fg fh cc)
            (andIntro (compositionInjective E g h a k ig ih cc) (compositionOrder g h a k og oh cc))))))

#print axioms compositionBijection
end M6.PA.RelationalSource.PairGraph
