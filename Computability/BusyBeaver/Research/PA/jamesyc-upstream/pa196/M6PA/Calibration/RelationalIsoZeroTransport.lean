module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoZeroWitness
@[expose] public section

/-! Total typed graphs transport emptiness in both directions. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def zeroByRightTotal {Γ : List Form} (g a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hr : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b))) :
    ND.Proof Γ (Ordinal.zero (.fvar b)) := by
  apply allIntro
  have hn : ND.Proof (shifted Γ) (∼mem (.fvar (b+1)) (.fvar 0)) := by
    apply byContradiction
    let d : Form := ∼∼mem (.fvar (b+1)) (.fvar 0)
    have hm : ND.Proof (d :: shifted Γ) (mem (.fvar (b+1)) (.fvar 0)) := by
      simpa [d] using (assumption (Γ := d :: shifted Γ) (p := d) (by simp))
    exact rightTotalZeroFalse (g+1) (a+1) (b+1) 0
      (up (Ordinal.zeroShift a hz) d) (up (orderTypedShift g a b ht) d)
      (up (orderRightShift g b hr) d) hm
  convert hn using 1 <;> isoSyntax

def zeroByLeftTotal {Γ : List Form} (g a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar b)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hr : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a))) :
    ND.Proof Γ (Ordinal.zero (.fvar a)) := by
  apply allIntro
  have hn : ND.Proof (shifted Γ) (∼mem (.fvar (a+1)) (.fvar 0)) := by
    apply byContradiction
    let d : Form := ∼∼mem (.fvar (a+1)) (.fvar 0)
    have hm : ND.Proof (d :: shifted Γ) (mem (.fvar (a+1)) (.fvar 0)) := by
      simpa [d] using (assumption (Γ := d :: shifted Γ) (p := d) (by simp))
    exact leftTotalZeroFalse (g+1) (a+1) (b+1) 0
      (up (Ordinal.zeroShift b hz) d) (up (orderTypedShift g a b ht) d)
      (up (orderLeftShift g a hr) d) hm
  convert hn using 1 <;> isoSyntax

#print axioms zeroByRightTotal
#print axioms zeroByLeftTotal
end M6.PA.RelationalSource.PairGraph
