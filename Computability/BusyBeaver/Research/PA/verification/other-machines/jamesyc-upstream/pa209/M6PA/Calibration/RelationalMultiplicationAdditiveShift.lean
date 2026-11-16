module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationFrame
public import M6PA.Calibration.RelationalAdditionApplications
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult addPrefix mulPrefix

def mulAddOutputConclusionShift {Γ : List Form} (base : Nat)
    (h : ND.Proof Γ (addOutputConclusion base)) :
    ND.Proof (shifted Γ) (addOutputConclusion (base+1)) := by
  convert shiftProof h using 1 <;>
    (simp only [addOutputConclusion,addOutput]; mulCompactSyntax)

#print axioms mulAddOutputConclusionShift
end M6.PA.RelationalSource.PairGraph
