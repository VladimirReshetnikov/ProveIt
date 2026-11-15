import PA194FoundationIsoPredecessorTyped
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def strictRestrictionSubgraph {Γ : List Form} (p g h : Nat)
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (edgeSubgraph (.fvar h) (.fvar g)) := by
  apply allIntro
  apply allIntro
  let q : Form := edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)
  have hq : ND.Proof (q :: shifted (shifted Γ)) q := assumption (by simp)
  have rr := up (strictRestrictionShift (p+1) (g+1) (h+1) (strictRestrictionShift p g h hr)) q
  have out := andLeft (strictCutCases (p+1+1) (g+1+1) (h+1+1) 1 0 rr hq)
  convert impIntro out using 1 <;> (try dsimp [q,edgeSubgraph]) <;> (try isoSyntax)

def predecessorGraphFunctional {Γ : List Form} (g h p : Nat)
    (hold : ND.Proof Γ (graphFunctional (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphFunctional (.fvar h)) := functionalSubgraph h g (strictRestrictionSubgraph p g h hr) hold

def predecessorGraphInjective {Γ : List Form} (g h p : Nat)
    (hold : ND.Proof Γ (graphInjective (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphInjective (.fvar h)) := injectiveSubgraph h g (strictRestrictionSubgraph p g h hr) hold

def predecessorGraphOrder {Γ : List Form} (g h p : Nat)
    (hold : ND.Proof Γ (graphOrder (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphOrder (.fvar h)) := orderSubgraph h g (strictRestrictionSubgraph p g h hr) hold

#print axioms strictRestrictionSubgraph
#print axioms predecessorGraphFunctional
#print axioms predecessorGraphInjective
#print axioms predecessorGraphOrder
end M6.PA.RelationalSource.PairGraph
