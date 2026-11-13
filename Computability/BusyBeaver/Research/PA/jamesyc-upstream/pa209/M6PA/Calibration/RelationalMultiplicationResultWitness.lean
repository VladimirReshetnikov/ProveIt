module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationPrefixStep
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulOutput (x y : Term n) : Formula n :=
  ∃¹ (Ordinal.domain (.bvar 0) ⋏ mulResult (Rew.bShift x) (Rew.bShift y) (.bvar 0))

/-- A literal multiplication result retains actual zero and graph witnesses. -/
def mulResultIntro {Γ : List Form} (x y w z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar x) (.fvar y) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar w))) :
    ND.Proof Γ (mulResult (.fvar x) (.fvar y) (.fvar w)) := by
  apply exsIntro _ (.fvar z)
  have h : ND.Proof Γ (∃¹ (Ordinal.zero (.fvar z) ⋏
      (mulPrefix (.fvar x) (.fvar y) (.fvar z) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar w)))) := by
    apply exsIntro _ (.fvar g)
    convert andIntro hz (andIntro hp he) using 1 <;> mulCompactSyntax
  convert h using 1 <;> mulCompactSyntax

def mulOutputFromEndpoint {Γ : List Form} (x y w z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar x) (.fvar y) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar w))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar y)) := by
  have parts := hp
  unfold mulPrefix at parts
  have hw := graphRangeAt g x w (andLeft (andRight (andRight parts))) he
  have hm := mulResultIntro x y w z g hz hp he
  apply exsIntro _ (.fvar w)
  convert andIntro hw hm using 1 <;> ((try simp only [mulOutput]); mulCompactSyntax)

#print axioms mulResultIntro
#print axioms mulOutputFromEndpoint
end M6.PA.RelationalSource.PairGraph

