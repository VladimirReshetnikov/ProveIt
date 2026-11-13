module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionPrefixStep
public import M6PA.Calibration.RelationalOrdinalInductionUniform
@[expose] public section

/-! Addition prefixes satisfy the actual ordinal induction schema. The sole
variable-schema premise is explicit Separation of the negated prefix property. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

def prefixProperty (base : Nat) : Formula 1 :=
  addPrefixExists (.bvar 0) (.fvar base)

set_option maxHeartbeats 1200000 in
def prefixInductionBase {Γ : List Form} (S : SetProofs Γ) (base : Nat)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar base))) :
    ND.Proof Γ (Ordinal.inductionBase (prefixProperty base)) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have ss := S.shift.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have out := zeroPrefixWitness ss.equality 0 (base+1) (andRight hd)
    (up (domainShift base hb) d) ss.empty ss.adjunction
  have h := impIntro out
  convert h using 1 <;> (dsimp [d]; simp only [Ordinal.inductionBase,prefixProperty]; prefixSyntax)


#print axioms prefixInductionBase
end M6.PA.RelationalSource.PairGraph
