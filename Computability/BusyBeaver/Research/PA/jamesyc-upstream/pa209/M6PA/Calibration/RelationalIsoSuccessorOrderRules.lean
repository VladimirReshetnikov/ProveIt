module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoOrderLocal
@[expose] public section

/-! All four old/new edge cases for order preservation. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorOrderAt {Γ : List Form} (E : FormulaEquality Γ) (g h a b x u y v : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)))
    (hf : ND.Proof Γ (edge (.fvar h) (.fvar u) (.fvar v))) :
    ND.Proof Γ (sourceIff (mem (.fvar x) (.fvar u)) (mem (.fvar y) (.fvar v))) := by
  have ce := mp he (andLeft (exactAt g h a b x y hx))
  have cf := mp hf (andLeft (exactAt g h a b u v hx))
  apply orElim ce
  · let p : Form := edge (.fvar g) (.fvar x) (.fvar y)
    apply orElim (up cf p)
    · exact orderOrderAt g x u y v (up (up ho p) _)
        (assumption (by simp [p])) (assumption (by simp))
    · let q : Form := eq (.fvar u) (.fvar a) ⋏ eq (.fvar v) (.fvar b)
      have hq : ND.Proof (q::p::Γ) q := assumption (by simp)
      let EE := E.weaken (fun r hr => List.mem_cons_of_mem q (List.mem_cons_of_mem p hr))
      have old := orderTypedAt g a b x y (up (up ht p) q) (assumption (by simp [p]))
      exact isoIffOfNeither _ _
        (memberNoEqualEndpoint EE a x u (up (up ha p) q) (andLeft old) (andLeft hq))
        (memberNoEqualEndpoint EE b y v (up (up hb p) q) (andRight old) (andRight hq))
  · let p : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar y) (.fvar b)
    apply orElim (up cf p)
    · let q : Form := edge (.fvar g) (.fvar u) (.fvar v)
      have hp : ND.Proof (q::p::Γ) p := assumption (by simp)
      let EE := E.weaken (fun r hr => List.mem_cons_of_mem q (List.mem_cons_of_mem p hr))
      have old := orderTypedAt g a b u v (up (up ht p) q) (assumption (by simp [q]))
      exact isoIffOfBoth _ _
        (Ordinal.memContainer EE.core a x u (EE.symmetryOf (andLeft hp)) (andLeft old))
        (Ordinal.memContainer EE.core b y v (EE.symmetryOf (andRight hp)) (andRight old))
    · let q : Form := eq (.fvar u) (.fvar a) ⋏ eq (.fvar v) (.fvar b)
      have hp : ND.Proof (q::p::Γ) p := assumption (by simp)
      have hq : ND.Proof (q::p::Γ) q := assumption (by simp)
      let EE := E.weaken (fun r hr => List.mem_cons_of_mem q (List.mem_cons_of_mem p hr))
      exact isoIffOfNeither _ _
        (equalEndpointsNoMem EE a x u (up (up ha p) q) (andLeft hp) (andLeft hq))
        (equalEndpointsNoMem EE b y v (up (up hb p) q) (andRight hp) (andRight hq))

#print axioms successorOrderAt
end M6.PA.RelationalSource.PairGraph
