module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualityTransitivity
public import M6PA.Calibration.PAInterpretedUniversal
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! Literal typed PAeq transitivity with all three guarded binders paid. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def interpretedTransitivity {Γ : List Form} (E : FormulaEquality Γ)
    (htrans : ND.Proof Γ PairGraph.isoTransitivityClosed) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.transitivity Fin.elim0 f) := by
  apply interpretedAllIntro
  apply interpretedAllIntro
  apply interpretedAllIntro
  let d : Form := Ordinal.domain (.fvar 0)
  let C1 := d::shifted Γ
  let C2 := d::shifted C1
  let C3 := d::shifted C2
  let E1 : FormulaEquality C1 := E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  let E2 : FormulaEquality C2 := E1.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  let E3 : FormulaEquality C3 := E2.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have h1 : ND.Proof C1 d := assumption (by simp [C1])
  have h2 : ND.Proof C2 (Ordinal.domain (.fvar 1)) := up (Ordinal.domainShift 0 h1) d
  have h3 : ND.Proof C3 (Ordinal.domain (.fvar 2)) := up (Ordinal.domainShift 1 h2) d
  have h0 : ND.Proof C3 d := assumption (by simp [C3])
  have ht1 : ND.Proof C1 PairGraph.isoTransitivityClosed := up (interpretedTransitivityShift htrans) d
  have ht2 : ND.Proof C2 PairGraph.isoTransitivityClosed := up (interpretedTransitivityShift ht1) d
  have ht3 : ND.Proof C3 PairGraph.isoTransitivityClosed := up (interpretedTransitivityShift ht2) d
  let b1 : Fin 1 → Term 0 := Fin.cases (.fvar 0) (fun i : Fin 0 => Rew.shift (Fin.elim0 i))
  let b2 : Fin 2 → Term 0 := Fin.cases (.fvar 0) (fun i => Rew.shift (b1 i))
  let b : Fin 3 → Term 0 := Fin.cases (.fvar 0) (fun i => Rew.shift (b2 i))
  let fs : Nat → Term 0 := fun i => Rew.shift (Rew.shift (Rew.shift (f i)))
  let p : Form := equal (.bvar 2) (.bvar 1) b fs
  let q : Form := equal (.bvar 1) (.bvar 0) b fs
  let EE := (E3.weaken (fun a ha => List.mem_cons_of_mem p ha)).weaken
    (fun a ha => List.mem_cons_of_mem q ha)
  have out : ND.Proof C3 (p 🡒 (q 🡒 equal (.bvar 2) (.bvar 0) b fs)) := by
    apply impIntro
    apply impIntro
    exact boundVariableEqualityTransitive EE 2 1 0 b fs (up (up ht3 p) q)
      (up (up h3 p) q) (up (up h0 p) q)
      (assumption (by simp [p,q])) (assumption (by simp [p,q]))
  convert out using 1 <;>
    (dsimp [C1,C2,C3,d,p,q,b,b1,b2,fs] <;>
      (try simp only [formula_neg,formula,Presentation.implies,Presentation.eq]) <;>
      (try congr 3) <;> (try (funext i; fin_cases i <;> rfl)))

#print axioms interpretedTransitivity
end M6.PA.ForwardRelational

