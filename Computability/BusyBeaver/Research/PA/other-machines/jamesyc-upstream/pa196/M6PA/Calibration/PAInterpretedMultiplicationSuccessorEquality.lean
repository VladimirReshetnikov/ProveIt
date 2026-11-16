module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedMultiplicationSuccessorPayloads
public import M6PA.Calibration.PAInterpretedFunctionCongruenceWitnesses
@[expose] public section

/-! Both literal term sides have real values, and every such value pair is
related by the correctly oriented actual order isomorphism. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def multiplicationSuccessorValueIso {Γ : List Form} {n : Nat} (I : MultiplicationImagePremises Γ) (T : TotalityPremises Γ)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (l r : Term 0)
    (hi : ND.Proof Γ (Ordinal.domain (b i))) (hj : ND.Proof Γ (Ordinal.domain (b j)))
    (hl : ND.Proof Γ (value (Presentation.mul (Presentation.succ (.bvar i)) (.bvar j)) b f l))
    (hr : ND.Proof Γ (value (Presentation.add (.bvar j) (Presentation.mul (.bvar i) (.bvar j))) b f r)) :
    ND.Proof Γ (PairGraph.orderIso l r) := by
  obtain ⟨ln,rfl⟩ := groundName l
  obtain ⟨rn,rfl⟩ := groundName r
  obtain ⟨x,hx⟩ := groundName (b i)
  obtain ⟨y,hy⟩ := groundName (b j)
  have left := multiplicationSuccessorLeftValue I.additionImage.coherence.equality i j b f (.fvar ln) hl
  have right := multiplicationSuccessorRightValue I.additionImage.coherence.equality i j b f (.fvar rn) hr
  rw [hx,hy] at left right
  have dx : ND.Proof Γ (Ordinal.domain (.fvar x)) := by simpa only [hx] using hi
  have dy : ND.Proof Γ (Ordinal.domain (.fvar y)) := by simpa only [hy] using hj
  exact multiplicationImagePayloads I T x y ln rn dx dy (valueDomain _ _ _ _ hr) left right

def multiplicationSuccessorVariablesEqual {Γ : List Form} {n : Nat}
    (I : MultiplicationImagePremises Γ) (T : TotalityPremises Γ)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hi : ND.Proof Γ (Ordinal.domain (b i))) (hj : ND.Proof Γ (Ordinal.domain (b j))) :
    ND.Proof Γ (equal (Presentation.mul (Presentation.succ (.bvar i)) (.bvar j))
      (Presentation.add (.bvar j) (Presentation.mul (.bvar i) (.bvar j))) b f) := by
  have cl : EnvironmentCoverage Γ b f (Presentation.mul (Presentation.succ (.bvar i)) (.bvar j)) :=
    Fin.cases (Fin.cases hi (fun a => Fin.elim0 a)) (Fin.cases hj (fun a => Fin.elim0 a))
  have cr : EnvironmentCoverage Γ b f (Presentation.add (.bvar j) (Presentation.mul (.bvar i) (.bvar j))) :=
    Fin.cases hj (Fin.cases (Fin.cases hi (Fin.cases hj (fun a => Fin.elim0 a))) (fun a => Fin.elim0 a))
  have hs := termTotality T _ b f cl
  have ht := termTotality T _ b f cr
  apply equalOfTotalValues _ _ b f hs ht
  let bs := freeShiftEnv (freeShiftEnv b)
  let fs := freeShiftEnv (freeShiftEnv f)
  let p := value (Presentation.mul (Presentation.succ (.bvar i)) (.bvar j)) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  let q := value (Presentation.add (.bvar j) (Presentation.mul (.bvar i) (.bvar j))) bs fs (.fvar 0)
  let C := q::shifted (p::shifted Γ)
  have hv : ND.Proof C (value (Presentation.mul (Presentation.succ (.bvar i)) (.bvar j)) bs fs (.fvar 1)) := by
    simpa only [p,value_shift,Rew.shift_fvar] using
      up (shiftProof (assumption (Γ := p::shifted Γ) (p := p) (by simp))) q
  have hw : ND.Proof C q := assumption (by simp [C])
  have di : ND.Proof C (Ordinal.domain (bs i)) := by
    simpa only [bs,freeShiftEnv,Semiformula.shift,Rewriting.shift,app_eq_rewAux,Ordinal.domain_rew] using
      up (shiftProof (up (shiftProof hi) p)) q
  have dj : ND.Proof C (Ordinal.domain (bs j)) := by
    simpa only [bs,freeShiftEnv,Semiformula.shift,Rewriting.shift,app_eq_rewAux,Ordinal.domain_rew] using
      up (shiftProof (up (shiftProof hj) p)) q
  exact multiplicationSuccessorValueIso ((I.shift.up p).shift.up q) ((T.shift.up p).shift.up q) i j bs fs (.fvar 1) (.fvar 0) di dj hv hw

#print axioms multiplicationSuccessorValueIso
#print axioms multiplicationSuccessorVariablesEqual
end M6.PA.ForwardRelational
