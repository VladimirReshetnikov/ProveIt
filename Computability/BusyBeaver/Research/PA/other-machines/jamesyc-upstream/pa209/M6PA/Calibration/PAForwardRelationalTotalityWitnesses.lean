module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalTotalityPremises
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult value

theorem q_one {m k : Nat} (τ : Rew language Nat (m+1) Nat k) :
    τ.q (.bvar 1) = Rew.bShift (τ (.bvar 0)) := by
  change τ.q (.bvar (Fin.succ 0)) = _
  exact Rew.q_bvar_succ τ 0

macro "valueWitnessSyntax" : tactic => `(tactic|
  (simp only [Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,
    Rewriting.subst,app_eq_rewAux,Semiformula.rewAux,Semiformula.imp_eq,
    Semiformula.neg_eq,rew_neg,value_rew,hasValue_rew,
    Ordinal.domain_rew,Ordinal.zero_rew,Ordinal.successor_rew,
    PairGraph.addResult_rew,PairGraph.mulResult_rew,
    shiftEnv_rew,q_one,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ];
   try simp [shiftEnv,freeShiftEnv];
   finishSourceSyntax))

def successorValueIntro {Γ : List Form} {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (x z : Term 0)
    (hx : ND.Proof Γ (value t b f x))
    (hz : ND.Proof Γ (Ordinal.domain z))
    (hs : ND.Proof Γ (Ordinal.successor x z)) :
    ND.Proof Γ (value (Presentation.succ t) b f z) := by
  rw [value_succ]
  apply andIntro hz
  apply exsIntro _ x
  convert andIntro hx hs using 1
  valueWitnessSyntax

def additionValueIntro {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (x y z : Term 0)
    (hx : ND.Proof Γ (value s b f x))
    (hy : ND.Proof Γ (value t b f y))
    (hz : ND.Proof Γ (Ordinal.domain z))
    (hr : ND.Proof Γ (PairGraph.addResult x y z)) :
    ND.Proof Γ (value (Presentation.add s t) b f z) := by
  rw [value_add]
  apply andIntro hz
  apply exsIntro _ x
  have hh : ND.Proof Γ (∃¹ (value s (shiftEnv b) (shiftEnv f) (Rew.bShift x) ⋏
      (value t (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏
        PairGraph.addResult (Rew.bShift x) (.bvar 0) (Rew.bShift z)))) := by
    apply exsIntro _ y
    convert andIntro hx (andIntro hy hr) using 1
    valueWitnessSyntax
  convert hh using 1
  valueWitnessSyntax

def multiplicationValueIntro {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (x y z : Term 0)
    (hx : ND.Proof Γ (value s b f x))
    (hy : ND.Proof Γ (value t b f y))
    (hz : ND.Proof Γ (Ordinal.domain z))
    (hr : ND.Proof Γ (PairGraph.mulResult x y z)) :
    ND.Proof Γ (value (Presentation.mul s t) b f z) := by
  rw [value_mul]
  apply andIntro hz
  apply exsIntro _ x
  have hh : ND.Proof Γ (∃¹ (value s (shiftEnv b) (shiftEnv f) (Rew.bShift x) ⋏
      (value t (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏
        PairGraph.mulResult (Rew.bShift x) (.bvar 0) (Rew.bShift z)))) := by
    apply exsIntro _ y
    convert andIntro hx (andIntro hy hr) using 1
    valueWitnessSyntax
  convert hh using 1
  valueWitnessSyntax

#print axioms successorValueIntro
#print axioms additionValueIntro
#print axioms multiplicationValueIntro
end M6.PA.ForwardRelational
