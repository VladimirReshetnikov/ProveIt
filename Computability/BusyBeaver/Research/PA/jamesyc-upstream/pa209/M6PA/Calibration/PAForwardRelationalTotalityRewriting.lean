module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalNaturality
public import M6PA.Calibration.PAForwardRelationalConstructors
public import M6PA.Calibration.RelationalSourceAdjunctionLogic
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult PairGraph.orderIso

/-- Existence of a value, with both environments shifted below its binder. -/
def hasValue {n m : Nat} (t : SourceTerm n)
    (b : Fin n → Term m) (f : Nat → Term m) : Formula m :=
  ∃¹ value t (shiftEnv b) (shiftEnv f) (.bvar 0)

theorem value_subst {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0) :
    (value t (shiftEnv b) (shiftEnv f) (.bvar 0))/[z] = value t b f z := by
  simp only [Rewriting.subst,app_eq_rewAux,value_rew]
  congr 1 <;> (try funext i) <;> simp [shiftEnv]

theorem hasValue_rew {n m k : Nat} (t : SourceTerm n)
    (τ : Rew language Nat m Nat k) (b : Fin n → Term m) (f : Nat → Term m) :
    Semiformula.rewAux τ (hasValue t b f) =
      hasValue t (fun i => τ (b i)) (fun i => τ (f i)) := by
  simp only [hasValue,Semiformula.rewAux,value_rew,shiftEnv_rew,Rew.q_bvar_zero]

def valueIntro {Γ : List ND.Form} {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0)
    (h : ND.Proof Γ (value t b f z)) : ND.Proof Γ (hasValue t b f) :=
  ND.exsIntro _ z (by simpa only [value_subst] using h)

def valueDomain {Γ : List ND.Form} {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0)
    (h : ND.Proof Γ (value t b f z)) : ND.Proof Γ (Ordinal.domain z) := by
  cases t with
  | bvar i => exact ND.andLeft h
  | fvar i => exact ND.andLeft h
  | func fn ts => cases fn <;> exact ND.andLeft h

def freeShiftEnv {ι : Type} (e : ι → Term 0) : ι → Term 0 :=
  fun i => Rew.shift (e i)

theorem value_free {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) :
    (value t (shiftEnv b) (shiftEnv f) (.bvar 0)).free =
      value t (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) := by
  simp only [Semiformula.free,Rewriting.free,app_eq_rewAux,value_rew]
  congr 1 <;> (try funext i) <;> simp [shiftEnv,freeShiftEnv]

theorem value_shift {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0) :
    (value t b f z).shift =
      value t (freeShiftEnv b) (freeShiftEnv f) (Rew.shift z) := by
  exact value_rew t Rew.shift b f z

theorem hasValue_shift {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) :
    (hasValue t b f).shift = hasValue t (freeShiftEnv b) (freeShiftEnv f) :=
  hasValue_rew t Rew.shift b f

def valueElim {Γ : List ND.Form} {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (q : ND.Form)
    (h : ND.Proof Γ (hasValue t b f))
    (k : ND.Proof (value t (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) :: ND.shifted Γ)
      q.shift) : ND.Proof Γ q :=
  ND.exsElim h (by simpa only [value_free] using k)

#print axioms value_free
#print axioms value_shift
#print axioms hasValue_shift
#print axioms valueElim
#print axioms value_subst
#print axioms hasValue_rew
#print axioms valueIntro
#print axioms valueDomain
end M6.PA.ForwardRelational
