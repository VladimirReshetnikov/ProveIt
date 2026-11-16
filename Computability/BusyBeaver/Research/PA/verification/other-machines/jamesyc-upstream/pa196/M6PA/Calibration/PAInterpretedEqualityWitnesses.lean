module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalNaturality
public import M6PA.Calibration.PAForwardRelationalConstructors
public import M6PA.Calibration.RelationalOrderIsoReflexivity
@[expose] public section

/-! Actual witness introduction for the typed interpretation of arithmetic
equality. This is not raw equality of interpreted representatives. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain

theorem interpretedQOne {m k : Nat} (τ : Rew language Nat (m+1) Nat k) :
    τ.q (.bvar 1) = Rew.bShift (τ (.bvar 0)) := by
  change τ.q (.bvar (Fin.succ 0)) = _
  exact Rew.q_bvar_succ τ 0

macro "interpretedWitnessSyntax" : tactic => `(tactic|
  (simp only [Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,
    Rewriting.subst,app_eq_rewAux,Semiformula.rewAux,Semiformula.imp_eq,
    Semiformula.neg_eq,rew_neg,value_rew,equal_rew,
    Ordinal.domain_rew,Ordinal.zero_rew,Ordinal.successor_rew,PairGraph.orderIso_rew,
    shiftEnv_rew,interpretedQOne,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ];
   try simp [shiftEnv];
   finishSourceSyntax))

def equalityValueIntro {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (x y : Term 0)
    (hx : ND.Proof Γ (value s b f x)) (hy : ND.Proof Γ (value t b f y))
    (hi : ND.Proof Γ (PairGraph.orderIso x y)) :
    ND.Proof Γ (equal s t b f) := by
  unfold equal
  apply exsIntro _ x
  have mid : ND.Proof Γ (∃¹ (value s (shiftEnv b) (shiftEnv f) (Rew.bShift x) ⋏
      (value t (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏ PairGraph.orderIso (Rew.bShift x) (.bvar 0)))) := by
    apply exsIntro _ y
    convert andIntro hx (andIntro hy hi) using 1
    interpretedWitnessSyntax
  convert mid using 1
  interpretedWitnessSyntax

def interpretedIsoSelf {Γ : List Form} (E : FormulaEquality Γ) (x : Term 0)
    (hidentity : ND.Proof Γ PairGraph.identityStatement)
    (hx : ND.Proof Γ (Ordinal.domain x)) : ND.Proof Γ (PairGraph.orderIso x x) := by
  cases x with
  | bvar i => nomatch i
  | func fn _ => nomatch fn
  | fvar k => exact PairGraph.orderIsoFromExists E k (PairGraph.identityAt k hidentity hx)

def boundVariableEqualitySelf {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hidentity : ND.Proof Γ PairGraph.identityStatement)
    (hi : ND.Proof Γ (Ordinal.domain (b i))) :
    ND.Proof Γ (equal (.bvar i) (.bvar i) b f) := by
  have hv : ND.Proof Γ (value (.bvar i) b f (b i)) := by
    rw [value_bvar]
    exact andIntro hi (E.reflexive (b i))
  exact equalityValueIntro _ _ b f (b i) (b i) hv hv (interpretedIsoSelf E _ hidentity hi)

#print axioms equalityValueIntro
#print axioms boundVariableEqualitySelf
end M6.PA.ForwardRelational

