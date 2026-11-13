module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSyntax
@[expose] public section

/-! Naturality under target relational rewriting, not source term substitution. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder
open RelationalSource
open Ordinal (Term Formula)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult PairGraph.orderIso

theorem shiftEnv_rew {ι : Type} {m k : Nat} (τ : Rew language Nat m Nat k)
    (e : ι → Term m) :
    (fun i => τ.q (shiftEnv e i)) = shiftEnv (fun i => τ (e i)) := by
  funext i
  exact Rew.q_comp_bShift_app τ (e i)

theorem bindEnv_rew {n m k : Nat} (τ : Rew language Nat m Nat k)
    (b : Fin n → Term m) :
    (fun i => τ.q (bindEnv b i)) = bindEnv (fun i => τ (b i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Rew.q_bvar_zero τ
  · exact Rew.q_comp_bShift_app τ (b j)

theorem lift_two_one {m k : Nat} (τ : Rew language Nat m Nat k) :
    τ.q.q (.bvar 1) = (.bvar 1 : Term (k+1+1)) := by
  change τ.q.q (.bvar (Fin.succ 0)) = _
  rw [Rew.q_bvar_succ,Rew.q_bvar_zero]
  rfl

theorem rew_neg {m k : Nat} (τ : Rew language Nat m Nat k) (p : Formula m) :
    Semiformula.rewAux τ p.neg = (Semiformula.rewAux τ p).neg :=
  Semiformula.rewAux_neg τ p

theorem value_rew {n : Nat} (t : SourceTerm n) {m k : Nat}
    (τ : Rew language Nat m Nat k) (b : Fin n → Term m)
    (f : Nat → Term m) (z : Term m) :
    Semiformula.rewAux τ (value t b f z) =
      value t (fun i => τ (b i)) (fun i => τ (f i)) (τ z) := by
  induction t generalizing m k with
  | bvar i => simp [value,Ordinal.domain_rew,ND.eq,Semiformula.rewAux,Function.comp_def,Matrix.comp_vecCons] <;> finishSourceSyntax
  | fvar i => simp [value,Ordinal.domain_rew,ND.eq,Semiformula.rewAux,Function.comp_def,Matrix.comp_vecCons] <;> finishSourceSyntax
  | func fn ts ih =>
    cases fn <;>
      simp only [value,Semiformula.rewAux,Ordinal.domain_rew,Ordinal.zero_rew,
        Ordinal.successor_rew,PairGraph.addResult_rew,PairGraph.mulResult_rew,
        ih,shiftEnv_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,lift_two_one]

theorem equal_rew {n m k : Nat} (s t : SourceTerm n)
    (τ : Rew language Nat m Nat k) (b : Fin n → Term m) (f : Nat → Term m) :
    Semiformula.rewAux τ (equal s t b f) =
      equal s t (fun i => τ (b i)) (fun i => τ (f i)) := by
  simp only [equal,Semiformula.rewAux,value_rew,PairGraph.orderIso_rew,
    shiftEnv_rew,Rew.q_bvar_zero,Rew.q_bvar_succ,lift_two_one]

theorem formula_rew {n : Nat} (p : SourceFormula n) {m k : Nat}
    (τ : Rew language Nat m Nat k) (b : Fin n → Term m) (f : Nat → Term m) :
    Semiformula.rewAux τ (formula p b f) =
      formula p (fun i => τ (b i)) (fun i => τ (f i)) := by
  induction p generalizing m k with
  | rel r ts => cases r; exact equal_rew _ _ _ _ _
  | nrel r ts => cases r; simp only [formula,rew_neg,equal_rew]
  | _ => simp only [formula,Semiformula.imp_eq,Semiformula.neg_eq,
      Semiformula.rewAux,rew_neg,Ordinal.domain_rew,
      Rew.q_bvar_zero,shiftEnv_rew,bindEnv_rew, *] <;> rfl

#print axioms value_rew
#print axioms equal_rew
#print axioms formula_rew
end M6.PA.ForwardRelational
