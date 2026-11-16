module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionCompatibility
@[expose] public section

/-! Pure source-variable renaming alignment. Unlike actual function-term
substitution this special case does preserve interpreted syntax literally. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult PairGraph.orderIso

theorem value_sourceMap {n k m : Nat} (t : SourceTerm n)
    (ρ : Fin n → Fin k) (ψ : Nat → Nat)
    (b : Fin k → Term m) (f : Nat → Term m) (z : Term m) :
    value (Rew.map ρ ψ t) b f z = value t (fun i => b (ρ i)) (fun i => f (ψ i)) z := by
  induction t generalizing m with
  | bvar i => rfl
  | fvar i => rfl
  | func fn ts ih =>
    cases fn <;> simp only [Rew.func, Function.comp_apply, value, ih] <;> rfl

/-- Source `bShift` skips the fresh environment head; it does not shift any
Nat free parameter. The target binder arity `m` is independent of the source. -/
theorem value_sourceBShift {n m : Nat} (t : SourceTerm n)
    (a : Term m) (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    value (Rew.bShift t) (Fin.cases a b) f z = value t b f z := by
  exact value_sourceMap t Fin.succ id (Fin.cases a b) f z

theorem equal_sourceMap {n k m : Nat} (s t : SourceTerm n)
    (ρ : Fin n → Fin k) (ψ : Nat → Nat)
    (b : Fin k → Term m) (f : Nat → Term m) :
    equal (Rew.map ρ ψ s) (Rew.map ρ ψ t) b f =
      equal s t (fun i => b (ρ i)) (fun i => f (ψ i)) := by
  simp only [equal, value_sourceMap]
  rfl

theorem bindEnv_sourceMap {n k m : Nat} (ρ : Fin n → Fin k)
    (b : Fin k → Term m) :
    (fun i => bindEnv b (Fin.cases 0 (fun j => (ρ j).succ) i)) =
      bindEnv (fun i => b (ρ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem formula_sourceMap {n k m : Nat} (p : SourceFormula n)
    (ρ : Fin n → Fin k) (ψ : Nat → Nat)
    (b : Fin k → Term m) (f : Nat → Term m) :
    formula (Semiformula.rewAux (Rew.map ρ ψ) p) b f =
      formula p (fun i => b (ρ i)) (fun i => f (ψ i)) := by
  induction p generalizing k m with
  | rel r ts => cases r; exact equal_sourceMap _ _ _ _ _ _
  | nrel r ts => cases r; simp only [Semiformula.rewAux, formula, Function.comp_apply, equal_sourceMap]
  | all p ih =>
    simp only [Semiformula.rewAux, formula, Rew.q_map, ih]
    rw [show (fun i => bindEnv b ((0 :> Fin.succ ∘ ρ) i)) =
      bindEnv (fun i => b (ρ i)) from bindEnv_sourceMap ρ b]
    rfl
  | exs p ih =>
    simp only [Semiformula.rewAux, formula, Rew.q_map, ih]
    rw [show (fun i => bindEnv b ((0 :> Fin.succ ∘ ρ) i)) =
      bindEnv (fun i => b (ρ i)) from bindEnv_sourceMap ρ b]
    rfl
  | _ => simp only [Semiformula.rewAux, formula, *]

theorem formula_sourceBShift {n m : Nat} (p : SourceFormula n)
    (a : Term m) (b : Fin n → Term m) (f : Nat → Term m) :
    formula (Semiformula.rewAux Rew.bShift p) (Fin.cases a b) f = formula p b f := by
  exact formula_sourceMap p Fin.succ id (Fin.cases a b) f

/-- The untouched new variable under a source quantifier. -/
theorem sourceLift_zero {n k : Nat} (σ : Rew Presentation.language Nat n Nat k) :
    σ.q (.bvar 0) = (.bvar 0 : SourceTerm (k+1)) := Rew.q_bvar_zero σ

/-- Old variables are substituted, then shifted past the fresh source binder. -/
theorem sourceLift_tail {n k : Nat} (σ : Rew Presentation.language Nat n Nat k)
    (i : Fin n) : σ.q (.bvar i.succ) = Rew.bShift (σ (.bvar i)) :=
  Rew.q_bvar_succ σ i

theorem sourceLift_free {n k : Nat} (σ : Rew Presentation.language Nat n Nat k)
    (i : Nat) : σ.q (.fvar i) = Rew.bShift (σ (.fvar i)) := Rew.q_fvar σ i

/-- Capture-aware lift aligns on every old source term, including genuine
function terms. This is a source syntax identity, not relational value equality. -/
theorem sourceLift_bShift {n k : Nat} (σ : Rew Presentation.language Nat n Nat k)
    (t : SourceTerm n) : σ.q (Rew.bShift t) = Rew.bShift (σ t) :=
  Rew.q_comp_bShift_app σ t

#print axioms equal_sourceMap
#print axioms formula_sourceMap
#print axioms formula_sourceBShift
#print axioms value_sourceMap
#print axioms value_sourceBShift
#print axioms sourceLift_zero
#print axioms sourceLift_tail
#print axioms sourceLift_free
#print axioms sourceLift_bShift
end M6.PA.ForwardRelational
