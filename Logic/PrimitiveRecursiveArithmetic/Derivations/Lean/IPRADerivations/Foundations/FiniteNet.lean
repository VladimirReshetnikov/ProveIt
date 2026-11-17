import IPRADerivations.Core.Order

/-!
# Finite-net lifting

Packet: `foundations/fiber_ipra_2026-11-16`, Theorem `thm:net`.

A net is a term `net(i, parameters)`, with its finite index bound supplied as
an arbitrary term. The domain, source and target closeness relations, and
predicates on observations are object-language formulas. Coverage, a modulus,
stability of the desired property, and correctness at the net points give the
relaxed property at every domain point. The selected index is sealed by
existential elimination.

The schema supports any finite number of parameters, arbitrary parameter and
point terms, and any context. Source/target closeness formulas may express
metric bounds after clearing denominators, including their query parameters.
-/

namespace LeanProofs.IPRA.Foundations.FiniteNet

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {k n m : ℕ}

/-- Evaluate a term body at a point and a finite parameter family. -/
def termAt (body : PTm (k + 1)) (x : PTm n) (parameters : Fin k → PTm n) : PTm n :=
  Syn.subst (Fin.cases x parameters) body

/-- Instantiate a predicate at a point and its parameters. -/
def point (A : Fm PTm (k + 1)) (x : PTm n) (parameters : Fin k → PTm n) : Fm PTm n :=
  A.subst (Fin.cases x parameters)

/-- Instantiate a two-point relation at its points and parameters. -/
def relation (R : Fm PTm (k + 2)) (x z : PTm n) (parameters : Fin k → PTm n) : Fm PTm n :=
  R.subst (Fin.cases x (Fin.cases z parameters))

@[simp] theorem subst_termAt (body : PTm (k + 1)) (x : PTm n)
    (parameters : Fin k → PTm n) (σ : Fin n → PTm m) :
    Syn.subst σ (termAt body x parameters) =
      termAt body (Syn.subst σ x) (fun i => Syn.subst σ (parameters i)) := by
  simp only [termAt, Syn.subst_subst]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

@[simp] theorem subst_point (A : Fm PTm (k + 1)) (x : PTm n)
    (parameters : Fin k → PTm n) (σ : Fin n → PTm m) :
    (point A x parameters).subst σ =
      point A (Syn.subst σ x) (fun i => Syn.subst σ (parameters i)) := by
  simp only [point, Fm.subst_subst]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

@[simp] theorem subst_relation (R : Fm PTm (k + 2)) (x z : PTm n)
    (parameters : Fin k → PTm n) (σ : Fin n → PTm m) :
    (relation R x z parameters).subst σ =
      relation R (Syn.subst σ x) (Syn.subst σ z)
        (fun i => Syn.subst σ (parameters i)) := by
  simp only [relation, Fm.subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases <;> rfl

/-- A domain point lies near some point of the finite net. -/
def coverage (domain : Fm PTm (k + 1)) (close : Fm PTm (k + 2))
    (net : PTm (k + 1)) (bound x : PTm n) (parameters : Fin k → PTm n) : Fm PTm n :=
  point domain x parameters ⟶
    .ex (lt (var 0) (Syn.shift bound) ⋏
      relation close (Syn.shift x)
        (termAt net (var 0) (fun i => Syn.shift (parameters i)))
        (fun i => Syn.shift (parameters i)))

/-- Nearby source-domain points have nearby observations. -/
def modulus (domain : Fm PTm (k + 1)) (close near : Fm PTm (k + 2))
    (image : PTm (k + 1)) (x : PTm n) (parameters : Fin k → PTm n) : Fm PTm n :=
  point domain x parameters ⟶
    .all (point domain (var 0) (fun i => Syn.shift (parameters i)) ⟶
      relation close (Syn.shift x) (var 0) (fun i => Syn.shift (parameters i)) ⟶
      relation near (termAt image (Syn.shift x) (fun i => Syn.shift (parameters i)))
        (termAt image (var 0) (fun i => Syn.shift (parameters i)))
        (fun i => Syn.shift (parameters i)))

/-- Transfer the property across the certified target discrepancy. -/
def stability (near : Fm PTm (k + 2)) (property relaxed : Fm PTm (k + 1))
    (image : PTm (k + 1)) (x : PTm n) (parameters : Fin k → PTm n) : Fm PTm n :=
  .all (point property (termAt image (var 0) (fun i => Syn.shift (parameters i)))
      (fun i => Syn.shift (parameters i)) ⟶
    relation near (termAt image (Syn.shift x) (fun i => Syn.shift (parameters i)))
      (termAt image (var 0) (fun i => Syn.shift (parameters i)))
      (fun i => Syn.shift (parameters i)) ⟶
    point relaxed (termAt image (Syn.shift x) (fun i => Syn.shift (parameters i)))
      (fun i => Syn.shift (parameters i)))

/-- Every in-range net point belongs to the domain and has the required property. -/
def netValid (domain property : Fm PTm (k + 1)) (net image : PTm (k + 1))
    (bound : PTm n) (parameters : Fin k → PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift bound) ⟶
    point domain (termAt net (var 0) (fun i => Syn.shift (parameters i)))
      (fun i => Syn.shift (parameters i)) ⋏
    point property
      (termAt image (termAt net (var 0) (fun i => Syn.shift (parameters i)))
        (fun i => Syn.shift (parameters i)))
      (fun i => Syn.shift (parameters i)))

/-- `thm:net`, with the covering net index kept local to the proof. -/
theorem lift_at {Γ : List (Fm PTm n)}
    (domain property relaxed : Fm PTm (k + 1)) (close near : Fm PTm (k + 2))
    (net image : PTm (k + 1)) (bound x : PTm n) (parameters : Fin k → PTm n)
    (hDomain : Γ ⊢[PRAAx] point domain x parameters)
    (hCoverage : Γ ⊢[PRAAx] coverage domain close net bound x parameters)
    (hModulus : Γ ⊢[PRAAx] modulus domain close near image x parameters)
    (hStability : Γ ⊢[PRAAx] stability near property relaxed image x parameters)
    (hNet : Γ ⊢[PRAAx] netValid domain property net image bound parameters) :
    Γ ⊢[PRAAx] point relaxed (termAt image x parameters) parameters := by
  refine .exE (.impE hCoverage hDomain) ?_
  let ρ : Fin k → PTm (n + 1) := fun i => Syn.shift (parameters i)
  let z := termAt net (var 0) ρ
  let witness := lt (var 0) (Syn.shift bound) ⋏ relation close (Syn.shift x) z ρ
  let Δ := witness :: Γ.map Fm.shift
  have hWitness : Δ ⊢[PRAAx] witness := Prf.hyp0
  have hPoints : Δ ⊢[PRAAx]
      point domain z ρ ⋏ point property (termAt image z ρ) ρ :=
    Prf.impE hNet.allOpen.wk (Prf.andE₁ hWitness)
  have hMod : Δ ⊢[PRAAx] point domain z ρ ⟶
      relation close (Syn.shift x) z ρ ⟶
      relation near (termAt image (Syn.shift x) ρ) (termAt image z ρ) ρ := by
    have h := Prf.allE z ((Prf.impE hModulus hDomain).shift.wk (ψ := witness))
    simpa only [Fm.shift, Fm.subst_all, Fm.subst_imp, subst_point,
      subst_relation, subst_termAt, Syn.subst_var, Syn.up_zero, Syn.up_succ,
      Syn.subst_inst_shift, Syn.subst_shift, Syn.subst_subst, Syn.inst_zero, Syn.inst_succ, Syn.shift_var, Δ, ρ, Syn.shift] using h
  have hStable : Δ ⊢[PRAAx] point property (termAt image z ρ) ρ ⟶
      relation near (termAt image (Syn.shift x) ρ) (termAt image z ρ) ρ ⟶
      point relaxed (termAt image (Syn.shift x) ρ) ρ := by
    have h := Prf.allE z (hStability.shift.wk (ψ := witness))
    simpa only [Fm.shift, stability, Fm.subst_all, Fm.subst_imp, subst_point,
      subst_relation, subst_termAt, Syn.subst_var, Syn.up_zero, Syn.up_succ,
      Syn.subst_inst_shift, Syn.subst_shift, Syn.subst_subst, Syn.inst_zero, Syn.inst_succ, Syn.shift_var, Δ, ρ, Syn.shift] using h
  have result := Prf.impE (Prf.impE hStable (Prf.andE₂ hPoints))
    (Prf.impE (Prf.impE hMod (Prf.andE₁ hPoints)) (Prf.andE₂ hWitness))
  simpa only [Fm.shift, subst_point, subst_termAt, Syn.shift, Δ, witness, z, ρ] using result


/-- The finite-net rule as an object-language implication in any context. -/
theorem finite_net {Γ : List (Fm PTm n)}
    (domain property relaxed : Fm PTm (k + 1)) (close near : Fm PTm (k + 2))
    (net image : PTm (k + 1)) (bound x : PTm n) (parameters : Fin k → PTm n) :
    Γ ⊢[PRAAx]
      point domain x parameters ⟶
      coverage domain close net bound x parameters ⟶
      modulus domain close near image x parameters ⟶
      stability near property relaxed image x parameters ⟶
      netValid domain property net image bound parameters ⟶
      point relaxed (termAt image x parameters) parameters := by
  refine .impI (.impI (.impI (.impI (.impI ?_))))
  exact lift_at domain property relaxed close near net image bound x parameters
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

/-- Universal closure of the finite-net rule for the supplied term bodies. -/
theorem finite_net_closed
    (domain property relaxed : Fm PTm (k + 1)) (close near : Fm PTm (k + 2))
    (net image : PTm (k + 1)) (bound x : PTm n) (parameters : Fin k → PTm n) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ n
      (point domain x parameters ⟶
      coverage domain close net bound x parameters ⟶
      modulus domain close near image x parameters ⟶
      stability near property relaxed image x parameters ⟶
      netValid domain property net image bound parameters ⟶
      point relaxed (termAt image x parameters) parameters) :=
  closeUniv n (finite_net domain property relaxed close near net image bound x parameters)

end LeanProofs.IPRA.Foundations.FiniteNet
