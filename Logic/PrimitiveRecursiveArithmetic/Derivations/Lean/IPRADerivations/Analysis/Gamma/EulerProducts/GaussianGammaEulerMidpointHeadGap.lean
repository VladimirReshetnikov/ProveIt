import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerRationalHeadConvexity

/-!
# The first-factor midpoint gap in rational Euler heads

The factor at index zero contributes the exact ratio
`(a+d)^2/(4*a*d)`. Each remaining factor preserves that same
ratio by the two-point arithmetic–geometric mean inequality.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerMidpointHeadGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaEulerRationalHead (numerator denominator numerator_zero numerator_succ)
open GaussianGammaEulerRationalHeadConvexity (denominator_power_scale)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def large (a d : PTm n) : PTm n := (a+d)*(a+d)
def small (a d : PTm n) : PTm n := two*two*a*d
def gap (a d : PTm n) : PTm n := monus (large a d) (small a d)

@[simp] theorem subst_large {m : ℕ} (σ : Fin n → PTm m) (a d : PTm n) :
    Syn.subst σ (large a d) = large (Syn.subst σ a) (Syn.subst σ d) := by simp [large]
@[simp] theorem subst_small {m : ℕ} (σ : Fin n → PTm m) (a d : PTm n) :
    Syn.subst σ (small a d) = small (Syn.subst σ a) (Syn.subst σ d) := by simp [small]
@[simp] theorem subst_gap {m : ℕ} (σ : Fin n → PTm m) (a d : PTm n) :
    Syn.subst σ (gap a d) = gap (Syn.subst σ a) (Syn.subst σ d) := by simp [gap]

theorem square_power (a : PTm n) : Γ ⊢[PRAAx] pw a two ≐ a*a :=
  (pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl _))

theorem ordered_square (a d : PTm n) (h : Γ ⊢[PRAAx] le a d) :
    Γ ⊢[PRAAx] large a d ≐ small a d+monus d a*monus d a := by
  have e := natEq (eq_add_of_le h)
  dsimp [large,small]
  apply deriveNat
  ipra_simps
  rw [e]
  ring

theorem small_le_large (a d : PTm n) : Γ ⊢[PRAAx] le (small a d) (large a d) := by
  refine .orE (le_total a d) ?_ ?_
  · exact le_of_eq_add (ordered_square a d Prf.hyp0)
  · have h := ordered_square d a (Prf.hyp0 : le d a :: Γ ⊢[PRAAx] le d a)
    exact le_of_eq_add ((by dsimp [large]; ipra_ring : le d a :: Γ ⊢[PRAAx] large a d ≐ large d a).eqTrans
      (h.eqTrans (congrAdd (by dsimp [small]; ipra_ring) (.eqRefl _))))

theorem gap_split (a d : PTm n) : Γ ⊢[PRAAx] large a d ≐ small a d+gap a d :=
  eq_add_of_le (small_le_large a d)

theorem gap_square (a d : PTm n) (h : Γ ⊢[PRAAx] le a d) :
    Γ ⊢[PRAAx] gap a d ≐ monus d a*monus d a := by
  have e := natEq (ordered_square a d h)
  have f := natEq (gap_split (Γ := Γ) a d)
  apply deriveNat
  ipra_simps
  linear_combination e-f

def numeratorComparison (N a d b : PTm n) : Fm PTm n :=
  le (pw (pw two two) (succ N)*(numerator (succ N) a b*numerator (succ N) d b)*large a d)
    (pw (numerator (succ N) (a+d) (two*b)) two*small a d)

@[simp] theorem subst_numeratorComparison {m : ℕ} (σ : Fin n → PTm m) (N a d b : PTm n) :
    (numeratorComparison N a d b).subst σ =
      numeratorComparison (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ b) := by
  simp [numeratorComparison]

private theorem numerator_first (a b : PTm n) : Γ ⊢[PRAAx] numerator (succ zero) a b ≐ a :=
  (numerator_succ zero a b).eqTrans ((congrMul (numerator_zero a b) (.eqRefl _)).eqTrans (by ipra_ring))

private theorem numerator_base (a d b : PTm n) : Γ ⊢[PRAAx] numeratorComparison zero a d b := by
  have e := natEq ((pw_one (pw two two)).eqTrans (square_power (Γ := Γ) two))
  have ea := natEq (numerator_first (Γ := Γ) a b)
  have ed := natEq (numerator_first (Γ := Γ) d b)
  have ec := natEq ((square_power (numerator (succ zero) (a+d) (two*b))).eqTrans
    (congrMul (numerator_first (Γ := Γ) (a+d) (two*b)) (numerator_first (a+d) (two*b))))
  dsimp [numeratorComparison,large,small]
  ipra_le 0 using rw [ea,ed,ec,e]; ring

private theorem numerator_step (N a d b : PTm n)
    (h : Γ ⊢[PRAAx] numeratorComparison N a d b) :
    Γ ⊢[PRAAx] numeratorComparison (succ N) a d b := by
  let u := a+b*succ N
  let v := d+b*succ N
  let w := a+d+two*b*succ N
  let X := numerator (succ N) a b
  let Y := numerator (succ N) d b
  let Z := numerator (succ N) (a+d) (two*b)
  let P := pw (pw two two) (succ N)
  have hw : Γ ⊢[PRAAx] le (pw two two*(u*v)) (w*w) := by
    apply le_congr _ _ (small_le_large u v)
    · dsimp [small]
      exact (congrMul (congrMul (square_power two).eqSymm (.eqRefl _)) (.eqRefl _)).eqTrans (by ipra_ring)
    · dsimp [large,u,v,w]
      ipra_ring
  have eP := natEq (pw_succ (Γ := Γ) (pw two two) (succ N))
  have eX := natEq (numerator_succ (Γ := Γ) (succ N) a b)
  have eY := natEq (numerator_succ (Γ := Γ) (succ N) d b)
  have eZ := natEq (numerator_succ (Γ := Γ) (succ N) (a+d) (two*b))
  have eW := natEq (square_power (Γ := Γ) (numerator (succ (succ N)) (a+d) (two*b)))
  have eQ := natEq (square_power (Γ := Γ) Z)
  have left : Γ ⊢[PRAAx]
      pw (pw two two) (succ (succ N))*(numerator (succ (succ N)) a b*numerator (succ (succ N)) d b)*large a d ≐
        (P*(X*Y)*large a d)*(pw two two*(u*v)) := by
    dsimp [P,X,Y,u,v]
    apply deriveNat
    ipra_simps
    rw [eP,eX,eY]
    ring
  have right : Γ ⊢[PRAAx]
      pw (numerator (succ (succ N)) (a+d) (two*b)) two*small a d ≐ (pw Z two*small a d)*(w*w) := by
    dsimp only [w]
    apply deriveNat
    ipra_simps
    rw [eW,eZ,eQ]
    ring
  exact le_congr left.eqSymm right.eqSymm (le_mul_mono h hw)

theorem numerator_gap (N a d b : PTm n) : Γ ⊢[PRAAx] numeratorComparison N a d b := by
  have hall : Γ ⊢[PRAAx] .all (numeratorComparison (var 0) (Syn.shift a) (Syn.shift d) (Syn.shift b)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_numeratorComparison,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        numerator_base a d b
    · simp only [subst_numeratorComparison,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact numerator_step _ _ _ _ Prf.hyp0
  simpa only [subst_numeratorComparison,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE N

def headComparison (N a d b : PTm n) : Fm PTm n :=
  le ((pw (denominator N (two*b)) two*large a d)*(numerator (succ N) a b*numerator (succ N) d b))
    ((denominator N b*denominator N b)*(pw (numerator (succ N) (a+d) (two*b)) two*small a d))

theorem head_gap (N a d b : PTm n) : Γ ⊢[PRAAx] headComparison N a d b := by
  let U := denominator N b
  let V := denominator N (two*b)
  let X := numerator (succ N) a b
  let Y := numerator (succ N) d b
  let Z := numerator (succ N) (a+d) (two*b)
  let P := pw (pw two two) (succ N)
  have e := natEq ((denominator_power_scale (Γ := Γ) N b two).eqTrans
    (congrMul (.eqRefl P) (square_power U)))
  have left : Γ ⊢[PRAAx] (pw V two*large a d)*(X*Y) ≐ (P*(X*Y)*large a d)*(U*U) := by
    apply deriveNat
    dsimp only [V]
    ipra_simps
    rw [e]
    ring
  exact le_congr left.eqSymm (by ipra_ring) (mul_le_mul_right (U*U) (numerator_gap N a d b))

theorem actual_Euler_midpoint_head_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (headComparison (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (head_gap _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerMidpointHeadGap
