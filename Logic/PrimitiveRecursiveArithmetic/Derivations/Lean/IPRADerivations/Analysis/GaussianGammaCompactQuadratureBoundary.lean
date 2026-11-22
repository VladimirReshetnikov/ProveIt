import IPRADerivations.Analysis.GaussianCompactRiemannName
import IPRADerivations.Analysis.GaussianGammaIntegralCutoffs

/-!
# Exact source compact Euler-quadrature boundary

For each fixed outer cutoff p,A,R, the interval is exactly [eta,top].
The compact name uses the original PR3 evaluator and its proved local
sampled-modulus certificate. At observation p its actual mesh is exactly
source cells(p,A,R). The diagonal across changing outer cutoffs is not
asserted regular here; improper tails and the genuine Euler integrand
modulus are separate obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCompactQuadratureBoundary

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen top lipschitz cells)
open GaussianCompactRiemannName (sampledModulus quadrature)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (p A R : PTm n) : PTm n := monus (etaDen p A R*top p A R) one
def data (p A R x : PTm n) : PTm n :=
  GaussianCompactRiemannName.data one (width p A R) (etaDen p A R) (lipschitz p A R) (top p A R) x
def source (F : PR 3) (p A R x : PTm n) : Fm PTm n :=
  sampledModulus F one (width p A R) (etaDen p A R) (lipschitz p A R) x
@[simp] theorem subst_width {m : ℕ} (σ : Fin n → PTm m) (p A R : PTm n) :
    Syn.subst σ (width p A R) = width (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [width,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p A R x : PTm n) :
    Syn.subst σ (data p A R x) = data (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [data,lipschitz,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (p A R x : PTm n) :
    (source F p A R x).subst σ = source F (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [source,lipschitz,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem exact_right_endpoint (p A R : PTm n) : Γ ⊢[PRAAx]
    one+width p A R ≐ etaDen p A R*top p A R :=
  (eq_add_of_le (GaussianRationalHorner.positive_product _ _
    (GaussianGammaIntegralCutoffs.eta_den_positive p A R) (GaussianGammaIntegralCutoffs.top_positive p A R))).eqSymm

theorem width_bound (p A R : PTm n) : Γ ⊢[PRAAx] le (width p A R) (etaDen p A R*top p A R) :=
  le_congr (.eqRefl _) (exact_right_endpoint p A R) (le_add_left (width p A R) one)

theorem compact_input (F : PR 3) (p A R x : PTm n) (h : Γ ⊢[PRAAx] source F p A R x) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input F one (width p A R) (etaDen p A R) (lipschitz p A R) (top p A R) x :=
  .andI (le_refl one) (.andI (GaussianGammaIntegralCutoffs.eta_den_positive p A R) (.andI (width_bound p A R) h))

theorem source_mesh (p A R : PTm n) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.mesh p (lipschitz p A R) (top p A R) ≐ cells p A R := .eqRefl _

theorem fixed_interval_name (F : PR 3) (p A R x : PTm n) (h : Γ ⊢[PRAAx] source F p A R x) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN (GaussianCompactRiemannName.nameF F) (data p A R x) :=
  GaussianCompactRiemannName.name_regular F _ _ _ _ _ _ (compact_input F p A R x h)

theorem source_diagonal_sample (F : PR 3) (p A R x : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.nameF F) p (data p A R x) ≐
      quadrature F (p+top p A R+num 6) (cells p A R) one (width p A R) (etaDen p A R) x :=
  GaussianCompactRiemannName.name_at F p _ _ _ _ _ _

def output (F : PR 3) (p A R x : PTm n) : PTm n := pairT
  (ap2 (GaussianCompactRiemannName.nameF F) p (data p A R x)) (pairT (cells p A R) (etaDen p A R))
def outputF (F : PR 3) : PR 4 := PTm.toPR (output F (var 0) (var 1) (var 2) (var 3))
def run (F : PR 3) (p A R x : PTm n) : PTm n := PTm.app (outputF F) ![p,A,R,x]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (p A R x : PTm n) :
    Syn.subst σ (output F p A R x) = output F (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ x) := by
  simp [output,cells,GaussianGammaIntegralCutoffs.meshCost,lipschitz,etaDen,top,
    GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
theorem program_at (F : PR 3) (p A R x : PTm n) : Γ ⊢[PRAAx] run F p A R x ≐ output F p A R x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output F (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,A,R,x]
theorem returned_sample (F : PR 3) (p A R x : PTm n) : Γ ⊢[PRAAx]
    fstT (run F p A R x) ≐ quadrature F (p+top p A R+num 6) (cells p A R) one (width p A R) (etaDen p A R) x :=
  (congrFst (program_at F p A R x)).eqTrans ((fst_pair _ _).eqTrans (source_diagonal_sample F p A R x))

theorem actual_source_compact_interval_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (one+width (var 0) (var 1) (var 2) ≐ etaDen (var 0) (var 1) (var 2)*top (var 0) (var 1) (var 2)) :=
  closeUniv 3 (exact_right_endpoint _ _ _)
theorem actual_source_compact_fixed_interval_name_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source F (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianEuclideanDistanceName.pointCN (GaussianCompactRiemannName.nameF F) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (fixed_interval_name F _ _ _ _ Prf.hyp0))
theorem actual_source_diagonal_mesh_sampler_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (GaussianCompactRiemannName.nameF F) (var 0) (data (var 0) (var 1) (var 2) (var 3)) ≐
      quadrature F (var 0+top (var 0) (var 1) (var 2)+num 6) (cells (var 0) (var 1) (var 2))
        one (width (var 0) (var 1) (var 2)) (etaDen (var 0) (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (source_diagonal_sample F _ _ _ _)
theorem actual_source_compact_quadrature_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run F (var 0) (var 1) (var 2) (var 3) ≐ output F (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at F _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCompactQuadratureBoundary
