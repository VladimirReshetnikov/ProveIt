import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffGeometry

/-!
# Exact common-step partition from the original deep eta to N

The original eta denominator refinement gives the lower and middle
widths. A literal additional upper width reaches the finite beta degree
N. The original middle interval keeps its original earlier denominator
after cancelling the exact refinement ratio. Every mesh count is an
explicit positive natural multiple; taking the shared mesh to contain
the old original mesh makes its divisibility witness literal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaIntegralCutoffPartition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen top cells)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaCompactCutoffGeometry (ratio lowerWidth middleWidth)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (deep A R : PTm n) : PTm n := etaDen deep A R
def upperWidth (k deep A R N : PTm n) : PTm n := denominator deep A R*monus N (top k A R)
def totalWidth (k deep A R N : PTm n) : PTm n := lowerWidth k deep A+middleWidth k deep A R+upperWidth k deep A R N
def commonMesh (k A R extra : PTm n) : PTm n := cells k A R*extra
def lowerCells (k deep A K : PTm n) : PTm n := lowerWidth k deep A*K
def middleCells (k deep A R K : PTm n) : PTm n := middleWidth k deep A R*K
def upperCells (k deep A R N K : PTm n) : PTm n := upperWidth k deep A R N*K
def totalCells (k deep A R N K : PTm n) : PTm n := totalWidth k deep A R N*K
def source (k deep A R N : PTm n) : Fm PTm n := le one A ⋏ (lt k deep ⋏ lt (top k A R) N)
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (deep A R : PTm n) :
    Syn.subst σ (denominator deep A R) = denominator (Syn.subst σ deep) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [denominator,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_upperWidth {l : ℕ} (σ : Fin n → PTm l) (k deep A R N : PTm n) :
    Syn.subst σ (upperWidth k deep A R N) = upperWidth (Syn.subst σ k) (Syn.subst σ deep) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [upperWidth,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_totalWidth {l : ℕ} (σ : Fin n → PTm l) (k deep A R N : PTm n) :
    Syn.subst σ (totalWidth k deep A R N) = totalWidth (Syn.subst σ k) (Syn.subst σ deep) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) := by simp [totalWidth]

theorem denominator_positive (deep A R : PTm n) : Γ ⊢[PRAAx] le one (denominator deep A R) :=
  GaussianGammaIntegralCutoffs.eta_den_positive _ _ _

theorem exact_denominator_refinement (k deep A R : PTm n) (h : Γ ⊢[PRAAx] le k deep) : Γ ⊢[PRAAx]
    denominator deep A R ≐ ratio k deep A*etaDen k A R :=
  GaussianGammaCompactCutoffGeometry.eta_den_refinement _ _ _ _ h

theorem lower_positive (k deep A R N : PTm n) (h : Γ ⊢[PRAAx] source k deep A R N) : Γ ⊢[PRAAx] le one (lowerWidth k deep A) :=
  GaussianGammaCompactCutoffGeometry.lower_positive _ _ _ h.andE₁ h.andE₂.andE₁
theorem middle_positive (k deep A R : PTm n) : Γ ⊢[PRAAx] le one (middleWidth k deep A R) :=
  GaussianGammaCompactCutoffGeometry.middle_positive _ _ _ _
theorem upper_positive (k deep A R N : PTm n) (h : Γ ⊢[PRAAx] source k deep A R N) : Γ ⊢[PRAAx] le one (upperWidth k deep A R N) :=
  positive_product _ _ (denominator_positive _ _ _) (GaussianGammaCompactCutoffGeometry.gap_positive _ _ h.andE₂.andE₂)
theorem degree_positive (k deep A R N : PTm n) (h : Γ ⊢[PRAAx] source k deep A R N) : Γ ⊢[PRAAx] le one N :=
  le_trans (GaussianGammaIntegralCutoffs.top_positive k A R) (le_of_lt h.andE₂.andE₂)
theorem total_positive (k deep A R N : PTm n) (h : Γ ⊢[PRAAx] source k deep A R N) : Γ ⊢[PRAAx] le one (totalWidth k deep A R N) :=
  le_trans (le_trans (lower_positive _ _ _ _ _ h) (le_add_right _ _)) (le_add_right _ _)

theorem lower_endpoint (k deep A : PTm n) : Γ ⊢[PRAAx] one+lowerWidth k deep A ≐ ratio k deep A :=
  GaussianGammaCompactCutoffGeometry.lower_endpoint _ _ _
theorem middle_endpoint (k deep A R : PTm n) (h : Γ ⊢[PRAAx] le k deep) : Γ ⊢[PRAAx]
    one+(lowerWidth k deep A+middleWidth k deep A R) ≐ denominator deep A R*top k A R :=
  (by ipra_ring : Γ ⊢[PRAAx] one+(lowerWidth k deep A+middleWidth k deep A R) ≐ (one+lowerWidth k deep A)+middleWidth k deep A R).eqTrans
    ((congrAdd (lower_endpoint _ _ _) (.eqRefl _)).eqTrans (GaussianGammaCompactCutoffGeometry.middle_endpoint _ _ _ _ h))

theorem total_endpoint (k deep A R N : PTm n) (h : Γ ⊢[PRAAx] source k deep A R N) : Γ ⊢[PRAAx]
    one+totalWidth k deep A R N ≐ denominator deep A R*N :=
  (by unfold totalWidth; ipra_ring : Γ ⊢[PRAAx] one+totalWidth k deep A R N ≐
    (one+(lowerWidth k deep A+middleWidth k deep A R))+upperWidth k deep A R N).eqTrans
      ((congrAdd (middle_endpoint _ _ _ _ (le_of_lt h.andE₂.andE₁)) (.eqRefl _)).eqTrans
        ((by unfold upperWidth; ipra_ring : Γ ⊢[PRAAx] denominator deep A R*top k A R+upperWidth k deep A R N ≐
          denominator deep A R*(top k A R+monus N (top k A R))).eqTrans
            (congrMul (.eqRefl _) (eq_add_of_le (le_of_lt h.andE₂.andE₂)).eqSymm)))

theorem total_is_original_width (k deep A R N : PTm n) (h : Γ ⊢[PRAAx] source k deep A R N) : Γ ⊢[PRAAx]
    totalWidth k deep A R N ≐ monus (denominator deep A R*N) one :=
  ((congrMonus (total_endpoint _ _ _ _ _ h).eqSymm (.eqRefl one)).eqTrans (add_monus' _ _)).eqSymm

theorem original_middle_count (k deep A R K : PTm n) : Γ ⊢[PRAAx]
    middleCells k deep A R K ≐ width k A R*(ratio k deep A*K) := by unfold middleCells middleWidth; ipra_ring
theorem original_shared_mesh_positive (k A R extra : PTm n) (h : Γ ⊢[PRAAx] le one extra) : Γ ⊢[PRAAx] le one (commonMesh k A R extra) :=
  positive_product _ _ (GaussianGammaIntegralCutoffs.mesh_positive _ _ _) h
theorem original_middle_mesh_divisibility (k deep A R extra : PTm n) : Γ ⊢[PRAAx]
    middleCells k deep A R (commonMesh k A R extra) ≐ cells k A R*(width k A R*ratio k deep A*extra) := by
  unfold middleCells commonMesh middleWidth; ipra_ring
theorem original_full_mesh_divisibility (k deep A R N extra : PTm n) : Γ ⊢[PRAAx]
    totalCells k deep A R N (commonMesh k A R extra) ≐ cells k A R*(totalWidth k deep A R N*extra) := by
  unfold totalCells commonMesh; ipra_ring
theorem exact_sum_of_cells (k deep A R N K : PTm n) : Γ ⊢[PRAAx]
    lowerCells k deep A K+middleCells k deep A R K+upperCells k deep A R N K ≐ totalCells k deep A R N K := by
  unfold lowerCells middleCells upperCells totalCells totalWidth; ipra_ring

def output (k deep A R N K : PTm n) : PTm n := pairT (denominator deep A R)
  (pairT (lowerCells k deep A K) (pairT (middleCells k deep A R K)
    (pairT (upperCells k deep A R N K) (totalCells k deep A R N K))))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (k deep A R N K : PTm n) : PTm n := PTm.app outputF ![k,deep,A,R,N,K]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (k deep A R N K : PTm n) :
    Syn.subst σ (output k deep A R N K) = output (Syn.subst σ k) (Syn.subst σ deep) (Syn.subst σ A)
      (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ K) := by
  simp [output,lowerCells,middleCells,upperCells,totalCells]
theorem program_at (k deep A R N K : PTm n) : Γ ⊢[PRAAx] run k deep A R N K ≐ output k deep A R N K := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![k,deep,A,R,N,K]

theorem original_deep_eta_to_N_partition_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      one+totalWidth (var 0) (var 1) (var 2) (var 3) (var 4) ≐ denominator (var 1) (var 2) (var 3)*var 4) :=
  closeUniv 5 (.impI (total_endpoint _ _ _ _ _ Prf.hyp0))
theorem original_middle_mesh_count_refines_original_cells_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (middleCells (var 0) (var 1) (var 2) (var 3) (commonMesh (var 0) (var 2) (var 3) (var 4)) ≐
      cells (var 0) (var 2) (var 3)*(width (var 0) (var 2) (var 3)*ratio (var 0) (var 1) (var 2)*var 4)) :=
  closeUniv 5 (original_middle_mesh_divisibility _ _ _ _ _)
theorem original_deep_beta_partition_mesh_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBetaIntegralCutoffPartition
