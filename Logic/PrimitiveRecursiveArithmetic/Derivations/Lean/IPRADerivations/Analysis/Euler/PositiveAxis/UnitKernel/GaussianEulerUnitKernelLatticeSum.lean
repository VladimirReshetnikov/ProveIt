import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelCompactName

/-!
# The original rational unit kernel on a uniform rational lattice

The left numerator, length, denominator and observation precision are
independent numerical data. Each term is the unchanged original
rational kernel evaluated at (a+i)/M. The final uniform scale is 1/M.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelLatticeSum

open_ipra
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul)
open GaussianRationalFiniteSum (sum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def row (i p z B a M : PTm n) : PTm n :=
  ap2 GaussianEulerUnitSubstitutionKernel.nameF p (GaussianEulerUnitSubstitutionKernel.data z B (a+i) M)
def body : PTm 2 := row (var 0) (field0 (var 1)) (field2 (var 1)) (field3 (var 1)) (field1 (var 1)) (field4 (var 1))
def data (p z B a M : PTm n) : PTm n := sampleData p a z B M zero
def lattice (p K z B a M : PTm n) : PTm n := qmul (fraction one M) (sum body K (data p z B a M))

ipra_subst row
ipra_subst data
ipra_subst lattice

theorem row_at (i p z B a M : PTm n) : Γ ⊢[PRAAx] inst2 body i (data p z B a M) ≐ row i p z B a M := by
  let d := data p z B a M
  ipra_congr (row (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl i, (show _ ⊢[PRAAx] field0 d ≐ p from GaussianCompactRiemannName.field0_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field2 d ≐ z from GaussianCompactRiemannName.field2_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field3 d ≐ B from GaussianCompactRiemannName.field3_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field1 d ≐ a from GaussianCompactRiemannName.field1_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field4 d ≐ M from GaussianCompactRiemannName.field4_at _ _ _ _ _ _)] using [body, inst2, d]

def sumF : PR 6 := PTm.toPR (lattice (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (p K z B a M : PTm n) : PTm n := PTm.app sumF ![p,K,z,B,a,M]

theorem program_at (p K z B a M : PTm n) : Γ ⊢[PRAAx] run p K z B a M ≐ lattice p K z B a M := by
  simpa [run,sumF] using toPR_eq (Γ := Γ)
    (lattice (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![p,K,z,B,a,M]

theorem actual_original_unit_kernel_lattice_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (inst2 body (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5)) ≐
      row (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (row_at _ _ _ _ _ _)

theorem actual_original_unit_kernel_lattice_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ lattice (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelLatticeSum
