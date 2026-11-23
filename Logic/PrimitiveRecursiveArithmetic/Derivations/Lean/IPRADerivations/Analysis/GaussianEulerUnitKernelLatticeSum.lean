import IPRADerivations.Analysis.GaussianEulerUnitKernelCompactName

/-!
# The original rational unit kernel on a uniform rational lattice

The left numerator, length, denominator and observation precision are
independent numerical data. Each term is the unchanged original
rational kernel evaluated at (a+i)/M. The final uniform scale is 1/M.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelLatticeSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul)
open GaussianRationalFiniteSum (sum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def row (i p z B a M : PTm n) : PTm n :=
  ap2 GaussianEulerUnitSubstitutionKernel.nameF p (GaussianEulerUnitSubstitutionKernel.data z B (a+i) M)
def body : PTm 2 := row (var 0) (field0 (var 1)) (field2 (var 1)) (field3 (var 1)) (field1 (var 1)) (field4 (var 1))
def data (p z B a M : PTm n) : PTm n := sampleData p a z B M zero
def lattice (p K z B a M : PTm n) : PTm n := qmul (fraction one M) (sum body K (data p z B a M))

@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (i p z B a M : PTm n) :
    Syn.subst σ (row i p z B a M) = row (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ M) := by simp [row]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p z B a M : PTm n) :
    Syn.subst σ (data p z B a M) = data (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ M) :=
  by simp [data]
@[simp] theorem subst_lattice {m : ℕ} (σ : Fin n → PTm m) (p K z B a M : PTm n) :
    Syn.subst σ (lattice p K z B a M) = lattice (Syn.subst σ p) (Syn.subst σ K) (Syn.subst σ z)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ M) := by simp [lattice]

theorem row_at (i p z B a M : PTm n) : Γ ⊢[PRAAx] inst2 body i (data p z B a M) ≐ row i p z B a M := by
  let d := data p z B a M
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (row (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![i,field0 d,field2 d,field3 d,field1 d,field4 d]) (σ' := ![i,p,z,B,a,M])
    (fun j => by
      fin_cases j
      exact .eqRefl _
      exact GaussianCompactRiemannName.field0_at _ _ _ _ _ _
      exact GaussianCompactRiemannName.field2_at _ _ _ _ _ _
      exact GaussianCompactRiemannName.field3_at _ _ _ _ _ _
      exact GaussianCompactRiemannName.field1_at _ _ _ _ _ _
      exact GaussianCompactRiemannName.field4_at _ _ _ _ _ _)
  simpa [body,inst2,d] using fields

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
