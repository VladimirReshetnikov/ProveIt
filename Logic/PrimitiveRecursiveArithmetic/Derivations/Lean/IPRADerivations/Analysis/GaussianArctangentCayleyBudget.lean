import IPRADerivations.Analysis.GaussianGammaHalfPiName
import IPRADerivations.AnalyticNumberTheory.ZetaFiniteContract

/-!
# Dyadic error budget for the arctangent Cayley telescope

The original quadrature mesh dominates the requested dyadic precision.
The exponential stage absorbs the number of mesh increments, so a sum
of local errors bounded by `A/M² + 2^(-s)` has norm at most
`(A+1)/2^p` at the original mesh.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleyBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaHalfPiName (meshAt meshIndex orderAt unit_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open WallisFinite (Dm)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (sum_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def stage (p M : PTm n) : PTm n := p+two*M

@[simp] theorem subst_stage {m : ℕ} (σ : Fin n → PTm m) (p M : PTm n) :
    Syn.subst σ (stage p M) = stage (Syn.subst σ p) (Syn.subst σ M) := by
  simp [stage]

private theorem dm_positive (m : PTm n) : Γ ⊢[PRAAx] le one (Dm m) := by
  have hs : Γ ⊢[PRAAx] le one (succ m) := zero_lt_succ m
  exact positive_product (num 16*unit m) (succ m*succ m)
    (positive_product (num 16) (unit m) (by ipra_le 15) (unit_positive m))
    (positive_product _ _ hs hs)

private theorem unit_le_mesh_index (p : PTm n) : Γ ⊢[PRAAx] le (unit p) (meshIndex p) :=
  le_congr (one_mul _) (.eqRefl _)
    (le_mul_mono (positive_product (num 8) (Dm (orderAt p)) (by ipra_le 7)
      (dm_positive (orderAt p))) (le_refl _))

theorem mesh_two (p : PTm n) : Γ ⊢[PRAAx] le two (meshAt p) := by
  have h := le_trans (unit_positive (Γ := Γ) p) (unit_le_mesh_index p)
  unfold meshAt
  ipra_le sl h

theorem mesh_ge_unit (p : PTm n) : Γ ⊢[PRAAx] le (unit p) (meshAt p) :=
  le_trans (unit_le_mesh_index p) (le_succ_self _)

theorem stage_ge (p M : PTm n) : Γ ⊢[PRAAx] le p (stage p M) :=
  le_add_right _ _

theorem stage_absorbs_mesh (p M : PTm n) : Γ ⊢[PRAAx] le (M*unit p) (unit (stage p M)) := by
  have hstep : Γ ⊢[PRAAx] le M (two*M) := by ipra_le 𝔞 M
  have hg := le_trans (AnalyticNumberTheory.ZetaFiniteContract.le_pow_self M)
    (unit_mono M (two*M) hstep)
  exact le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two p (two*M)).eqSymm)
    (le_mul_mono hg (le_refl (unit p)))

theorem budget (A p M : PTm n) (hm : Γ ⊢[PRAAx] le (unit p) M) :
    Γ ⊢[PRAAx] le (M*(A*unit (stage p M)+(M*M))*unit p)
      ((A+one)*((M*M)*unit (stage p M))) := by
  let U := unit (stage p M)
  have first := le_mul_mono (le_refl (M*(A*U))) hm
  have second := le_mul_mono (le_refl (M*M)) (stage_absorbs_mesh (Γ := Γ) p M)
  exact le_congr (by ipra_ring) (by ipra_ring) (sum_mono first second)

theorem mesh_budget (p : PTm n) : Γ ⊢[PRAAx]
    le (meshAt p*(num 128*unit (stage p (meshAt p))+(meshAt p*meshAt p))*unit p)
      (num 129*((meshAt p*meshAt p)*unit (stage p (meshAt p)))) :=
  le_congr (.eqRefl _) (by ipra_ring) (budget (num 128) p (meshAt p) (mesh_ge_unit p))

theorem actual_original_arctangent_exponential_mesh_budget_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le (meshAt (var 0)*(num 128*unit (stage (var 0) (meshAt (var 0)))+
        (meshAt (var 0)*meshAt (var 0)))*unit (var 0))
        (num 129*((meshAt (var 0)*meshAt (var 0))*unit (stage (var 0) (meshAt (var 0)))))) :=
  closeUniv 1 (mesh_budget _)

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleyBudget
