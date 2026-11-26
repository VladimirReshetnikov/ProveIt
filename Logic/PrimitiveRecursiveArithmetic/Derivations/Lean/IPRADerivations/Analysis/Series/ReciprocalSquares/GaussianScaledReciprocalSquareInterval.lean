import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareInterval
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperEndpointInverse
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalInverseQuadraticAlgebra

/-!
# Exact inverse-square telescope with a fixed additional denominator

Scale every term by the positive common factor before applying the
existing inverse-square sum theorem. The exact finite scaling law
then restores the original sum and the common denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianScaledReciprocalSquareInterval

open_ipra
open ComplexLogarithmRemainder (oneCode normSq_one)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply sum_canonical)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianReciprocalSquareInterval (rowsBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rows (t : PTm 2) (N C D x : PTm n) : Fm PTm n := .all
  (bounded (inst2 t (var 0) (Syn.shift x)) (Syn.shift C)
    (Syn.shift D*(succ (Syn.shift N+var 0)*succ (Syn.shift N+var 0))))

@[simp] theorem subst_rows {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (N C D x : PTm n) :
    (rows t N C D x).subst σ = rows t (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ x) := by
  simp [rows,Syn.subst_shift,Syn.shift_subst]

theorem row_at (t : PTm 2) (N C D x i : PTm n) (h : Γ ⊢[PRAAx] rows t N C D x) :
    Γ ⊢[PRAAx] bounded (inst2 t i x) C (D*(succ (N+i)*succ (N+i))) := by
  simpa only [rows,GaussianRationalMetric.subst_bounded,subst_inst2,PTm.subst_mul,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

private theorem scale_bound (D C K q : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] bounded q C (D*K)) : Γ ⊢[PRAAx] bounded (qmul (naturalPoint D) q) C K := by
  have hDK := positive_product D K hD hK
  have prod := bounded_product (naturalPoint D) q D one C (D*K) (le_refl one) hDK
    (GaussianNamedNaturalScale.natural_point_bound D) h
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hDK) hK
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) prod

private theorem scaled_rows (t : PTm 2) (N C D x : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rows t N C D x) :
    Γ ⊢[PRAAx] rowsBounded (multiplyBody t) N C (pairT (naturalPoint D) x) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  let k := succ (sh N+i)
  have hd : Δ ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hD.shift
  have hh : Δ ⊢[PRAAx] rows t (sh N) (sh C) (sh D) (sh x) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  have hk : Δ ⊢[PRAAx] le one k := zero_lt_succ _
  have b := scale_bound (sh D) (sh C) (k*k) (inst2 t i (sh x)) hd (positive_product _ _ hk hk)
    (row_at t (sh N) (sh C) (sh D) (sh x) i hh)
  simpa only [rowsBounded,Syn.shift,sh,Δ,i,k,subst_pairT,GaussianRationalNaturalScale.subst_naturalPoint] using
    bound_congr (multiply_body_at t (naturalPoint (sh D)) i (sh x)).eqSymm (.eqRefl _) (.eqRefl _) b

private theorem inverse_bound (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (ofGaussian oneCode D) one D :=
  bounded_of_cleared _ _ _ _ _ hD hD (ofGaussian_represents oneCode D hD)
    (le_congr (congrMul (.eqRefl (D*D)) normSq_one).eqSymm (by ipra_ring) (le_refl (D*D*one)))

theorem tail_bound (t : PTm 2) (N r C D x : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rows t N C D x) :
    Γ ⊢[PRAAx] bounded (sum t r x) C (D*N) := by
  let a := naturalPoint D
  let b := ofGaussian oneCode D
  let v := sum t r x
  have sumBound := GaussianReciprocalSquareInterval.tail_bound (multiplyBody t) N r C (pairT a x)
    hN (scaled_rows t N C D x hD h)
  have bv := bound_congr (sum_multiply t a r x) (.eqRefl _) (.eqRefl _) sumBound
  have prod := bounded_product b (qmul a v) one D C N hD hN (inverse_bound D hD) bv
  have unit : Γ ⊢[PRAAx] qmul b a ≐ GaussianRationalReciprocal.qone :=
    (qmul_commutative b a).eqTrans (GaussianBetaUpperEndpointInverse.natural_reciprocal_one D hD)
  have restore := GaussianRationalInverseQuadraticAlgebra.cancel_nested_product b a v (sum_canonical t r x) unit
  exact bound_congr restore (one_mul C) (.eqRefl _) prod

theorem actual_scaled_reciprocal_square_tail_closed (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let N := var 0
       let r := var 1
       let C := var 2
       let D := var 3
       let x := var 4
       (le one N ⋏ (le one D ⋏ rows t N C D x)) ⟶ bounded (sum t r x) C (D*N)) :=
  closeUniv 5 (.impI (tail_bound t _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianScaledReciprocalSquareInterval
