import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPowerIntegralMesh
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPanelPartsOuterFold

/-!
# Exact antiderivative comparisons for the original outer mass prefix

The corrected primitive relates successive unit panels and telescopes
through the actual outer fold. The finite error depends on the mesh
alone. The pure integral from the original rational input to infinity
is the starting rational primitive with an explicit cutoff error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianFactorBudget (power_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderFirstPanelReadback (upper_of_add_order)
open GaussianStirlingAllOrderPanelPartsOuterFold (massPrefix mass_succ)
open GaussianStirlingAllOrderPowerIntegralMesh (brackets join_brackets upperPrimitive panel_integral_brackets)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive primitive_canonical endpointSample)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open RationalAlgebra (add_congr add_commutative add_associative multiply_congr positive_product)
open RationalArithmetic (add add_guard)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalGaussianEmbedding (embed)
open RationalGaussianNameEmbedding (distance_from_radius)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalReciprocalPowerTail (add_zero_right zero_fraction)
open RationalValueBounds (radius_of_upper upper_of_order)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def prefixLaw (e : ℕ) (A B M L : PTm n) : Fm PTm n :=
  brackets (primitive e A B) (primitive e (A+B*L) B)
    (upperPrimitive e A B M) (upperPrimitive e (A+B*L) B M) (massPrefix e A B M L)

@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (e : ℕ) (A B M L : PTm n) :
    (prefixLaw e A B M L).subst σ =
      prefixLaw e (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ M) (Syn.subst σ L) :=
  by simp [prefixLaw]

private theorem input_readback (e : ℕ) (U V B M : PTm n) (h : Γ ⊢[PRAAx] U ≐ V) :
    (Γ ⊢[PRAAx] primitive e U B ≐ primitive e V B) ∧
      (Γ ⊢[PRAAx] upperPrimitive e U B M ≐ upperPrimitive e V B M) := by
  have p : Γ ⊢[PRAAx] primitive e U B ≐ primitive e V B :=
    fraction_congr (.eqRefl _) (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) h))
  have w : Γ ⊢[PRAAx] endpointSample e U B M ≐ endpointSample e V B M :=
    multiply_congr (.eqRefl _) (fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) h))
  exact ⟨p,add_congr p w⟩

private theorem prefix_zero (e : ℕ) (he : 2≤e) (A B M : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] prefixLaw e A B M zero := by
  let x := primitive e A B
  let y := upperPrimitive e A B M
  have row := input_readback (Γ := Γ) e (A+B*zero) A B M (by ipra_ring)
  have eq : Γ ⊢[PRAAx] massPrefix e A B M zero ≐ fraction zero one :=
    (RationalFiniteSum.sum_zero _ _).eqTrans zero_fraction.eqSymm
  have z (u v : PTm n) (r : Γ ⊢[PRAAx] u ≐ v) (hv : Γ ⊢[PRAAx] RationalNormalForm.wellFormed v) :
      Γ ⊢[PRAAx] add (massPrefix e A B M zero) u ≐ v :=
    (add_congr eq r).eqTrans ((add_commutative _ _).eqTrans (add_zero_right _ hv))
  exact .andI (rationalLE_congr (.eqRefl x) (z _ _ row.1 (primitive_canonical e he A B hA)).eqSymm (reflexive x))
    (rationalLE_congr (z _ _ row.2 (add_guard _ _)).eqSymm (.eqRefl y) (reflexive y))

private theorem prefix_step (e : ℕ) (he : 2≤e) (A B M L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M)
    (ih : Γ ⊢[PRAAx] prefixLaw e A B M L) :
    Γ ⊢[PRAAx] prefixLaw e A B M (succ L) := by
  let U := A+B*L
  have hU : Γ ⊢[PRAAx] le one U := le_trans hA (le_add_right _ _)
  have h := panel_integral_brackets e he U B M hU hM
  have read := input_readback (Γ := Γ) e (U+B) (A+B*succ L) B M (by dsimp [U]; ipra_ring)
  have step : Γ ⊢[PRAAx] brackets (primitive e U B) (primitive e (A+B*succ L) B)
      (upperPrimitive e U B M) (upperPrimitive e (A+B*succ L) B M)
      (GaussianStirlingAllOrderPanelPartsRecurrence.panelMass e U B M) :=
    .andI (rationalLE_congr (.eqRefl _) (add_congr (.eqRefl _) read.1) h.andE₁)
      (rationalLE_congr (add_congr (.eqRefl _) read.2) (.eqRefl _) h.andE₂)
  exact join_brackets _ _ _ _ _ _ _ _ _ ih step (mass_succ e A B M L).eqSymm

theorem prefix_integral_brackets (e : ℕ) (he : 2≤e) (A B M L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] prefixLaw e A B M L := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw e (Syn.shift A) (Syn.shift B) (Syn.shift M) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero e he A B M hA
    · simp only [subst_prefixLaw,subst_repl_shift,Syn.subst_var,Syn.repl_zero]
      let δ := prefixLaw e (Syn.shift A) (Syn.shift B) (Syn.shift M) (var 0)
      let Δ := δ :: Γ.map Fm.shift
      have a : Δ ⊢[PRAAx] le one (Syn.shift A) := by
        simpa [Δ,Fm.shift,Syn.shift,one] using hA.shift.wk
      have m : Δ ⊢[PRAAx] le one (Syn.shift M) := by
        simpa [Δ,Fm.shift,Syn.shift,one] using hM.shift.wk
      exact prefix_step e he _ _ _ _ a m Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE L

theorem endpoint_sample_bounds (e : ℕ) (A B M : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (endpointSample e A B M) ⋏
      rationalLE (endpointSample e A B M) (fraction (power e B) M) := by
  let P := power e A
  let C := power e B
  have hP : Γ ⊢[PRAAx] le one P := power_positive _ _ hA
  have hD := positive_product hM hP
  have eq : Γ ⊢[PRAAx] endpointSample e A B M ≐ fraction C (M*P) :=
    (fraction_multiply _ _ _ _ hM hP).eqTrans (fraction_congr (one_mul _) (.eqRefl _))
  have lo := fraction_order zero one C (M*P) (le_refl one) hD (by ipra_le 𝔞(C))
  have hi := fraction_order C (M*P) C M hD hM
    (by ipra_le 𝔞(C)*𝔞(M)*sl hP)
  exact .andI (rationalLE_congr (.eqRefl _) eq.eqSymm lo) (rationalLE_congr eq.eqSymm (.eqRefl _) hi)

theorem corrected_prefix_bounds (e : ℕ) (he : 2≤e) (A B M L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] rationalLE (primitive e A B) (add (massPrefix e A B M L) (primitive e (A+B*L) B)) ⋏
      rationalLE (add (massPrefix e A B M L) (primitive e (A+B*L) B))
        (add (primitive e A B) (fraction (power e B) M)) := by
  let W := A+B*L
  let P := massPrefix e A B M L
  let v := primitive e W B
  let x := add P v
  have hW : Γ ⊢[PRAAx] le one W := le_trans hA (le_add_right _ _)
  have bound := prefix_integral_brackets e he A B M L hA hM
  have c := endpoint_sample_bounds e W B M hW hM
  have monotone := add_monotone x x _ _ (reflexive x) c.andE₁
  have grow : Γ ⊢[PRAAx] rationalLE x (add P (upperPrimitive e W B M)) :=
    rationalLE_congr (add_zero_right _ (add_guard _ _)) (add_associative _ _ _) monotone
  have endCap := add_monotone (primitive e A B) _ _ _ (reflexive _) (endpoint_sample_bounds e A B M hA hM).andE₂
  exact .andI bound.andE₁ (transitive grow (transitive bound.andE₂ endCap))

theorem prefix_distance (e : ℕ) (he : 2≤e) (A B M L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded (embed (add (massPrefix e A B M L) (primitive e (A+B*L) B)))
      (embed (primitive e A B)) (power e B) M := by
  have h := corrected_prefix_bounds e he A B M L hA hM
  exact distance_from_radius _ _ _ _ hM
    (radius_of_upper _ _ _ _ (upper_of_add_order _ _ _ _ hM h.andE₂) (upper_of_order _ _ _ _ h.andE₁))

theorem actual_original_reciprocal_mass_prefix_distance_closed (e : ℕ) (he : 2≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (le one (var 0) ⟶ le one (var 2) ⟶
      distanceBounded (embed (add (massPrefix e (var 0) (var 1) (var 2) (var 3))
        (primitive e (var 0+var 1*var 3) (var 1))))
        (embed (primitive e (var 0) (var 1))) (power e (var 1)) (var 2)) :=
  closeUniv 4 (.impI (.impI (prefix_distance e he _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralPrefix
