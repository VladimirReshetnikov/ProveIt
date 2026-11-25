import IPRADerivations.Analysis.GaussianBinetWeightedExponentialRowRate
import IPRADerivations.Analysis.GaussianBinetWeightedExponential

/-!
# Uniform finite readback of the original weighted Binet quadrature

A common finite refinement compares an arbitrary unit mesh with the
actual cofinal mesh queried by the original sampler. The estimate
depends on the upper time horizon and remains valid at zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialUniform

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetWeightedExponentialGrid (evaluatorF value cell_at)
open GaussianBinetWeightedExponentialRowRate (gain numerator row_error subst_gain subst_numerator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid sampleBody sampleData subst_sampleData)
open GaussianNamedInverseRate (rateDenominator subst_rateDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (cellDistances refinement)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def readBudget (p M T : PTm n) : PTm n := gain T*unit p+(gain T+num 8)*M

@[simp] theorem subst_readBudget {m : ℕ} (σ : Fin n → PTm m) (p M T : PTm n) :
    Syn.subst σ (readBudget p M T) = readBudget (Syn.subst σ p) (Syn.subst σ M) (Syn.subst σ T) := by
  simp [readBudget]

theorem tag_distance (i R N : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (fraction i (R*N)) (fraction (quo i R) N) one N := by
  let v : PTm n → PTm n := GaussianCompactRiemannName.value
  have read (j M : PTm n) : Γ ⊢[PRAAx] v (grid j M zero one one) ≐ fraction j M :=
    (GaussianCompactRiemannName.value_grid j M zero one one).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (one_mul M))
  exact distance_congr (read i (R*N)) (read (quo i R) N) (.eqRefl _) (one_mul N)
    (GaussianCompactRiemannName.grid_distance i R N zero one one hR hN (le_refl one))

theorem refinement_error (p q R N a b T : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hN : Γ ⊢[PRAAx] le one N)
    (hb : Γ ⊢[PRAAx] le one b) (hT : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] distanceBounded (value p (R*N) a b) (value q N a b)
      (numerator p q T one N) (rateDenominator N p q) := by
  let f := sampleBody evaluatorF
  let x := sampleData p (R*N) one one one (pairT a b)
  let y := sampleData q N one one one (pairT a b)
  let A := numerator p q T one N
  let D := rateDenominator N p q
  have cells : Γ ⊢[PRAAx] cellDistances f f N R x y A D := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (s R*s N)::Γ.map Fm.shift
    have hsR : Δ ⊢[PRAAx] le one (s R) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hR.shift.wk
    have hsN : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have hsB : Δ ⊢[PRAAx] le one (s b) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hb.shift.wk
    have hsT : Δ ⊢[PRAAx] le (s a) (s T*s b) := by simpa [Δ,s,Fm.shift,Syn.shift] using hT.shift.wk
    have hi : Δ ⊢[PRAAx] lt (var 0) (s R*s N) := Prf.hyp0
    have near := tag_distance (var 0) (s R) (s N) hsR hsN
    have row := row_error (s p) (s q) (s a) (s b) (var 0) (s R*s N) (quo (var 0) (s R)) (s N)
      (s T) one (s N) hsB hsT (positive_product _ _ hsR hsN) (le_of_lt hi) hsN
      (le_of_lt (GaussianCompactRiemannName.coarse_bound _ _ _ hsR hi)) hsN near
    simpa only [s,Δ,Syn.shift,f,x,y,A,D,subst_sampleData,subst_numerator,subst_rateDenominator,PTm.subst_mul,subst_pairT,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      distance_congr (cell_at _ _ _ _ _).eqSymm (cell_at _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) row
  exact distance_congr (.eqRefl _) (.eqRefl _) (one_mul A) (one_mul D)
    (refinement f f N R x y one one A D hN hR (le_refl one)
      (GaussianNamedInverseRate.denominator_positive N p q hN) cells)

private theorem value_congr (p M N a b : PTm n) (e : Γ ⊢[PRAAx] M ≐ N) :
    Γ ⊢[PRAAx] value p M a b ≐ value p N a b :=
  GaussianCompactRiemannName.quadrature_index_congr evaluatorF p M N one one one (pairT a b) e

theorem finite_readback (p M a b T : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hb : Γ ⊢[PRAAx] le one b) (hT : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianBinetWeightedExponential.nameF p (GaussianBinetWeightedExponential.data a b))
      (value p M a b) (readBudget p M T) (M*unit p) := by
  let s := GaussianBinetWeightedExponential.clock p a b
  let N := GaussianBinetWeightedExponential.mesh s a
  let r := s+N
  let L := gain T
  let P := unit p
  let U := unit r
  let E := M*P
  have hP := unit_positive (Γ := Γ) p
  have hE := positive_product _ _ hM hP
  have later : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have hNp : Γ ⊢[PRAAx] le P N :=
    le_trans (GaussianExponentialReference.unit_monotone later) (le_add_left _ _)
  have hN := le_trans hP hNp
  have grow : Γ ⊢[PRAAx] le P U :=
    GaussianExponentialReference.unit_monotone (le_trans later (le_add_right s N))
  have fineCoarse := refinement_error r p N M a b T hN hM hb hT
  have fineActual := refinement_error r r M N a b T hM hN hb hT
  have first : Γ ⊢[PRAAx] distanceBounded (value r (N*M) a b) (value p M a b) (L*P+num 4*M) E := by
    apply distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive M r p hM) hE ?_ fineCoarse
    dsimp only [numerator,rateDenominator,E,L,P,U]
    ipra_le 2*𝔞(M*M*unit p)*sl grow
  have second : Γ ⊢[PRAAx] distanceBounded (value r (M*N) a b) (value r N a b) ((L+num 4)*M) E := by
    apply distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive N r r hN) hE ?_ fineActual
    dsimp only [numerator,rateDenominator,E]
    ipra_le 𝔞(gain T)*𝔞(M*U*U)*sl hNp+4*𝔞(M*N*U)*sl grow
  have ordered := distance_congr (value_congr r (M*N) (N*M) a b (mul_comm M N)) (.eqRefl _) (.eqRefl _) (.eqRefl _) second
  have joined := distance_triangle_same _ _ _ _ _ _ hE (distance_symmetric _ _ _ _ hE ordered) first
  exact distance_congr (GaussianBinetWeightedExponential.sample_at p a b).eqSymm (.eqRefl _)
    (by dsimp only [readBudget,L,P]; ipra_ring) (.eqRefl _) joined

theorem actual_weighted_Binet_finite_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ le (var 2) (var 4*var 3) ⟶
      distanceBounded
        (ap2 GaussianBinetWeightedExponential.nameF (var 0) (GaussianBinetWeightedExponential.data (var 2) (var 3)))
        (value (var 0) (var 1) (var 2) (var 3)) (readBudget (var 0) (var 1) (var 4)) (var 1*unit (var 0))) :=
  closeUniv 5 (.impI (.impI (.impI (finite_readback _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialUniform
