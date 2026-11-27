import IPRADerivations.Analysis.Integration.Partitions.GaussianPartitionedFiniteSumDistance
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameArithmetic

/-!
# Partitioned Gaussian sum error weighted by the actual total cut count

The error at each original prefix is its actual fine count times the
local row radius. A genuine guarded QF induction telescopes the exact
native block lengths, so no maximum block-size certificate is needed.
Multiplying both original sums by 1/M gives the unamplified local radius
when the final cut count is at most M. Empty and repeated cuts are valid.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPartitionedFiniteSumTotalDistance

open_ipra
open GaussianPartitionedFiniteSum (increasing block cut_step original_prefix_step)
open GaussianPartitionedFiniteSumDistance (blockLength coarseRow coarseBody coarse_at blockAgreement block_error)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qzero qmul positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def prefixLaw (cut : PR 2) (f g : PTm 2) (K d x y A B k : PTm n) : Fm PTm n := le k K ⟶
  distanceBounded (sum f (ap2 cut k d) x) (sum (coarseBody cut g) k (pairT d y)) (ap2 cut k d*A) B

def unitWeight (M : PTm n) : PTm n :=
  GaussianRationalHorner.ofGaussian (ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode) M

ipra_subst prefixLaw
ipra_subst unitWeight

theorem prefix_zero (cut : PR 2) (f g : PTm 2) (d x y A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (h0 : Γ ⊢[PRAAx] ap2 cut zero d ≐ zero) : Γ ⊢[PRAAx]
    distanceBounded (sum f (ap2 cut zero d) x) (sum (coarseBody cut g) zero (pairT d y)) (ap2 cut zero d*A) B := by
  have fine := (GaussianRationalFiniteSum.sum_index_congr f h0 (.eqRefl x)).eqTrans (GaussianRationalFiniteSum.sum_zero f x)
  have radius : Γ ⊢[PRAAx] ap2 cut zero d*A ≐ zero := (congrMul h0 (.eqRefl A)).eqTrans (zero_mul A)
  exact distance_congr fine.eqSymm (GaussianRationalFiniteSum.sum_zero _ _).eqSymm radius.eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qzero B hB)

theorem prefix_step (cut : PR 2) (f g : PTm 2) (K d x y A B k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] increasing cut d)
    (hr : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B) (hk : Γ ⊢[PRAAx] lt k K)
    (ih : Γ ⊢[PRAAx] distanceBounded (sum f (ap2 cut k d) x) (sum (coarseBody cut g) k (pairT d y)) (ap2 cut k d*A) B) :
    Γ ⊢[PRAAx] distanceBounded (sum f (ap2 cut (succ k) d) x) (sum (coarseBody cut g) (succ k) (pairT d y)) (ap2 cut (succ k) d*A) B := by
  have next : Γ ⊢[PRAAx] sum (coarseBody cut g) (succ k) (pairT d y) ≐
      GaussianRationalHorner.qadd (sum (coarseBody cut g) k (pairT d y)) (coarseRow cut g k d y) :=
    (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (coarse_at cut g k d y))
  have total : Γ ⊢[PRAAx] ap2 cut k d*A+blockLength cut k d*A ≐ ap2 cut (succ k) d*A :=
    (by ipra_ring : Γ ⊢[PRAAx] ap2 cut k d*A+blockLength cut k d*A ≐ (ap2 cut k d+blockLength cut k d)*A).eqTrans
      (congrMul (eq_add_of_le (cut_step cut d k hm)).eqSymm (.eqRefl A))
  exact distance_congr (original_prefix_step cut f k d x hm).eqSymm next.eqSymm total (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ B hB ih (block_error cut f g K d x y A B k hB hr hk))

/-- The actual fine prefix and the actual weighted coarse prefix have
error exactly proportional to the actual total fine count. -/
theorem prefix_comparison (cut : PR 2) (f g : PTm 2) (K d x y A B k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] increasing cut d) (h0 : Γ ⊢[PRAAx] ap2 cut zero d ≐ zero)
    (hr : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B) (hk : Γ ⊢[PRAAx] le k K) : Γ ⊢[PRAAx]
    distanceBounded (sum f (ap2 cut k d) x) (sum (coarseBody cut g) k (pairT d y)) (ap2 cut k d*A) B := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] increasing cut (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hm.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] blockAgreement cut f g (Syn.shift K) (Syn.shift d) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift B) :=
    by simpa [Fm.shift,Syn.shift] using hr.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw cut f g (Syn.shift K) (Syn.shift d) (Syn.shift x) (Syn.shift y)
      (Syn.shift A) (Syn.shift B) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_prefixLaw]
    · exact .impI ((prefix_zero cut f g d x y A B hB h0).wk)
    · refine .impI ?_
      exact prefix_step cut f g (Syn.shift K) (Syn.shift d) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift B)
        (var 0) bs.wk.wk ms.wk.wk rs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw cut f g K d x y A B k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem original_comparison (cut : PR 2) (f g : PTm 2) (K d x y A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] increasing cut d) (h0 : Γ ⊢[PRAAx] ap2 cut zero d ≐ zero)
    (hr : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B) : Γ ⊢[PRAAx]
    distanceBounded (sum f (ap2 cut K d) x) (sum (coarseBody cut g) K (pairT d y)) (ap2 cut K d*A) B :=
  prefix_comparison cut f g K d x y A B K hB hm h0 hr (le_refl _)

theorem weighted_total_comparison (cut : PR 2) (f g : PTm 2) (K d x y A B w H D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hm : Γ ⊢[PRAAx] increasing cut d)
    (h0 : Γ ⊢[PRAAx] ap2 cut zero d ≐ zero) (hr : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B)
    (hw : Γ ⊢[PRAAx] bounded w H D) : Γ ⊢[PRAAx]
    distanceBounded (qmul w (sum f (ap2 cut K d) x)) (qmul w (sum (coarseBody cut g) K (pairT d y))) (H*(ap2 cut K d*A)) (D*B) :=
  GaussianRationalRoundedPower.distance_mul_left hD hB hw
    (original_comparison cut f g K d x y A B hB hm h0 hr)

theorem unit_weight_bound (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx] bounded (unitWeight M) one M := by
  have eq := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (GaussianRationalHorner.ofGaussian (var 0) (var 1) : PTm 2)
    (σ := ![ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode,M*one])
    (σ' := ![ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode,M]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact by
        change Γ ⊢[PRAAx] M*one ≐ M
        ipra_ring)
  have actual : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.weight one M one ≐ unitWeight M := by
    simpa [GaussianRationalRiemannRefinement.weight,unitWeight] using eq
  exact GaussianRationalReciprocal.bound_congr actual (.eqRefl _) (by ipra_ring)
    (GaussianRationalRiemannRefinement.weight_bound one M one hM (le_refl one))

/-- Scaling by the genuine original Gaussian fraction 1/M cancels the
actual total row count whenever that final cut count is at most M. -/
theorem scaled_total_comparison (cut : PR 2) (f g : PTm 2) (K d x y A B M : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) (hm : Γ ⊢[PRAAx] increasing cut d)
    (h0 : Γ ⊢[PRAAx] ap2 cut zero d ≐ zero) (hr : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B)
    (hFinal : Γ ⊢[PRAAx] le (ap2 cut K d) M) : Γ ⊢[PRAAx]
    distanceBounded (qmul (unitWeight M) (sum f (ap2 cut K d) x))
      (qmul (unitWeight M) (sum (coarseBody cut g) K (pairT d y))) A B :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hM hB) hB
    (by ipra_le 𝔞 A*𝔞 B*sl hFinal)
    (weighted_total_comparison cut f g K d x y A B (unitWeight M) one M hB hM hm h0 hr (unit_weight_bound M hM))

theorem actual_original_partitioned_total_distance_closed (cut : PR 2) (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 5) ⋏ (increasing cut (var 1) ⋏ (ap2 cut zero (var 1) ≐ zero ⋏ blockAgreement cut f g
      (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ⟶
      distanceBounded (sum f (ap2 cut (var 0) (var 1)) (var 2)) (sum (coarseBody cut g) (var 0) (pairT (var 1) (var 3)))
        (ap2 cut (var 0) (var 1)*var 4) (var 5)) :=
  closeUniv 6 (.impI (original_comparison cut f g _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

theorem actual_scaled_partitioned_total_distance_closed (cut : PR 2) (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 5) ⋏ (le one (var 6) ⋏ (increasing cut (var 1) ⋏ (ap2 cut zero (var 1) ≐ zero ⋏
      (blockAgreement cut f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏ le (ap2 cut (var 0) (var 1)) (var 6)))))) ⟶
      distanceBounded (qmul (unitWeight (var 6)) (sum f (ap2 cut (var 0) (var 1)) (var 2)))
        (qmul (unitWeight (var 6)) (sum (coarseBody cut g) (var 0) (pairT (var 1) (var 3)))) (var 4) (var 5)) :=
  closeUniv 7 (.impI (scaled_total_comparison cut f g _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPartitionedFiniteSumTotalDistance
