import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalDirectionIteration
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalDirectionNormalizer

/-!
# Actual rational direction construction from a nonzero original input

The original raw Gaussian-rational input determines the initializer,
positive normalizer and normalized target. The checked numerical clock
supplies every precision and iteration bound. The actual output is unit,
and its kth power is within 1/(4q) of the actual normalized target.
The source's radical-free phase certificate is a further consequence;
it is not an input to this construction or its accuracy proof.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDirectionConstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalDirectionClock (height sixteen eight)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalDirectionNormalizer (norm initial target normalizer)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (four)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def start (c k q : PTm n) : PTm n := initial c (height k q)
def direction (c k q : PTm n) : PTm n := GaussianRationalDirectionIteration.direction (start c k q) k q
def normalized (c k q : PTm n) : PTm n := target c (height k q)
def normalizing (c k q : PTm n) : PTm n := normalizer c (height k q)

@[simp] theorem subst_start {m : ℕ} (σ : Fin n → PTm m) (c k q : PTm n) :
    Syn.subst σ (start c k q) = start (Syn.subst σ c) (Syn.subst σ k) (Syn.subst σ q) := by simp [start]
@[simp] theorem subst_direction {m : ℕ} (σ : Fin n → PTm m) (c k q : PTm n) :
    Syn.subst σ (direction c k q) = direction (Syn.subst σ c) (Syn.subst σ k) (Syn.subst σ q) := by simp [direction]
@[simp] theorem subst_normalized {m : ℕ} (σ : Fin n → PTm m) (c k q : PTm n) :
    Syn.subst σ (normalized c k q) = normalized (Syn.subst σ c) (Syn.subst σ k) (Syn.subst σ q) := by simp [normalized]
@[simp] theorem subst_normalizing {m : ℕ} (σ : Fin n → PTm m) (c k q : PTm n) :
    Syn.subst σ (normalizing c k q) = normalizing (Syn.subst σ c) (Syn.subst σ k) (Syn.subst σ q) := by simp [normalizing]

theorem initial_distance (c k q : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c))
    (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    distanceBounded (start c k q) (normalized c k q) one (sixteen*q) := by
  have hH := GaussianRationalDirectionClock.height_positive (Γ := Γ) k q
  have hd := GaussianRationalDirectionIteration.denominator_positive q hq
  have actual := GaussianRationalDirectionNormalizer.initial_squared_error c (height k q) hc hH
  have numeric : Γ ⊢[PRAAx] le ((sixteen*q)*(sixteen*q)*GaussianRationalCircleParametrization.four)
      ((one*one)*height k q) :=
    le_congr (by unfold GaussianRationalCircleParametrization.four; ipra_ring) (by ipra_ring)
      (GaussianRationalDirectionClock.initialization_squared_budget k q hk)
  exact RationalArgmin.transitive actual (GaussianEuclideanDistanceName.fraction_order _ _ _ _ hH
    (positive_product _ _ hd hd) numeric)

theorem output_unit (c k q : PTm n) : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit (direction c k q) :=
  GaussianRationalDirectionIteration.direction_unit _ _ _ (GaussianRationalDirectionNormalizer.initial_unit c (height k q))

theorem output_canonical (c k q : PTm n) : Γ ⊢[PRAAx] canonical (direction c k q) :=
  GaussianRationalReciprocal.power_canonical _ _

theorem power_close_start (c k q : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    distanceBounded (power (direction c k q) k) (start c k q) two (sixteen*q) := by
  have actual := GaussianRationalDirectionIteration.direction_close (start c k q) k q hk hq
    (GaussianRationalDirectionNormalizer.initial_canonical c (height k q))
    (GaussianRationalDirectionNormalizer.initial_unit c (height k q))
  have identity : Γ ⊢[PRAAx] one*(sixteen*q) ≐ two*(eight*q) :=
    (congrMul (.eqRefl one) (congrMul GaussianRationalDirectionIteration.sixteen_double_eight (.eqRefl q))).eqTrans (by ipra_ring)
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (GaussianBalancedRadiusSyntax.unit_positive (succ two)) hq)
    (GaussianRationalDirectionIteration.denominator_positive q hq)
    (le_congr (.eqRefl _) identity (le_refl _)) actual

/-- The actual arbitrary-input producer derives its own normalized phase
and every accuracy bound from the original nonzero-input guard. -/
theorem power_close_normalized (c k q : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c))
    (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    distanceBounded (power (direction c k q) k) (normalized c k q) one (four*q) := by
  have actual := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _
    (GaussianRationalDirectionIteration.denominator_positive q hq)
    (power_close_start c k q hk hq) (initial_distance c k q hc hk hq)
  have square : Γ ⊢[PRAAx] pw two two ≐ four :=
    (pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl two))
  have cube : Γ ⊢[PRAAx] pw two (succ two) ≐ four*two :=
    (pw_succ two two).eqTrans (congrMul square (.eqRefl two))
  have sixteenValue : Γ ⊢[PRAAx] sixteen ≐ four*four :=
    (congrAp2 powF (by unfold four; ipra_ring) (.eqRefl two)).eqTrans
      ((pw_succ two (succ two)).eqTrans ((congrMul cube (.eqRefl two)).eqTrans (by unfold four; ipra_ring)))
  have numeric : Γ ⊢[PRAAx] le ((two+one)*(four*q)) (one*(sixteen*q)) :=
    le_of_eq_add (d := four*q) ((congrMul (.eqRefl one) (congrMul sixteenValue (.eqRefl q))).eqTrans
      (by unfold four; ipra_ring))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (GaussianRationalDirectionIteration.denominator_positive q hq)
    (positive_product _ _ (le_of_eq_add (d := one+two) (by unfold four; ipra_ring)) hq) numeric actual

theorem grid_large (k q : PTm n) : Γ ⊢[PRAAx]
    le GaussianRationalDirectionNormalizer.sixtyFour (height k q) := by
  have fixed : Γ ⊢[PRAAx] le (GaussianRationalDirectionNormalizer.sixtyFour : PTm n) (LeanProofs.IPRA.PTm.num 1024) :=
    le_of_eq_add (d := LeanProofs.IPRA.PTm.num 960) (by unfold GaussianRationalDirectionNormalizer.sixtyFour; ipra_ring)
  have squares := positive_product (Γ := Γ) _ _
    (GaussianBalancedRadiusSyntax.unit_positive (GaussianRationalDirectionClock.localIndex k q))
    (GaussianBalancedRadiusSyntax.unit_positive (GaussianRationalDirectionClock.localIndex k q))
  have scaled := mul_le_mul_right (LeanProofs.IPRA.PTm.num 1024) squares
  exact le_trans fixed (le_congr (by ipra_ring)
    ((GaussianRationalDirectionIteration.height_precision k q).eqTrans (GaussianRationalHalfAngle.precision_factor _)).eqSymm scaled)

def certificate (c k q : PTm n) : Fm PTm n := canonical (direction c k q) ⋏
  (GaussianRationalHalfAngle.unit (direction c k q) ⋏
    (distanceBounded (power (direction c k q) k) (normalized c k q) one (four*q) ⋏
      GaussianRationalDirectionNormalizer.certificate c (height k q)))

@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (c k q : PTm n) :
    (certificate c k q).subst σ = certificate (Syn.subst σ c) (Syn.subst σ k) (Syn.subst σ q) := by simp [certificate]

theorem construction_correct (c k q : PTm n) (hc : Γ ⊢[PRAAx] le one (norm c))
    (hk : Γ ⊢[PRAAx] le one k) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx] certificate c k q :=
  .andI (output_canonical c k q) (.andI (output_unit c k q)
    (.andI (power_close_normalized c k q hc hk hq) (GaussianRationalDirectionNormalizer.initialization c (height k q) hc (grid_large k q))))

def output (c k q : PTm n) : PTm n := pairT (direction c k q) (pairT (power (direction c k q) k)
  (pairT (normalizing c k q) (pairT (normalized c k q) (pairT (start c k q) (GaussianRationalDirectionClock.run k q)))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (c k q : PTm n) : PTm n := ap3 outputF c k q

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (c k q : PTm n) :
    Syn.subst σ (output c k q) = output (Syn.subst σ c) (Syn.subst σ k) (Syn.subst σ q) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (c k q : PTm n) :
    Syn.subst σ (run c k q) = run (Syn.subst σ c) (Syn.subst σ k) (Syn.subst σ q) := by simp [run]

theorem program_at (c k q : PTm n) : Γ ⊢[PRAAx] run c k q ≐ output c k q := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![c,k,q]

theorem returned_direction (c k q : PTm n) : Γ ⊢[PRAAx] fstT (run c k q) ≐ direction c k q :=
  (congrFst (program_at c k q)).eqTrans (fst_pair _ _)

theorem returned_power (c k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run c k q)) ≐ power (direction c k q) k :=
  (congrFst ((congrSnd (program_at c k q)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)

theorem returned_normalizer (c k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run c k q))) ≐ normalizing c k q :=
  (congrFst ((congrSnd ((congrSnd (program_at c k q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)

theorem returned_normalized (c k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run c k q)))) ≐ normalized c k q :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at c k q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)

theorem returned_initial (c k q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run c k q))))) ≐ start c k q :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at c k q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)

theorem returned_clock (c k q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run c k q))))) ≐ GaussianRationalDirectionClock.run k q :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at c k q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem nonzero_direction_construction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (norm (var 0)) ⟶ le one (var 1) ⟶ le one (var 2) ⟶ certificate (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (construction_correct _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem direction_construction_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalDirectionConstruction
