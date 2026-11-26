import IPRADerivations.Analysis.Integration.GaussianPartitionedFiniteSum
import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement

/-!
# Actual finite Gaussian sum comparison along numerical blocks

Each original fine block is compared with repetitions of its actual
coarse observation. The original grouping theorem and the existing
inner and outer finite sum metrics supply the complete comparison.
All block counts and indices are numerical, including repeated cuts.
The local premise is a finite row-distance contract, not a sum identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPartitionedFiniteSumDistance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPartitionedFiniteSum (increasing block blockBody grouped_from_zero)
open GaussianRationalFiniteSum (sum)
open GaussianRationalRiemannRefinement (termsDistance constantBody sum_distance constant_sum)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def blockLength (cut : PR 2) (i d : PTm n) : PTm n := monus (ap2 cut (succ i) d) (ap2 cut i d)
def coarseRow (cut : PR 2) (g : PTm 2) (i d y : PTm n) : PTm n :=
  natScale (blockLength cut i d) (inst2 g i y)
def coarseBody (cut : PR 2) (g : PTm 2) : PTm 2 :=
  coarseRow cut g (var 0) (fstT (var 1)) (sndT (var 1))
def blockAgreement (cut : PR 2) (f g : PTm 2) (K d x y A B : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift K) ⟶ termsDistance (offB f) constantBody
    (blockLength cut (var 0) (Syn.shift d)) (pairT (ap2 cut (var 0) (Syn.shift d)) (Syn.shift x))
    (inst2 g (var 0) (Syn.shift y)) (Syn.shift A) (Syn.shift B))
def blockBound (cut : PR 2) (K d H : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift K) ⟶ le (blockLength cut (var 0) (Syn.shift d)) (Syn.shift H))

@[simp] theorem subst_blockLength {m : ℕ} (σ : Fin n → PTm m) (cut : PR 2) (i d : PTm n) :
    Syn.subst σ (blockLength cut i d) = blockLength cut (Syn.subst σ i) (Syn.subst σ d) := by simp [blockLength]
@[simp] theorem subst_coarseRow {m : ℕ} (σ : Fin n → PTm m) (cut : PR 2) (g : PTm 2) (i d y : PTm n) :
    Syn.subst σ (coarseRow cut g i d y) = coarseRow cut g (Syn.subst σ i) (Syn.subst σ d) (Syn.subst σ y) := by simp [coarseRow]
@[simp] theorem subst_blockAgreement {m : ℕ} (σ : Fin n → PTm m) (cut : PR 2) (f g : PTm 2) (K d x y A B : PTm n) :
    (blockAgreement cut f g K d x y A B).subst σ = blockAgreement cut f g (Syn.subst σ K) (Syn.subst σ d)
      (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [blockAgreement,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_blockBound {m : ℕ} (σ : Fin n → PTm m) (cut : PR 2) (K d H : PTm n) :
    (blockBound cut K d H).subst σ = blockBound cut (Syn.subst σ K) (Syn.subst σ d) (Syn.subst σ H) := by
  simp [blockBound,Syn.subst_shift,Syn.shift_subst]

theorem coarse_at (cut : PR 2) (g : PTm 2) (i d y : PTm n) : Γ ⊢[PRAAx]
    inst2 (coarseBody cut g) i (pairT d y) ≐ coarseRow cut g i d y := by
  simp only [coarseBody,inst2,subst_coarseRow,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have left := congrAp2 (Γ := Γ) cut (.eqRefl i) (fst_pair d y)
  have right := congrAp2 (Γ := Γ) cut (.eqRefl (succ i)) (fst_pair d y)
  exact GaussianRationalNaturalScale.natScale_congr (congrMonus right left)
    (congrInst2 g (.eqRefl i) (snd_pair d y))

theorem agreement_at (cut : PR 2) (f g : PTm 2) (K d x y A B i : PTm n)
    (h : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B) (hi : Γ ⊢[PRAAx] lt i K) : Γ ⊢[PRAAx]
    termsDistance (offB f) constantBody (blockLength cut i d) (pairT (ap2 cut i d) x) (inst2 g i y) A B := by
  have rule := h.allE i
  simp only [Fm.subst_imp,subst_lt,GaussianRationalRiemannRefinement.subst_termsDistance,
    subst_blockLength,subst_pairT,subst_ap2,subst_inst2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at rule
  exact .impE rule hi

theorem bound_at (cut : PR 2) (K d H i : PTm n) (h : Γ ⊢[PRAAx] blockBound cut K d H)
    (hi : Γ ⊢[PRAAx] lt i K) : Γ ⊢[PRAAx] le (blockLength cut i d) H := by
  have rule := h.allE i
  simp only [Fm.subst_imp,subst_lt,subst_le,subst_blockLength,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at rule
  exact .impE rule hi

theorem block_error (cut : PR 2) (f g : PTm 2) (K d x y A B i : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B) (hi : Γ ⊢[PRAAx] lt i K) : Γ ⊢[PRAAx]
    distanceBounded (block cut f i d x) (coarseRow cut g i d y) (blockLength cut i d*A) B :=
  distance_congr (.eqRefl _) (constant_sum (inst2 g i y) (blockLength cut i d)) (.eqRefl _) (.eqRefl _)
    (sum_distance (offB f) constantBody _ _ _ A B hB (agreement_at cut f g K d x y A B i h hi))

theorem bounded_block_error (cut : PR 2) (f g : PTm 2) (K d x y A B H i : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B)
    (hb : Γ ⊢[PRAAx] blockBound cut K d H) (hi : Γ ⊢[PRAAx] lt i K) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (blockBody cut f) i (pairT d x)) (inst2 (coarseBody cut g) i (pairT d y)) (H*A) B :=
  distance_congr (GaussianPartitionedFiniteSum.block_at cut f i d x).eqSymm (coarse_at cut g i d y).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ (H*A) B hB hB
      (mul_le_mul_right B (mul_le_mul_right A (bound_at cut K d H i hb hi))) (block_error cut f g K d x y A B i hB h hi))

theorem outer_agreement (cut : PR 2) (f g : PTm 2) (K d x y A B H : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B)
    (hb : Γ ⊢[PRAAx] blockBound cut K d H) : Γ ⊢[PRAAx]
    termsDistance (blockBody cut f) (coarseBody cut g) K (pairT d x) (pairT d y) (H*A) B := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] blockAgreement cut f g (Syn.shift K) (Syn.shift d) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] blockBound cut (Syn.shift K) (Syn.shift d) (Syn.shift H) := by simpa [Fm.shift,Syn.shift] using hb.shift
  refine .allI (.impI ?_)
  simpa only [termsDistance,subst_pairT,PTm.subst_mul,Syn.shift] using
    bounded_block_error cut f g (Syn.shift K) (Syn.shift d) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift B) (Syn.shift H) (var 0)
      bs.wk hs.wk ns.wk Prf.hyp0

/-- The original fine prefix is compared with actual weighted coarse
rows. All indices and block counts are internal numerical terms. -/
theorem original_comparison (cut : PR 2) (f g : PTm 2) (K d x y A B H : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] increasing cut d) (h0 : Γ ⊢[PRAAx] ap2 cut zero d ≐ zero)
    (hr : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B) (hb : Γ ⊢[PRAAx] blockBound cut K d H) : Γ ⊢[PRAAx]
    distanceBounded (sum f (ap2 cut K d) x) (sum (coarseBody cut g) K (pairT d y)) (K*(H*A)) B :=
  distance_congr (grouped_from_zero cut f K d x hm h0) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sum_distance _ _ K _ _ (H*A) B hB (outer_agreement cut f g K d x y A B H hB hr hb))

theorem weighted_comparison (cut : PR 2) (f g : PTm 2) (K d x y A B H w M D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hm : Γ ⊢[PRAAx] increasing cut d)
    (h0 : Γ ⊢[PRAAx] ap2 cut zero d ≐ zero) (hr : Γ ⊢[PRAAx] blockAgreement cut f g K d x y A B)
    (hb : Γ ⊢[PRAAx] blockBound cut K d H) (hw : Γ ⊢[PRAAx] bounded w M D) : Γ ⊢[PRAAx]
    distanceBounded (qmul w (sum f (ap2 cut K d) x)) (qmul w (sum (coarseBody cut g) K (pairT d y))) (M*(K*(H*A))) (D*B) :=
  GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference w _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_product _ _ M D _ B hD hB hw (original_comparison cut f g K d x y A B H hB hm h0 hr hb))

theorem actual_original_partitioned_finite_distance_closed (cut : PR 2) (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 5) ⋏ (increasing cut (var 1) ⋏ (ap2 cut zero (var 1) ≐ zero ⋏
      (blockAgreement cut f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏ blockBound cut (var 0) (var 1) (var 6))))) ⟶
      distanceBounded (sum f (ap2 cut (var 0) (var 1)) (var 2)) (sum (coarseBody cut g) (var 0) (pairT (var 1) (var 3)))
        (var 0*(var 6*var 4)) (var 5)) :=
  closeUniv 7 (.impI (original_comparison cut f g _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPartitionedFiniteSumDistance
