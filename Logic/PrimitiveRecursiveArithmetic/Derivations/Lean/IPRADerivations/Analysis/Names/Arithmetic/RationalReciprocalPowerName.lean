import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerBounds.RationalReciprocalPowerTail
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumName
import IPRADerivations.Analysis.RationalArithmetic.RationalClosure

/-!
# Actual cofinal reciprocal-power names

The original rational finite sums are sampled at an explicit cofinal
power-of-two cutoff. The sharp finite tail proves regularity. A shifted
tail name has nonnegative samples bounded by the exact C17 potential;
its true finite-prefix reconstruction agrees with the zeta sampler at
independent precisions. No infinite sum, regularity or reconstruction
law is supplied as a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalReciprocalPowerName

open_ipra
open RationalReciprocalPowerTail (reciprocalPower potential tail tail_zero tail_succ tail_canonical
  add_zero_right finite_conservation sharp_tail tail_nonnegative potential_denominator_positive predecessor_positive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalArgmin (rationalLE)
open RationalArithmetic (add)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper radius upper_mono upper_order_left upper_order_right upper_of_order radius_of_upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem tail_congr {m N r a B s : PTm n} (hm : Γ ⊢[PRAAx] m ≐ a)
    (hN : Γ ⊢[PRAAx] N ≐ B) (hr : Γ ⊢[PRAAx] r ≐ s) : Γ ⊢[PRAAx] tail m N r ≐ tail a B s := by
  ipra_congr (tail (var 0) (var 1) (var 2) : PTm 3) with [hm, hN, hr]

theorem split_zero (m N r : PTm n) : Γ ⊢[PRAAx]
    tail m N (r+zero) ≐ add (tail m N r) (tail m (N+r) zero) :=
  (tail_congr (.eqRefl m) (.eqRefl N) (add_zero r)).eqTrans
    ((add_zero_right _ (tail_canonical m N r)).eqSymm.eqTrans
      (RationalAlgebra.add_congr (.eqRefl _) (tail_zero m (N+r)).eqSymm))

theorem split_succ (m N r s : PTm n) (ih : Γ ⊢[PRAAx]
    tail m N (r+s) ≐ add (tail m N r) (tail m (N+r) s)) : Γ ⊢[PRAAx]
    tail m N (r+succ s) ≐ add (tail m N r) (tail m (N+r) (succ s)) := by
  have left := (tail_congr (.eqRefl m) (.eqRefl N) (by ipra_ring : Γ ⊢[PRAAx] r+succ s ≐ succ (r+s))).eqTrans
    ((tail_succ m N (r+s)).eqTrans
      (RationalAlgebra.add_congr ih (RationalReciprocalPowerTail.reciprocal_congr (.eqRefl m)
        (by ipra_ring : Γ ⊢[PRAAx] succ (N+(r+s)) ≐ succ ((N+r)+s)))))
  exact left.eqTrans ((RationalAlgebra.add_associative _ _ _).eqTrans
    (RationalAlgebra.add_congr (.eqRefl _) (tail_succ m (N+r) s).eqSymm))

/-- Literal code equality for the actual finite sum, with arbitrary raw
numerical parameters and independently normalized rational additions. -/
theorem tail_split (m N r s : PTm n) : Γ ⊢[PRAAx]
    tail m N (r+s) ≐ add (tail m N r) (tail m (N+r) s) := by
  have hall : Γ ⊢[PRAAx] .all (tail (Syn.shift m) (Syn.shift N) (Syn.shift r+var 0) ≐
      add (tail (Syn.shift m) (Syn.shift N) (Syn.shift r)) (tail (Syn.shift m) (Syn.shift N+Syn.shift r) (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq,RationalReciprocalPowerTail.subst_tail,RationalArithmetic.subst_add,PTm.subst_add,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using split_zero (Γ := Γ) m N r
    · simp only [Fm.subst_eq,RationalReciprocalPowerTail.subst_tail,RationalArithmetic.subst_add,PTm.subst_add,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact split_succ (Syn.shift m) (Syn.shift N) (Syn.shift r) (var 0) Prf.hyp0
  simpa only [Fm.subst_eq,RationalReciprocalPowerTail.subst_tail,RationalArithmetic.subst_add,PTm.subst_add,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE s

theorem fraction_add_upper (c A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    upper (add c (fraction A B)) c A B := by
  have dc := RationalArgmin.denominator_positive (Γ := Γ) c
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _
    (RationalAlgebra.positive_product dc hB) dc
    (RationalRepresentations.represents_add _ _ _ _ _ _ (RationalRepresentations.represents_self c)
      (fraction_represents _ _ hB)) (RationalRepresentations.represents_self c)
  apply zle_of_toZ zero
  simp only [ZT.toZ_sub,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem potential_denominator_dominates (m k : PTm n) (hm : Γ ⊢[PRAAx] le two m)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] le k (pred m*pw k (pred m)) := by
  have hp := predecessor_positive m hm
  have p := le_congr (pw_one k) (.eqRefl _) (GaussianFactorBudget.power_monotone_length k one (pred m) hk hp)
  have mult := AnalyticNumberTheory.PhiLower.le_mul_mono hp (le_refl (pw k (pred m)))
  exact le_trans p (le_congr (one_mul _) (.eqRefl _) mult)

theorem later_order (m N r s : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hr : Γ ⊢[PRAAx] le one r)
    (hrs : Γ ⊢[PRAAx] le r s) : Γ ⊢[PRAAx] rationalLE (tail m N r) (tail m N s) := by
  have start : Γ ⊢[PRAAx] le one (N+r) := le_trans hr (le_add_left r N)
  have positive := tail_nonnegative m (N+r) (monus s r) hm start
  have added := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ (RationalArgmin.reflexive (tail m N r)) positive
  have split := (tail_congr (.eqRefl m) (.eqRefl N) (eq_add_of_le hrs)).eqTrans (tail_split m N r (monus s r))
  exact RationalArgmin.rationalLE_congr (add_zero_right _ (tail_canonical m N r)) split.eqSymm added

theorem later_sharp_upper (m N r s : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hr : Γ ⊢[PRAAx] le one r)
    (hrs : Γ ⊢[PRAAx] le r s) : Γ ⊢[PRAAx]
    upper (tail m N s) (tail m N r) one (pred m*pw (N+r) (pred m)) := by
  have start : Γ ⊢[PRAAx] le one (N+r) := le_trans hr (le_add_left r N)
  have added := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ (RationalArgmin.reflexive (tail m N r))
    (sharp_tail m (N+r) (monus s r) hm start)
  have split := (tail_congr (.eqRefl m) (.eqRefl N) (eq_add_of_le hrs)).eqTrans (tail_split m N r (monus s r))
  exact upper_order_left _ _ _ _ _
    (RationalArgmin.rationalLE_congr split.eqSymm (.eqRefl _) added)
    (fraction_add_upper _ _ _ (potential_denominator_positive m (N+r) hm start))

theorem later_upper (m N r s : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hr : Γ ⊢[PRAAx] le one r)
    (hrs : Γ ⊢[PRAAx] le r s) : Γ ⊢[PRAAx] upper (tail m N s) (tail m N r) one r := by
  have start : Γ ⊢[PRAAx] le one (N+r) := le_trans hr (le_add_left r N)
  exact upper_mono _ _ _ _ _ _ (potential_denominator_positive m (N+r) hm start)
    (later_sharp_upper m N r s hm hr hrs)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm
      (le_trans (le_add_left r N) (potential_denominator_dominates m (N+r) hm start)))

/-- One-sided comparison is valid without ordering the two cutoffs: if
the first is earlier, positivity supplies the stronger exact order. -/
theorem any_upper (m N r s : PTm n) (hm : Γ ⊢[PRAAx] le two m)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] upper (tail m N r) (tail m N s) one s := by
  refine .orE (le_total r s) ?_ ?_
  · exact upper_of_order _ _ _ _ (later_order m N r s hm.wk hr.wk Prf.hyp0)
  · exact later_upper m N s r hm.wk hs.wk Prf.hyp0

def unit (p : PTm n) : PTm n := pw two p
def cutoff (p : PTm n) : PTm n := num 4*unit p
def observation (p m N : PTm n) : PTm n := tail m N (cutoff p)
ipra_subst unit
ipra_subst cutoff
ipra_subst observation
theorem unit_positive (p : PTm n) : Γ ⊢[PRAAx] le one (unit p) :=
  GaussianFactorBudget.power_positive two p (le_succ_self one)
theorem cutoff_positive (p : PTm n) : Γ ⊢[PRAAx] le one (cutoff p) := by
  have h := unit_positive (Γ := Γ) p
  ipra_le 4*sl h+3 using unfold cutoff; ipra_simps; ring

theorem observation_regularity (p q m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    radius (observation p m N) (observation q m N) (unit p+unit q) (unit p*unit q) := by
  apply radius_of_upper _ _ _ _
  · exact upper_mono _ _ _ _ _ _ (cutoff_positive q)
      (any_upper m N (cutoff p) (cutoff q) hm (cutoff_positive p) (cutoff_positive q))
      (le_of_eq_add (d := num 3*unit p*unit q+num 4*unit q*unit q) (by unfold cutoff; ipra_ring))
  · exact upper_mono _ _ _ _ _ _ (cutoff_positive p)
      (any_upper m N (cutoff q) (cutoff p) hm (cutoff_positive q) (cutoff_positive p))
      (le_of_eq_add (d := num 3*unit p*unit q+num 4*unit p*unit p) (by unfold cutoff; ipra_ring))


def harmonicPrefix (m N : PTm n) : PTm n := tail m zero N
def zetaF : PR 2 := PTm.toPR (observation (var 0) (var 1) zero)
def zetaSample (p m : PTm n) : PTm n := ap2 zetaF p m
def tailData (m N : PTm n) : PTm n := pairT m N
def tailNameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (sndT (var 1)))
def tailSample (p m N : PTm n) : PTm n := ap2 tailNameF p (tailData m N)
def reconstruction (p m N : PTm n) : PTm n := add (harmonicPrefix m N) (observation p m N)
def reconstructionF : PR 2 := PTm.toPR (reconstruction (var 0) (fstT (var 1)) (sndT (var 1)))
def reconstructedSample (p m N : PTm n) : PTm n := ap2 reconstructionF p (tailData m N)

@[simp] theorem subst_prefix {l : ℕ} (σ : Fin n → PTm l) (m N : PTm n) :
    Syn.subst σ (harmonicPrefix m N) = harmonicPrefix (Syn.subst σ m) (Syn.subst σ N) := by simp [harmonicPrefix]
ipra_subst zetaSample
ipra_subst tailData
ipra_subst tailSample
ipra_subst reconstruction
ipra_subst reconstructedSample

theorem observation_congr {p m N q a B : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q)
    (hm : Γ ⊢[PRAAx] m ≐ a) (hN : Γ ⊢[PRAAx] N ≐ B) :
    Γ ⊢[PRAAx] observation p m N ≐ observation q a B := by
  ipra_congr (observation (var 0) (var 1) (var 2) : PTm 3) with [hp, hm, hN]

theorem zeta_sample_at (p m : PTm n) : Γ ⊢[PRAAx] zetaSample p m ≐ observation p m zero := by
  simpa only [zetaSample,zetaF,ap2,subst_observation,Syn.subst_var,ConciseIPRA.PTm.subst_zero,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
    toPR_eq (Γ := Γ) (observation (var 0) (var 1) zero : PTm 2) ![p,m]
theorem tail_sample_at (p m N : PTm n) : Γ ⊢[PRAAx] tailSample p m N ≐ observation p m N := by
  have e : Γ ⊢[PRAAx] tailSample p m N ≐ observation p (fstT (tailData m N)) (sndT (tailData m N)) := by
    simpa only [tailSample,tailNameF,ap2,subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
      toPR_eq (Γ := Γ) (observation (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,tailData m N]
  exact e.eqTrans (observation_congr (.eqRefl _) (fst_pair _ _) (snd_pair _ _))
theorem reconstruction_sample_at (p m N : PTm n) : Γ ⊢[PRAAx] reconstructedSample p m N ≐ reconstruction p m N := by
  have e : Γ ⊢[PRAAx] reconstructedSample p m N ≐ reconstruction p (fstT (tailData m N)) (sndT (tailData m N)) := by
    simpa only [reconstructedSample,reconstructionF,ap2,subst_reconstruction,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
      toPR_eq (Γ := Γ) (reconstruction (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,tailData m N]
  exact e.eqTrans (RationalAlgebra.add_congr
    (tail_congr (fst_pair _ _) (.eqRefl _) (snd_pair _ _))
    (observation_congr (.eqRefl _) (fst_pair _ _) (snd_pair _ _)))

theorem zeta_sample_canonical (p m : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (zetaSample p m) :=
  RationalCubeMinimum.well_formed_congr (zeta_sample_at p m).eqSymm (tail_canonical m zero (cutoff p))
theorem tail_sample_canonical (p m N : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (tailSample p m N) :=
  RationalCubeMinimum.well_formed_congr (tail_sample_at p m N).eqSymm (tail_canonical m N (cutoff p))

theorem zeta_samples_regularity (p q m : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    radius (zetaSample p m) (zetaSample q m) (unit p+unit q) (unit p*unit q) :=
  RationalValueBounds.radius_congr (zeta_sample_at p m).eqSymm (zeta_sample_at q m).eqSymm (.eqRefl _) (.eqRefl _)
    (observation_regularity p q m zero hm)
theorem tail_samples_regularity (p q m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    radius (tailSample p m N) (tailSample q m N) (unit p+unit q) (unit p*unit q) :=
  RationalValueBounds.radius_congr (tail_sample_at p m N).eqSymm (tail_sample_at q m N).eqSymm (.eqRefl _) (.eqRefl _)
    (observation_regularity p q m N hm)

theorem zeta_name_regular (m : PTm n) (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] RationalCubeInfimumName.regular zetaF m := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le two (Syn.shift (Syn.shift m)) := by
    simpa [Fm.shift,Syn.shift] using hm.shift.shift
  simpa only [RationalCubeInfimumName.regular,RationalCubeGrid.scale,unit,zetaSample,Syn.shift] using
    zeta_samples_regularity (var 1) (var 0) (Syn.shift (Syn.shift m)) hs

theorem tail_name_regular (m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] RationalCubeInfimumName.regular tailNameF (tailData m N) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le two (Syn.shift (Syn.shift m)) := by
    simpa [Fm.shift,Syn.shift] using hm.shift.shift
  simpa only [RationalCubeInfimumName.regular,RationalCubeGrid.scale,unit,tailSample,subst_tailData,Syn.shift] using
    tail_samples_regularity (var 1) (var 0) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift N)) hs

/-- Every actual shifted-tail sample lies in the exact positive C17
interval. No dyadic error is needed for this samplewise bound. -/
theorem tail_sample_bounds (p m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (fraction zero one) (tailSample p m N) ⋏ rationalLE (tailSample p m N) (potential m N) :=
  .andI (RationalArgmin.rationalLE_congr (.eqRefl _) (tail_sample_at p m N).eqSymm (tail_nonnegative m N (cutoff p) hm hN))
    (RationalArgmin.rationalLE_congr (tail_sample_at p m N).eqSymm (.eqRefl _) (sharp_tail m N (cutoff p) hm hN))

/-- The actual zeta observation is never above this sharp finite-prefix
upper bound, even if its sampled prefix is shorter than N. -/
theorem zeta_upper (p m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    upper (zetaSample p m) (harmonicPrefix m N) one (pred m*pw N (pred m)) := by
  have actual : Γ ⊢[PRAAx] upper (observation p m zero) (harmonicPrefix m N) one (pred m*pw N (pred m)) := by
    refine .orE (le_total (cutoff p) N) ?_ ?_
    · exact upper_of_order _ _ _ _ (later_order m zero (cutoff p) N hm.wk (cutoff_positive p) Prf.hyp0)
    · exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) (zero_add N)))
        (later_sharp_upper m zero N (cutoff p) hm.wk hN.wk Prf.hyp0)
  exact RationalValueBounds.upper_congr (zeta_sample_at p m).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) actual

/-- The lower comparison keeps the ordinary observation error: an early
finite zeta sample need not already exceed every original finite prefix. -/
theorem zeta_lower (p m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    upper (harmonicPrefix m N) (zetaSample p m) one (unit p) := by
  have actual : Γ ⊢[PRAAx] upper (harmonicPrefix m N) (observation p m zero) one (unit p) :=
    upper_mono _ _ _ _ _ _ (cutoff_positive p)
    (any_upper m zero N (cutoff p) hm hN (cutoff_positive p))
    (le_of_eq_add (d := num 3*unit p) (by unfold cutoff; ipra_ring))
  exact RationalValueBounds.upper_congr (.eqRefl _) (zeta_sample_at p m).eqSymm (.eqRefl _) (.eqRefl _) actual

theorem reconstruction_prefix (p m N : PTm n) : Γ ⊢[PRAAx]
    harmonicPrefix m (N+cutoff p) ≐ reconstruction p m N :=
  (tail_split m zero N (cutoff p)).eqTrans
    (RationalAlgebra.add_congr (.eqRefl _) (tail_congr (.eqRefl m) (zero_add N) (.eqRefl _)))

/-- Literal H_N plus the genuine positive tail name represents the SAME
cofinal reciprocal-power sum at independent observations. -/
theorem reconstruction_error (p q m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    radius (zetaSample p m) (reconstructedSample q m N) (unit p+unit q) (unit p*unit q) := by
  have hL : Γ ⊢[PRAAx] le one (N+cutoff q) := le_trans (cutoff_positive q) (le_add_left _ _)
  have bound : Γ ⊢[PRAAx] radius (harmonicPrefix m (cutoff p)) (harmonicPrefix m (N+cutoff q))
      (unit p+unit q) (unit p*unit q) := by
    apply radius_of_upper _ _ _ _
    · exact upper_mono _ _ _ _ _ _ hL
        (any_upper m zero (cutoff p) (N+cutoff q) hm (cutoff_positive p) hL)
        (le_of_eq_add (d := (unit p+unit q)*N+num 3*unit p*unit q+num 4*unit q*unit q) (by unfold cutoff; ipra_ring))
    · exact upper_mono _ _ _ _ _ _ (cutoff_positive p)
        (any_upper m zero (N+cutoff q) (cutoff p) hm hL (cutoff_positive p))
        (le_of_eq_add (d := num 3*unit p*unit q+num 4*unit p*unit p) (by unfold cutoff; ipra_ring))
  exact RationalValueBounds.radius_congr (zeta_sample_at p m).eqSymm
    ((reconstruction_prefix q m N).eqTrans (reconstruction_sample_at q m N).eqSymm) (.eqRefl _) (.eqRefl _) bound


theorem cutoff_cofinal (p : PTm n) : Γ ⊢[PRAAx] le p (cutoff p) := by
  have small : Γ ⊢[PRAAx] le p (unit p) := le_trans (le_succ_self p) (RationalClosure.succ_le_two_pow p)
  have large : Γ ⊢[PRAAx] le (unit p) (cutoff p) := by
    unfold cutoff
    ipra_le 3*𝔞 (unit p)
  exact le_trans small large

theorem reconstructed_samples_regularity (p q m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    radius (reconstructedSample p m N) (reconstructedSample q m N) (unit p+unit q) (unit p*unit q) := by
  have hp : Γ ⊢[PRAAx] le one (N+cutoff p) := le_trans (cutoff_positive p) (le_add_left _ _)
  have hq : Γ ⊢[PRAAx] le one (N+cutoff q) := le_trans (cutoff_positive q) (le_add_left _ _)
  have bound : Γ ⊢[PRAAx] radius (harmonicPrefix m (N+cutoff p)) (harmonicPrefix m (N+cutoff q))
      (unit p+unit q) (unit p*unit q) := by
    apply radius_of_upper _ _ _ _
    · exact upper_mono _ _ _ _ _ _ hq (any_upper m zero (N+cutoff p) (N+cutoff q) hm hp hq)
        (le_of_eq_add (d := (unit p+unit q)*N+num 3*unit p*unit q+num 4*unit q*unit q) (by unfold cutoff; ipra_ring))
    · exact upper_mono _ _ _ _ _ _ hp (any_upper m zero (N+cutoff q) (N+cutoff p) hm hq hp)
        (le_of_eq_add (d := (unit p+unit q)*N+num 3*unit p*unit q+num 4*unit p*unit p) (by unfold cutoff; ipra_ring))
  exact RationalValueBounds.radius_congr
    ((reconstruction_prefix p m N).eqTrans (reconstruction_sample_at p m N).eqSymm)
    ((reconstruction_prefix q m N).eqTrans (reconstruction_sample_at q m N).eqSymm) (.eqRefl _) (.eqRefl _) bound

theorem reconstructed_name_regular (m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] RationalCubeInfimumName.regular reconstructionF (tailData m N) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le two (Syn.shift (Syn.shift m)) := by
    simpa [Fm.shift,Syn.shift] using hm.shift.shift
  simpa only [RationalCubeInfimumName.regular,RationalCubeGrid.scale,unit,reconstructedSample,subst_tailData,Syn.shift] using
    reconstructed_samples_regularity (var 1) (var 0) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift N)) hs

theorem reconstruction_actual_sum (p m N : PTm n) : Γ ⊢[PRAAx]
    reconstructedSample p m N ≐ add (harmonicPrefix m N) (tailSample p m N) :=
  (reconstruction_sample_at p m N).eqTrans (RationalAlgebra.add_congr (.eqRefl _) (tail_sample_at p m N).eqSymm)

theorem actual_reciprocal_power_finite_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tail (var 0) (var 1) (var 2+var 3) ≐
      add (tail (var 0) (var 1) (var 2)) (tail (var 0) (var 1+var 2) (var 3))) :=
  closeUniv 4 (tail_split _ _ _ _)

theorem actual_zeta_cutoff_cofinal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (var 0) (cutoff (var 0))) := closeUniv 1 (cutoff_cofinal _)

theorem actual_zeta_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (zetaSample (var 0) (var 1) ≐ harmonicPrefix (var 1) (cutoff (var 0)) ⋏
      RationalNormalForm.wellFormed (zetaSample (var 0) (var 1))) :=
  closeUniv 2 (.andI (zeta_sample_at _ _) (zeta_sample_canonical _ _))

theorem actual_zeta_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le two (var 0) ⟶ RationalCubeInfimumName.regular zetaF (var 0)) :=
  closeUniv 1 (.impI (zeta_name_regular _ Prf.hyp0))

theorem source_C17_positive_tail_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le two (var 1) ⟶ le one (var 2) ⟶
      (RationalCubeInfimumName.regular tailNameF (tailData (var 1) (var 2)) ⋏
        (rationalLE (fraction zero one) (tailSample (var 0) (var 1) (var 2)) ⋏
          rationalLE (tailSample (var 0) (var 1) (var 2)) (potential (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.impI (.andI (tail_name_regular _ _ Prf.hyp1) (tail_sample_bounds _ _ _ Prf.hyp1 Prf.hyp0))))

theorem source_C17_original_zeta_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le two (var 1) ⟶ le one (var 2) ⟶
      (upper (harmonicPrefix (var 1) (var 2)) (zetaSample (var 0) (var 1)) one (unit (var 0)) ⋏
        upper (zetaSample (var 0) (var 1)) (harmonicPrefix (var 1) (var 2)) one
          (pred (var 1)*pw (var 2) (pred (var 1))))) :=
  closeUniv 3 (.impI (.impI (.andI (zeta_lower _ _ _ Prf.hyp1 Prf.hyp0) (zeta_upper _ _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_positive_tail_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (reconstructedSample (var 0) (var 1) (var 2) ≐
      add (harmonicPrefix (var 1) (var 2)) (tailSample (var 0) (var 1) (var 2))) :=
  closeUniv 3 (reconstruction_actual_sum _ _ _)

theorem actual_positive_tail_reconstruction_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le two (var 0) ⟶ RationalCubeInfimumName.regular reconstructionF (tailData (var 0) (var 1))) :=
  closeUniv 2 (.impI (reconstructed_name_regular _ _ Prf.hyp0))

theorem source_C17_zeta_equals_prefix_plus_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le two (var 2) ⟶
      radius (zetaSample (var 0) (var 2)) (reconstructedSample (var 1) (var 2) (var 3))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 4 (.impI (reconstruction_error _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalReciprocalPowerName
