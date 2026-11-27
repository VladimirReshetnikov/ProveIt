import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteEqualityChain

/-!
# A constant sequence of Gaussian names with a vanishing envelope

The finite equality-chain proof propagates adjacent equivalences
at every internal index by quantifier-free induction. A computed
index then reduces a reciprocal decay envelope to a dyadic error,
which identifies the initial name with the original zero name.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianNamedRecurrencePinning

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianNamedFiniteEqualityChain (allSteps sample finite_cross)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianNameRingLaws (equivalent_of_envelope zeroF zero_fast zero_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianReconstructionRoots (distance_zero_iff)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def regularFamily (f : PR 2) (b : PTm 2) (x : PTm n) : Fm PTm n :=
  .all (pointCN f (inst2 b (var 0) (Syn.shift x)))

ipra_subst regularFamily [Syn.subst_shift, Syn.shift_subst]

theorem regular_at (f : PR 2) (b : PTm 2) (x j : PTm n) (h : Γ ⊢[PRAAx] regularFamily f b x) :
    Γ ⊢[PRAAx] pointCN f (inst2 b j x) := by
  ipra_simpa_inst [regularFamily,subst_pointCN,subst_inst2] using h.allE j

def decayAt (f : PR 2) (b : PTm 2) (x B C j : PTm n) : Fm PTm n :=
  le one j ⟶ .all
    (bounded (sample f b (var 0) (Syn.shift j) (Syn.shift x))
      (Syn.shift B*unit (var 0)+Syn.shift C*Syn.shift j) (Syn.shift j*unit (var 0)))

/-- At each positive internal index (j) the named observations obey
(B/j+C/2^p), with the same (B,C) for the whole sequence. -/
def decayEnvelope (f : PR 2) (b : PTm 2) (x B C : PTm n) : Fm PTm n :=
  .all (decayAt f b (Syn.shift x) (Syn.shift B) (Syn.shift C) (var 0))

ipra_subst decayAt [one, Syn.subst_shift, Syn.shift_subst]

ipra_subst decayEnvelope [Syn.subst_shift, Syn.shift_subst]

theorem decay_at (f : PR 2) (b : PTm 2) (x B C j p : PTm n) (hj : Γ ⊢[PRAAx] le one j)
    (h : Γ ⊢[PRAAx] decayEnvelope f b x B C) :
    Γ ⊢[PRAAx] bounded (sample f b p j x) (B*unit p+C*j) (j*unit p) := by
  have atIndex : Γ ⊢[PRAAx] decayAt f b x B C j := by
    ipra_simpa_inst [decayEnvelope,subst_decayAt] using h.allE j
  have all := Prf.impE atIndex hj
  ipra_simpa_inst [GaussianRationalMetric.subst_bounded,GaussianNamedFiniteEqualityChain.subst_sample,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_add] using all.allE p

theorem index_cross (f : PR 2) (b : PTm 2) (x j : PTm n)
    (hr : Γ ⊢[PRAAx] regularFamily f b x) (hs : Γ ⊢[PRAAx] allSteps f b x) :
    Γ ⊢[PRAAx] crossEquivalent f f (inst2 b j x) (inst2 b zero x) :=
  finite_cross f b j x hs (regular_at f b x j hr) (regular_at f b x zero hr)

def witnessIndex (B p : PTm n) : PTm n := B*unit p+one

theorem initial_observation_bound (f : PR 2) (b : PTm 2) (x B C p : PTm n)
    (hr : Γ ⊢[PRAAx] regularFamily f b x) (hs : Γ ⊢[PRAAx] allSteps f b x)
    (hd : Γ ⊢[PRAAx] decayEnvelope f b x B C) :
    Γ ⊢[PRAAx] bounded (sample f b p zero x) (C+num 3) (unit p) := by
  let U := unit p
  let j := witnessIndex B p
  let a := inst2 b zero x
  let z := inst2 b j x
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hj : Γ ⊢[PRAAx] le one j :=
    le_congr (.eqRefl _) (by dsimp only [j,witnessIndex,U]; ipra_ring) (le_add_right one (B*U))
  have estimate := decay_at f b x B C j p hj hd
  have small : Γ ⊢[PRAAx] bounded (ap2 f p z) (C+one) U :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hj hu) hu
      (le_of_eq_add (d := U) (by dsimp only [j,witnessIndex,U]; ipra_ring)) estimate
  have link := cross_symm f f z a (index_cross f b x j hr hs)
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 f p a) (ap2 f p z) two U :=
    GaussianNameEquivalence.cross_diagonal_at p link
  have both := distance_triangle_same _ _ qzero _ _ U hu near ((distance_zero_iff _ _ _ hu).iffMpr small)
  exact (distance_zero_iff _ _ _ hu).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) both)

theorem zero_cross (f : PR 2) (b : PTm 2) (x y B C : PTm n)
    (hr : Γ ⊢[PRAAx] regularFamily f b x) (hs : Γ ⊢[PRAAx] allSteps f b x)
    (hd : Γ ⊢[PRAAx] decayEnvelope f b x B C) :
    Γ ⊢[PRAAx] crossEquivalent f zeroF (inst2 b zero x) y := by
  apply equivalent_of_envelope _ _ _ _ (C+num 3) (regular_at f b x zero hr) (zero_fast y)
  refine .allI ?_
  let s (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have rs : Δ ⊢[PRAAx] regularFamily f b (s x) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_regularFamily] using hr.shift
  have ss : Δ ⊢[PRAAx] allSteps f b (s x) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,GaussianNamedFiniteEqualityChain.subst_allSteps] using hs.shift
  have ds : Δ ⊢[PRAAx] decayEnvelope f b (s x) (s B) (s C) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_decayEnvelope] using hd.shift
  have bound := initial_observation_bound f b (s x) (s B) (s C) p rs ss ds
  have read := distance_congr (.eqRefl _) (zero_at (Γ := Δ) p (s y)).eqSymm (.eqRefl _) (.eqRefl _)
    ((distance_zero_iff _ _ _ (unit_positive (Γ := Δ) p)).iffMpr bound)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,s,Δ,p,Syn.shift,subst_inst2,
    GaussianNamedFiniteEqualityChain.sample,PTm.subst_add,PTm.subst_num,ConciseIPRA.PTm.subst_zero] using read

theorem actual_named_regular_recurrence_index_closed (f : PR 2) (b : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (regularFamily f b (var 0) ⟶ allSteps f b (var 0) ⟶
        crossEquivalent f f (inst2 b (var 1) (var 0)) (inst2 b zero (var 0))) :=
  closeUniv 2 (.impI (.impI (index_cross f b _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_named_vanishing_recurrence_closed (f : PR 2) (b : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (regularFamily f b (var 0) ⟶ allSteps f b (var 0) ⟶ decayEnvelope f b (var 0) (var 2) (var 3) ⟶
        crossEquivalent f zeroF (inst2 b zero (var 0)) (var 1)) :=
  closeUniv 4 (.impI (.impI (.impI (zero_cross f b _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedRecurrencePinning
