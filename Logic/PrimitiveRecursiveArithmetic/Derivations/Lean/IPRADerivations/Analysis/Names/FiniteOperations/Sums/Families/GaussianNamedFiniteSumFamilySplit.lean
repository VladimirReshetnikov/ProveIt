import IPRADerivations.Analysis.Names.FiniteOperations.Sums.Families.GaussianNamedFiniteSumFamily
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamilyAppend
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference

/-!
# Endpoint splits of finite sums of Gaussian names

The rational observations at one row clock split literally at the first
or last row. The different clocks of the original named sum and its split
are compared using the internal count. Removing the diagonal error
gives exact equivalence at independent requested precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilySplit

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedFiniteProductFamily (regularRows regular_at)
open GaussianNamedFiniteProductFamilyAppend (regular_prefix)
open GaussianNamedFiniteSumFamily (body data finite observation nameF term_at sample_at finite_distance regular)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent point_at_later)
open GaussianNameRingLaws (equivalent_of_envelope add_sample_error three)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem body_shift (f : PR 2) (t : PTm 2) : shiftBody (body f t) = body f (shiftBody t) := by
  change Syn.subst ![succ (var 0), var 1] (ap2 f (fstT (var 1)) (inst2 t (var 0) (sndT (var 1)))) = _
  simp only [subst_ap2,subst_inst2,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    body,inst2_shiftBody]

theorem finite_first (f : PR 2) (t : PTm 2) (p N x : PTm n) :
    Γ ⊢[PRAAx] finite f t p (succ N) x ≐ qadd (ap2 f p (inst2 t zero x)) (finite f (shiftBody t) p N x) := by
  have e := GaussianRationalFiniteSum.sum_shift_first (Γ := Γ) (body f t) N (pairT p x)
  rw [body_shift f t] at e
  exact e.eqTrans (qadd_congr (term_at f t zero p x) (.eqRefl _))

theorem finite_append (f : PR 2) (t : PTm 2) (p N x : PTm n) :
    Γ ⊢[PRAAx] finite f t p (succ N) x ≐ qadd (finite f t p N x) (ap2 f p (inst2 t N x)) :=
  (GaussianRationalFiniteSum.sum_succ (body f t) N (pairT p x)).eqTrans
    (qadd_congr (.eqRefl _) (term_at f t N p x))

theorem regular_tail (f : PR 2) (t : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (succ N) x) : Γ ⊢[PRAAx] regularRows f (shiftBody t) N x := by
  refine .allI (.impI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] regularRows f t (succ (sh N)) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) (sh N) := Prf.hyp0
  have hj : Δ ⊢[PRAAx] lt (succ (var 0)) (succ (sh N)) :=
    le_congr (succ_eq_add_one (succ (var 0))).eqSymm (succ_eq_add_one (sh N)).eqSymm (add_le_add_right one hi)
  rw [inst2_shiftBody]
  exact regular_at f t (succ (sh N)) (sh x) (succ (var 0)) hs hj

/-- Compare a literal sum at a sufficient row clock with the original
family sampler. Either clock can be the later one. -/
theorem finite_sample_distance (f : PR 2) (t : PTm 2) (k p N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t N x) (hk : Γ ⊢[PRAAx] le (N*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded (finite f t k N x) (ap2 (nameF f t) p (data N x)) two (unit p) := by
  let l := exponent N p
  have hl := query_budget (Γ := Γ) N p
  have hkl := positive_product _ _ (unit_positive (Γ := Γ) k) (unit_positive l)
  have e := finite_distance f t k l N x h
  have comparison : Γ ⊢[PRAAx] le ((N*(unit k+unit l))*unit p) (two*(unit k*unit l)) := by
    ipra_le 𝔞(unit l)*sl hk + 𝔞(unit k)*sl hl
  exact distance_congr (.eqRefl _) (sample_at f t p N x).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ two (unit p) hkl (unit_positive p) comparison e)

private theorem sum_readback (f g : PR 2) (z a b x y p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] z ≐ qadd a b)
    (ha : Γ ⊢[PRAAx] distanceBounded a (ap2 f p x) two (unit p))
    (hb : Γ ⊢[PRAAx] distanceBounded b (ap2 g p y) two (unit p)) :
    Γ ⊢[PRAAx] distanceBounded z (ap2 (addF f g) p (addData x y)) (num 7) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have e := distance_congr he.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hp ha hb)
  have o := distance_symmetric _ _ _ _ hp (add_sample_error f g x y p hf hg)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp e o)

theorem first_sample (f : PR 2) (t : PTm 2) (p N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (succ N) x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f t) p (data (succ N) x))
      (ap2 (addF f (nameF f (shiftBody t))) p (addData (inst2 t zero x) (data N x))) (num 7) (unit p) := by
  let k := exponent (succ N) p
  have hpk : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have hk := le_trans (mul_le_mul_right (unit p) (le_succ_self (Γ := Γ) N)) (query_budget (succ N) p)
  have hFirst := regular_at f t (succ N) x zero h (zero_lt_succ N)
  have hTail := regular_tail f t N x h
  have e := (sample_at (Γ := Γ) f t p (succ N) x).eqTrans (finite_first f t k N x)
  exact sum_readback f (nameF f (shiftBody t)) _ _ _ _ _ p hFirst (regular f (shiftBody t) N x hTail) e
    (point_at_later f (inst2 t zero x) p k hFirst hpk) (finite_sample_distance f (shiftBody t) k p N x hTail hk)

theorem append_sample (f : PR 2) (t : PTm 2) (p N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (succ N) x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f t) p (data (succ N) x))
      (ap2 (addF (nameF f t) f) p (addData (data N x) (inst2 t N x))) (num 7) (unit p) := by
  let k := exponent (succ N) p
  have hpk : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have hk := le_trans (mul_le_mul_right (unit p) (le_succ_self (Γ := Γ) N)) (query_budget (succ N) p)
  have hLast := regular_at f t (succ N) x N h (le_refl (succ N))
  have hInit := regular_prefix f t N (succ N) x (le_succ_self N) h
  have e := (sample_at (Γ := Γ) f t p (succ N) x).eqTrans (finite_append f t k N x)
  exact sum_readback (nameF f t) f _ _ _ _ _ p (regular f t N x hInit) hLast e
    (finite_sample_distance f t k p N x hInit hk) (point_at_later f (inst2 t N x) p k hLast hpk)

theorem first_cross (f : PR 2) (t : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (succ N) x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f t) (addF f (nameF f (shiftBody t))) (data (succ N) x)
      (addData (inst2 t zero x) (data N x)) := by
  have hFirst := regular_at f t (succ N) x zero h (zero_lt_succ N)
  have hTail := regular f (shiftBody t) N x (regular_tail f t N x h)
  refine equivalent_of_envelope _ _ _ _ (num 7) (regular f t (succ N) x h)
    (GaussianNameArithmetic.add_fast _ _ _ _ hFirst hTail) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] regularRows f t (succ (Syn.shift N)) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [Syn.shift,GaussianNamedFiniteSumFamily.subst_data,GaussianNameArithmetic.subst_addData,
    subst_inst2,PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using first_sample f t (var 0) (Syn.shift N) (Syn.shift x) hs

theorem append_cross (f : PR 2) (t : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (succ N) x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f t) (addF (nameF f t) f) (data (succ N) x)
      (addData (data N x) (inst2 t N x)) := by
  have hLast := regular_at f t (succ N) x N h (le_refl (succ N))
  have hInit := regular f t N x (regular_prefix f t N (succ N) x (le_succ_self N) h)
  refine equivalent_of_envelope _ _ _ _ (num 7) (regular f t (succ N) x h)
    (GaussianNameArithmetic.add_fast _ _ _ _ hInit hLast) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] regularRows f t (succ (Syn.shift N)) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [Syn.shift,GaussianNamedFiniteSumFamily.subst_data,GaussianNameArithmetic.subst_addData,
    subst_inst2,PTm.subst_num,ConciseIPRA.PTm.subst_succ] using append_sample f t (var 0) (Syn.shift N) (Syn.shift x) hs

theorem actual_named_finite_family_first_split_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (regularRows f t (succ (var 0)) (var 1) ⟶
        crossEquivalent (nameF f t) (addF f (nameF f (shiftBody t))) (data (succ (var 0)) (var 1))
          (addData (inst2 t zero (var 1)) (data (var 0) (var 1)))) :=
  closeUniv 2 (.impI (first_cross f t _ _ Prf.hyp0))

theorem actual_named_finite_family_append_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (regularRows f t (succ (var 0)) (var 1) ⟶
        crossEquivalent (nameF f t) (addF (nameF f t) f) (data (succ (var 0)) (var 1))
          (addData (data (var 0) (var 1)) (inst2 t (var 0) (var 1)))) :=
  closeUniv 2 (.impI (append_cross f t _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilySplit
