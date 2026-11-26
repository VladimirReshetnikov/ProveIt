import IPRADerivations.Analysis.RationalArithmetic.Distances.RationalSupMetric
import IPRADerivations.Foundations.FiniteHausdorffImage
import IPRADerivations.Foundations.RealizerComposition

/-!
# Hausdorff distance of arbitrary finite rational vector lists

The two original lists share the single actual pool `append S T`.
Normalization of this pool computes one positive denominator and actual
prefix/suffix grid blocks. The source cover predicate below refers directly
to the original independently denominated rational coordinates. Its
equivalence to a weighted bound on the computed Hausdorff numerator is proved
using actual normalized lookups, exact quotient clearing, coordinate maxima
and nearest-neighbor scans.

List nonemptiness remains explicit. A radius `A/B` has positive `B` for its
rational interpretation; the cleared arithmetic equivalence also permits
`B=0`. Triangle and invariance comparisons between results computed in
different common pools are not asserted here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalHausdorff

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric
open LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length append append_length append_left append_right entry_congr)
open LeanProofs.IPRA.Foundations.RealizerComposition (slice slice_length slice_lookup)
open LeanProofs.IPRA.Foundations.FiniteHausdorff
open LeanProofs.IPRA.Foundations.FiniteHausdorffImage
  (scaled_maximum_bound weighted_directed_bound scale_maximum)
open LeanProofs.IPRA.Foundations.DemandClosure (maximum_left maximum_right maximum_le)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr subst_zabs)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pool (S T : PTm n) : PTm n := append S T
def normalizedBlock (P d offset count : PTm n) : PTm n := slice (normalizedList P d) offset count

ipra_subst pool
ipra_subst normalizedBlock

theorem normalizedBlock_length (P d offset count : PTm n) :
    Γ ⊢[PRAAx] length (normalizedBlock P d offset count) ≐ count := slice_length _ _ _

theorem normalizedBlock_lookup (P d offset count i : PTm n) (hi : Γ ⊢[PRAAx] lt i count) :
    Γ ⊢[PRAAx] entry (normalizedBlock P d offset count) i ≐ entry (normalizedList P d) (offset + i) :=
  slice_lookup _ _ _ _ hi

/-- External proof indexing only; all list, dimension and position data are
ordinary internal numerical arguments. -/
inductive Side | left | right

def source : Side → PTm n → PTm n → PTm n
  | .left, S, _ => S
  | .right, _, T => T
def offset : Side → PTm n → PTm n → PTm n
  | .left, _, _ => zero
  | .right, S, _ => length S
def grid (s : Side) (S T d : PTm n) : PTm n :=
  normalizedBlock (pool S T) d (offset s S T) (length (source s S T))
def denominator (S T d : PTm n) : PTm n := commonDenominator (pool S T) d
def parameter (S T d : PTm n) : PTm n := metricData (pool S T) d

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (s : Side) (S T : PTm n) :
    Syn.subst σ (source s S T) = source s (Syn.subst σ S) (Syn.subst σ T) := by cases s <;> rfl
@[simp] theorem subst_offset {m : ℕ} (σ : Fin n → PTm m) (s : Side) (S T : PTm n) :
    Syn.subst σ (offset s S T) = offset s (Syn.subst σ S) (Syn.subst σ T) := by cases s <;> simp [offset]
ipra_subst grid
ipra_subst denominator
ipra_subst parameter

theorem grid_length (s : Side) (S T d : PTm n) : Γ ⊢[PRAAx] length (grid s S T d) ≐ length (source s S T) :=
  normalizedBlock_length _ _ _ _

theorem source_index_bound (s : Side) (S T i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) :
    Γ ⊢[PRAAx] lt (offset s S T + i) (length (pool S T)) := by
  cases s with
  | left =>
    exact lt_congr (zero_add i).eqSymm (append_length S T).eqSymm
      (lt_of_lt_of_le hi (le_add_right _ _))
  | right =>
    exact lt_congr (.eqRefl _) (append_length S T).eqSymm (SequenceComposition.add_lt_left _ hi)

theorem source_membership (s : Side) (S T i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) :
    Γ ⊢[PRAAx] entry (pool S T) (offset s S T + i) ≐ entry (source s S T) i := by
  cases s with
  | left => exact (entry_congr (.eqRefl _) (zero_add i)).eqTrans (append_left hi)
  | right => exact append_right hi

theorem grid_lookup (s : Side) (S T d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) :
    Γ ⊢[PRAAx] entry (grid s S T d) i ≐ entry (normalizedList (pool S T) d) (offset s S T + i) :=
  normalizedBlock_lookup _ _ _ _ _ hi

theorem grid_point_length (s : Side) (S T d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) :
    Γ ⊢[PRAAx] length (entry (grid s S T d) i) ≐ d :=
  (congrFst (grid_lookup s S T d i hi)).eqTrans
    ((congrFst (normalizedList_lookup _ _ _ (source_index_bound s S T i hi))).eqTrans (normalizedVector_length _ _ _))

theorem rationalDenominator_congr {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) (k : PTm n) :
    Γ ⊢[PRAAx] rationalDenominator x k ≐ rationalDenominator y k :=
  congrSucc (congrSnd (entry_congr h (.eqRefl _)))

theorem rationalNumerator_value_congr {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) (k : PTm n) :
    ZT.toZ Γ (rationalNumerator x k) = ZT.toZ Γ (rationalNumerator y k) := by
  simp only [rationalNumerator, numeratorOf, ZT.toZ]
  rw [natEq (congrFst (congrFst (entry_congr h (.eqRefl _)))),
    natEq (congrSnd (congrFst (entry_congr h (.eqRefl _))))]

theorem coordinate_value_congr {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) (k : PTm n) :
    ZT.toZ Γ (coordinate x k) = ZT.toZ Γ (coordinate y k) := by
  simp only [coordinate, ZT.toZ]
  rw [natEq (congrFst (entry_congr h (.eqRefl _))), natEq (congrSnd (entry_congr h (.eqRefl _)))]

/-- Actual prefix/suffix blocks preserve every original rational coordinate. -/
theorem grid_coordinate (s : Side) (S T d i k : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hk : Γ ⊢[PRAAx] lt k d) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (rationalDenominator (entry (source s S T) i) k) * coordinate (entry (grid s S T d) i) k)
      (ZT.ofNat (denominator S T d) * rationalNumerator (entry (source s S T) i) k) := by
  have actual := ZT.toZ_eq (normalized_coordinate (pool S T) d (offset s S T + i) k
    (source_index_bound s S T i hi) hk)
  have member := source_membership s S T i hi
  apply ZT.derive
  rw [ZT.toZ_mul, ZT.toZ_ofNat, coordinate_value_congr (grid_lookup s S T d i hi) k,
    ZT.toZ_mul, ZT.toZ_ofNat]
  simp only [ZT.toZ_mul, ZT.toZ_ofNat] at actual
  rw [natEq (rationalDenominator_congr member k), rationalNumerator_value_congr member k] at actual
  exact actual

def crossNumerator (x y k : PTm n) : ZT n :=
  rationalNumerator x k * ZT.ofNat (rationalDenominator y k) -
    rationalNumerator y k * ZT.ofNat (rationalDenominator x k)
def denominatorProduct (x y k : PTm n) : PTm n := rationalDenominator x k * rationalDenominator y k

ipra_subst crossNumerator
ipra_subst denominatorProduct

theorem grid_difference (s t : Side) (S T d i j k : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hj : Γ ⊢[PRAAx] lt j (length (source t S T)))
    (hk : Γ ⊢[PRAAx] lt k d) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (denominatorProduct (entry (source s S T) i) (entry (source t S T) j) k) *
        coordinateDifference (entry (grid s S T d) i) (entry (grid t S T d) j) k)
      (ZT.ofNat (denominator S T d) * crossNumerator (entry (source s S T) i) (entry (source t S T) j) k) := by
  have actual := ZT.toZ_eq (normalized_difference (pool S T) d (offset s S T + i) (offset t S T + j) k
    (source_index_bound s S T i hi) (source_index_bound t S T j hj) hk)
  have memberI := source_membership s S T i hi
  have memberJ := source_membership t S T j hj
  apply ZT.derive
  simp only [denominatorProduct, crossNumerator, coordinateDifference, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat,
    Q.mk_mul, map_mul]
  rw [coordinate_value_congr (grid_lookup s S T d i hi) k, coordinate_value_congr (grid_lookup t S T d j hj) k]
  simp only [coordinateDifference, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat, Q.mk_mul, map_mul] at actual
  rw [natEq (rationalDenominator_congr memberI k), natEq (rationalDenominator_congr memberJ k),
    rationalNumerator_value_congr memberI k, rationalNumerator_value_congr memberJ k] at actual
  exact actual

private theorem abs_scale (c : PTm n) (u : ZT n) : Γ ⊢[PRAAx] zabs (ZT.ofNat c * u) ≐ c * zabs u := by
  have equal : ZT.toZ Γ (ZT.ofNat c * u) = ZT.toZ Γ (⟨c * u.pos, c * u.neg⟩ : ZT n) := by
    rw [ZT.toZ_mul, ZT.toZ_ofNat]
    simp only [ZT.toZ, Q.mk_mul, map_mul]
    ring
  exact (zabs_congr equal).eqTrans (Probability.MedianWeighted.ad_mul c u.pos u.neg)

theorem grid_distance_clears (s t : Side) (S T d i j k : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hj : Γ ⊢[PRAAx] lt j (length (source t S T)))
    (hk : Γ ⊢[PRAAx] lt k d) :
    Γ ⊢[PRAAx] denominatorProduct (entry (source s S T) i) (entry (source t S T) j) k *
      coordinateDistance (entry (grid s S T d) i) (entry (grid t S T d) j) k ≐
      denominator S T d * zabs (crossNumerator (entry (source s S T) i) (entry (source t S T) j) k) :=
  (abs_scale _ _).eqSymm.eqTrans ((zabs_congr (ZT.toZ_eq (grid_difference s t S T d i j k hi hj hk))).eqTrans (abs_scale _ _))

#print axioms grid_coordinate
#print axioms grid_difference
#print axioms grid_distance_clears

/-! ## Original rational-coordinate radii and actual grid point distances -/

def coordinateRadius (x y k A B : PTm n) : Fm PTm n :=
  le (B * zabs (crossNumerator x y k)) (A * denominatorProduct x y k)
def pointRadius (x y d A B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift d) ⟶ coordinateRadius (Syn.shift x) (Syn.shift y) (var 0) (Syn.shift A) (Syn.shift B))

@[simp] theorem subst_coordinateRadius {m : ℕ} (σ : Fin n → PTm m) (x y k A B : PTm n) :
    (coordinateRadius x y k A B).subst σ = coordinateRadius (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [coordinateRadius, subst_le, PTm.subst_mul, subst_zabs, subst_crossNumerator, subst_denominatorProduct]
ipra_subst pointRadius [Fm.subst_all, Fm.subst_imp, subst_lt, subst_coordinateRadius, Syn.subst_var, Syn.up_zero,
    Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem pointRadius_at (x y d A B k : PTm n) (h : Γ ⊢[PRAAx] pointRadius x y d A B) (hk : Γ ⊢[PRAAx] lt k d) :
    Γ ⊢[PRAAx] coordinateRadius x y k A B := by
  have rule : Γ ⊢[PRAAx] lt k d ⟶ coordinateRadius x y k A B := by
    simpa only [pointRadius, Fm.subst_imp, subst_lt, subst_coordinateRadius, Syn.subst_var,
      Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE k h
  exact .impE rule hk

private alias positive_cancel := Common.mul_cancel_le

theorem rationalDenominator_one_le (x k : PTm n) : Γ ⊢[PRAAx] le one (rationalDenominator x k) :=
  (succ_monus_succ zero _).eqTrans (zero_le _)

theorem denominatorProduct_one_le (x y k : PTm n) : Γ ⊢[PRAAx] le one (denominatorProduct x y k) :=
  le_congr (one_mul one) (.eqRefl _)
    (le_mul_mono (rationalDenominator_one_le x k) (rationalDenominator_one_le y k))

theorem source_coordinate_bound (s t : Side) (S T d i j k A B : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hj : Γ ⊢[PRAAx] lt j (length (source t S T)))
    (hk : Γ ⊢[PRAAx] lt k d)
    (h : Γ ⊢[PRAAx] coordinateRadius (entry (source s S T) i) (entry (source t S T) j) k A B) :
    Γ ⊢[PRAAx] le (B * coordinateDistance (entry (grid s S T d) i) (entry (grid t S T d) j) k)
      (A * denominator S T d) := by
  have scaled := mul_le_mul_right (denominator S T d) h
  have left : Γ ⊢[PRAAx]
      (B * zabs (crossNumerator (entry (source s S T) i) (entry (source t S T) j) k)) * denominator S T d ≐
      denominatorProduct (entry (source s S T) i) (entry (source t S T) j) k *
        (B * coordinateDistance (entry (grid s S T d) i) (entry (grid t S T d) j) k) := by
    ipra_lc -(Groth.ι (Q.mk Γ B)) * natEq (grid_distance_clears s t S T d i j k hi hj hk)
  exact positive_cancel (denominatorProduct_one_le _ _ _) (le_congr left (by ipra_ring) scaled)

theorem grid_coordinate_bound (s t : Side) (S T d i j k A B : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hj : Γ ⊢[PRAAx] lt j (length (source t S T)))
    (hk : Γ ⊢[PRAAx] lt k d)
    (h : Γ ⊢[PRAAx] le (B * coordinateDistance (entry (grid s S T d) i) (entry (grid t S T d) j) k)
      (A * denominator S T d)) :
    Γ ⊢[PRAAx] coordinateRadius (entry (source s S T) i) (entry (source t S T) j) k A B := by
  have scaled := mul_le_mul_right (denominatorProduct (entry (source s S T) i) (entry (source t S T) j) k) h
  have left : Γ ⊢[PRAAx]
      (B * coordinateDistance (entry (grid s S T d) i) (entry (grid t S T d) j) k) *
        denominatorProduct (entry (source s S T) i) (entry (source t S T) j) k ≐
      denominator S T d * (B * zabs (crossNumerator (entry (source s S T) i) (entry (source t S T) j) k)) := by
    ipra_lc (Groth.ι (Q.mk Γ B)) * natEq (grid_distance_clears s t S T d i j k hi hj hk)
  have positive : Γ ⊢[PRAAx] le one (denominator S T d) := commonDenominator_one_le _ _
  exact positive_cancel positive (le_congr left (by ipra_ring) scaled)

theorem metric_bound_of_coordinates (P d x y B R : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift d) ⟶
      le (Syn.shift B * coordinateDistance (Syn.shift x) (Syn.shift y) (var 0)) (Syn.shift R))) :
    Γ ⊢[PRAAx] le (B * distance metricF x y (metricData P d)) R := by
  have sup : Γ ⊢[PRAAx] le (B * supDistance x y d) R := by
    apply scaled_maximum_bound
    refine .allI (.impI ?_)
    have value := Prf.impE h.allOpen.wk Prf.hyp0
    simpa only [Syn.shift, subst_pairT] using le_congr
      (congrMul (.eqRefl (Syn.shift B)) (distanceBody_at (Syn.shift x) (Syn.shift y) (var 0)).eqSymm) (.eqRefl _) value
  exact le_congr (congrMul (.eqRefl _) (metricData_distance P d x y).eqSymm) (.eqRefl _) sup

theorem coordinate_bound_of_metric (P d x y k B R : PTm n) (hk : Γ ⊢[PRAAx] lt k d)
    (h : Γ ⊢[PRAAx] le (B * distance metricF x y (metricData P d)) R) :
    Γ ⊢[PRAAx] le (B * coordinateDistance x y k) R :=
  le_trans (le_mul_mono (le_refl B) (coordinate_bound x y d k hk))
    (le_congr (congrMul (.eqRefl _) (metricData_distance P d x y)) (.eqRefl _) h)

theorem point_radius_to_metric (s t : Side) (S T d i j A B : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hj : Γ ⊢[PRAAx] lt j (length (source t S T)))
    (h : Γ ⊢[PRAAx] pointRadius (entry (source s S T) i) (entry (source t S T) j) d A B) :
    Γ ⊢[PRAAx] le (B * distance metricF (entry (grid s S T d) i) (entry (grid t S T d) j) (parameter S T d))
      (A * denominator S T d) := by
  apply metric_bound_of_coordinates
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have indexI : Δ ⊢[PRAAx] lt (Syn.shift i) (length (source s (Syn.shift S) (Syn.shift T))) := by
    simpa only [Fm.shift, subst_lt, SequenceComposition.subst_length, subst_source, Syn.shift] using hi.shift.wk
  have indexJ : Δ ⊢[PRAAx] lt (Syn.shift j) (length (source t (Syn.shift S) (Syn.shift T))) := by
    simpa only [Fm.shift, subst_lt, SequenceComposition.subst_length, subst_source, Syn.shift] using hj.shift.wk
  have radius : Δ ⊢[PRAAx] pointRadius (entry (source s (Syn.shift S) (Syn.shift T)) (Syn.shift i))
      (entry (source t (Syn.shift S) (Syn.shift T)) (Syn.shift j)) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_pointRadius, MasterCertificate.subst_entry, subst_source, Syn.shift] using h.shift.wk
  have result := source_coordinate_bound s t (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift i) (Syn.shift j)
    (var 0) (Syn.shift A) (Syn.shift B) indexI indexJ Prf.hyp0 (pointRadius_at _ _ _ _ _ _ radius Prf.hyp0)
  simpa only [Δ, Syn.shift, PTm.subst_mul, subst_denominator, MasterCertificate.subst_entry, subst_grid] using result

theorem metric_to_point_radius (s t : Side) (S T d i j A B : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hj : Γ ⊢[PRAAx] lt j (length (source t S T)))
    (h : Γ ⊢[PRAAx] le (B * distance metricF (entry (grid s S T d) i) (entry (grid t S T d) j) (parameter S T d))
      (A * denominator S T d)) :
    Γ ⊢[PRAAx] pointRadius (entry (source s S T) i) (entry (source t S T) j) d A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have indexI : Δ ⊢[PRAAx] lt (Syn.shift i) (length (source s (Syn.shift S) (Syn.shift T))) := by
    simpa only [Fm.shift, subst_lt, SequenceComposition.subst_length, subst_source, Syn.shift] using hi.shift.wk
  have indexJ : Δ ⊢[PRAAx] lt (Syn.shift j) (length (source t (Syn.shift S) (Syn.shift T))) := by
    simpa only [Fm.shift, subst_lt, SequenceComposition.subst_length, subst_source, Syn.shift] using hj.shift.wk
  have bound : Δ ⊢[PRAAx] le (Syn.shift B * distance metricF
      (entry (grid s (Syn.shift S) (Syn.shift T) (Syn.shift d)) (Syn.shift i))
      (entry (grid t (Syn.shift S) (Syn.shift T) (Syn.shift d)) (Syn.shift j))
      (parameter (Syn.shift S) (Syn.shift T) (Syn.shift d))) (Syn.shift A * denominator (Syn.shift S) (Syn.shift T) (Syn.shift d)) := by
    simpa only [Fm.shift, subst_le, PTm.subst_mul, subst_distance, MasterCertificate.subst_entry,
      subst_grid, subst_parameter, subst_denominator, Syn.shift] using h.shift.wk
  have result := grid_coordinate_bound s t (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift i) (Syn.shift j)
    (var 0) (Syn.shift A) (Syn.shift B) indexI indexJ Prf.hyp0
    (coordinate_bound_of_metric _ _ _ _ _ _ _ Prf.hyp0 bound)
  simpa only [Δ, Syn.shift, MasterCertificate.subst_entry, subst_source] using result

#print axioms source_coordinate_bound
#print axioms grid_coordinate_bound
#print axioms point_radius_to_metric
#print axioms metric_to_point_radius

/-! ## The source cover uses only original rational coordinates -/

def originalHit (s t : Side) (S T d A B i : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (length (source t (Syn.shift S) (Syn.shift T))) ⋏
    pointRadius (entry (source s (Syn.shift S) (Syn.shift T)) (Syn.shift i))
      (entry (source t (Syn.shift S) (Syn.shift T)) (var 0)) (Syn.shift d) (Syn.shift A) (Syn.shift B))

def originalCover (s t : Side) (S T d A B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (source s (Syn.shift S) (Syn.shift T))) ⟶
    originalHit s t (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift A) (Syn.shift B) (var 0))

def originalClose (S T d A B : PTm n) : Fm PTm n :=
  originalCover .left .right S T d A B ⋏ originalCover .right .left S T d A B

ipra_subst originalHit [Fm.subst_ex, Fm.subst_and, subst_lt, SequenceComposition.subst_length, subst_source,
    MasterCertificate.subst_entry, subst_pointRadius, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift,
    Syn.shift_subst]

ipra_subst originalCover [Fm.subst_all, Fm.subst_imp, subst_lt, SequenceComposition.subst_length, subst_source,
    subst_originalHit, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

ipra_subst originalClose

theorem originalCover_at (s t : Side) (S T d A B i : PTm n)
    (h : Γ ⊢[PRAAx] originalCover s t S T d A B) (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) :
    Γ ⊢[PRAAx] originalHit s t S T d A B i := by
  have rule : Γ ⊢[PRAAx] lt i (length (source s S T)) ⟶ originalHit s t S T d A B i := by
    simpa only [originalCover, Fm.subst_imp, subst_lt, SequenceComposition.subst_length, subst_source,
      subst_originalHit, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE i h
  exact .impE rule hi

theorem originalHit_intro (s t : Side) (S T d A B i j : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length (source t S T)))
    (h : Γ ⊢[PRAAx] pointRadius (entry (source s S T) i) (entry (source t S T) j) d A B) :
    Γ ⊢[PRAAx] originalHit s t S T d A B i := by
  refine .exI j ?_
  simpa only [originalHit, Fm.subst_and, subst_lt, SequenceComposition.subst_length, subst_source,
    subst_pointRadius, MasterCertificate.subst_entry, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.andI hj h

theorem minimum_bound_of_original_hit (s t : Side) (S T d i A B : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (h : Γ ⊢[PRAAx] originalHit s t S T d A B i) :
    Γ ⊢[PRAAx] le (B * distanceTo metricF (entry (grid s S T d) i) (grid t S T d) (parameter S T d))
      (A * denominator S T d) := by
  refine .exE h ?_
  let E : Fm PTm (n + 1) := lt (var 0) (length (source t (Syn.shift S) (Syn.shift T))) ⋏
    pointRadius (entry (source s (Syn.shift S) (Syn.shift T)) (Syn.shift i))
      (entry (source t (Syn.shift S) (Syn.shift T)) (var 0)) (Syn.shift d) (Syn.shift A) (Syn.shift B)
  have indexI : E :: Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (source s (Syn.shift S) (Syn.shift T))) := by
    simpa only [Fm.shift, subst_lt, SequenceComposition.subst_length, subst_source, Syn.shift] using hi.shift.wk
  have indexJ : E :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (length (source t (Syn.shift S) (Syn.shift T))) :=
    Prf.andE₁ Prf.hyp0
  have gridJ : E :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (length (grid t (Syn.shift S) (Syn.shift T) (Syn.shift d))) :=
    lt_congr (.eqRefl _) (grid_length t _ _ _).eqSymm indexJ
  have point := point_radius_to_metric s t (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift i) (var 0)
    (Syn.shift A) (Syn.shift B) indexI indexJ (Prf.andE₂ Prf.hyp0)
  have bound := le_trans (le_mul_mono (le_refl (Syn.shift B)) (distanceTo_le metricF _ _ _ (var 0) gridJ)) point
  simpa only [E, Fm.shift, subst_le, PTm.subst_mul, subst_distanceTo, MasterCertificate.subst_entry,
    subst_grid, subst_parameter, subst_denominator, Syn.shift] using bound

/-- Weighted directed distance follows from original rational witnesses. -/
theorem directed_bound_of_original (s t : Side) (S T d A B : PTm n)
    (h : Γ ⊢[PRAAx] originalCover s t S T d A B) :
    Γ ⊢[PRAAx] le (B * directed metricF (grid s S T d) (grid t S T d) (parameter S T d))
      (A * denominator S T d) := by
  apply weighted_directed_bound
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (grid s (Syn.shift S) (Syn.shift T) (Syn.shift d))) :: Γ.map Fm.shift
  have index : Δ ⊢[PRAAx] lt (var 0) (length (source s (Syn.shift S) (Syn.shift T))) :=
    lt_congr (.eqRefl _) (grid_length s _ _ _) Prf.hyp0
  have cover : Γ.map Fm.shift ⊢[PRAAx] originalCover s t (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_originalCover, Syn.shift] using h.shift
  have result := minimum_bound_of_original_hit s t (Syn.shift S) (Syn.shift T) (Syn.shift d) (var 0)
    (Syn.shift A) (Syn.shift B) index (originalCover_at s t _ _ _ _ _ _ cover.wk index)
  simpa only [Δ, Syn.shift, PTm.subst_mul, subst_grid, subst_parameter, subst_denominator] using result

/-- Actual least nearest indices reconstruct original rational witnesses. -/
theorem original_of_directed_bound (s t : Side) (S T d A B : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length (source t S T)))
    (h : Γ ⊢[PRAAx] le (B * directed metricF (grid s S T d) (grid t S T d) (parameter S T d))
      (A * denominator S T d)) : Γ ⊢[PRAAx] originalCover s t S T d A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (source s (Syn.shift S) (Syn.shift T))) :: Γ.map Fm.shift
  let u := entry (grid s (Syn.shift S) (Syn.shift T) (Syn.shift d)) (var 0)
  let target := grid t (Syn.shift S) (Syn.shift T) (Syn.shift d)
  let p := parameter (Syn.shift S) (Syn.shift T) (Syn.shift d)
  let j := nearest metricF u target p
  have targetPositive : Δ ⊢[PRAAx] le one (length target) := by
    have raw : Δ ⊢[PRAAx] le one (length (source t (Syn.shift S) (Syn.shift T))) := by
      simpa only [Fm.shift, subst_le, SequenceComposition.subst_length, subst_source,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hT.shift.wk
    exact le_congr (.eqRefl _) (grid_length t _ _ _).eqSymm raw
  have gridI : Δ ⊢[PRAAx] lt (var 0) (length (grid s (Syn.shift S) (Syn.shift T) (Syn.shift d))) :=
    lt_congr (.eqRefl _) (grid_length s _ _ _).eqSymm Prf.hyp0
  have gridJ : Δ ⊢[PRAAx] lt j (length target) := Prf.andE₁ (nearest_spec metricF u target p targetPositive)
  have sourceJ : Δ ⊢[PRAAx] lt j (length (source t (Syn.shift S) (Syn.shift T))) :=
    lt_congr (.eqRefl _) (grid_length t _ _ _) gridJ
  have bound : Δ ⊢[PRAAx] le (Syn.shift B * directed metricF
      (grid s (Syn.shift S) (Syn.shift T) (Syn.shift d)) target p)
      (Syn.shift A * denominator (Syn.shift S) (Syn.shift T) (Syn.shift d)) := by
    simpa only [Fm.shift, subst_le, PTm.subst_mul, subst_directed, subst_grid,
      subst_parameter, subst_denominator, Syn.shift, target, p] using h.shift.wk
  have point := le_trans (le_mul_mono (le_refl (Syn.shift B))
    (nearest_error metricF (grid s (Syn.shift S) (Syn.shift T) (Syn.shift d)) target p (var 0) targetPositive gridI)) bound
  have radius := metric_to_point_radius s t (Syn.shift S) (Syn.shift T) (Syn.shift d) (var 0) j
    (Syn.shift A) (Syn.shift B) (Prf.hyp0 : Δ ⊢[PRAAx] _) sourceJ point
  exact originalHit_intro s t _ _ _ _ _ _ j sourceJ radius

def numerator (S T d : PTm n) : PTm n := hausdorff metricF (grid .left S T d) (grid .right S T d) (parameter S T d)
def rationalHausdorff (S T d : PTm n) : PTm n := pairT (numerator S T d) (denominator S T d)

ipra_subst numerator
ipra_subst rationalHausdorff

theorem bound_of_original_close (S T d A B : PTm n) (h : Γ ⊢[PRAAx] originalClose S T d A B) :
    Γ ⊢[PRAAx] le (B * numerator S T d) (A * denominator S T d) :=
  le_congr (scale_maximum B _ _).eqSymm (.eqRefl _)
    (maximum_le (directed_bound_of_original .left .right S T d A B (Prf.andE₁ h))
      (directed_bound_of_original .right .left S T d A B (Prf.andE₂ h)))

theorem original_close_of_bound (S T d A B : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] le (B * numerator S T d) (A * denominator S T d)) :
    Γ ⊢[PRAAx] originalClose S T d A B :=
  .andI (original_of_directed_bound .left .right S T d A B hT
    (le_trans (le_mul_mono (le_refl B) (maximum_left _ _)) h))
    (original_of_directed_bound .right .left S T d A B hS
      (le_trans (le_mul_mono (le_refl B) (maximum_right _ _)) h))

/-- Exact original-coordinate cover iff the actual computed rational bound. -/
theorem original_cover_iff (S T d A B : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] Fm.iff (originalClose S T d A B) (le (B * numerator S T d) (A * denominator S T d)) :=
  .iffI (.impI (bound_of_original_close S T d A B Prf.hyp0))
    (.impI (original_close_of_bound S T d A B hS.wk hT.wk Prf.hyp0))

#print axioms minimum_bound_of_original_hit
#print axioms directed_bound_of_original
#print axioms original_of_directed_bound
#print axioms original_cover_iff

/-! ## Actual fixed PR output and normalization metadata -/

def blockF : PR 4 := PTm.toPR (normalizedBlock (var 0) (var 1) (var 2) (var 3))
def leftF : PR 3 := PTm.toPR (grid .left (var 0) (var 1) (var 2))
def rightF : PR 3 := PTm.toPR (grid .right (var 0) (var 1) (var 2))
def numeratorF : PR 3 := PTm.toPR (numerator (var 0) (var 1) (var 2))
def denominatorF : PR 3 := PTm.toPR (denominator (var 0) (var 1) (var 2))
def codeF : PR 3 := PTm.toPR (rationalHausdorff (var 0) (var 1) (var 2))

theorem block_at (P d offset count : PTm n) :
    Γ ⊢[PRAAx] FiniteQueryDemand.apply4 blockF P d offset count ≐ normalizedBlock P d offset count := by
  have h := toPR_eq (Γ := Γ) (normalizedBlock (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P, d, offset, count]
  simpa [blockF, FiniteQueryDemand.apply4] using h
theorem left_at (S T d : PTm n) : Γ ⊢[PRAAx] ap3 leftF S T d ≐ grid .left S T d := by
  have h := toPR_eq (Γ := Γ) (grid .left (var 0) (var 1) (var 2) : PTm 3) ![S, T, d]
  simpa [leftF, ap3] using h
theorem right_at (S T d : PTm n) : Γ ⊢[PRAAx] ap3 rightF S T d ≐ grid .right S T d := by
  have h := toPR_eq (Γ := Γ) (grid .right (var 0) (var 1) (var 2) : PTm 3) ![S, T, d]
  simpa [rightF, ap3] using h
theorem numerator_at (S T d : PTm n) : Γ ⊢[PRAAx] ap3 numeratorF S T d ≐ numerator S T d := by
  have h := toPR_eq (Γ := Γ) (numerator (var 0) (var 1) (var 2) : PTm 3) ![S, T, d]
  simpa [numeratorF, ap3] using h
theorem denominator_at (S T d : PTm n) : Γ ⊢[PRAAx] ap3 denominatorF S T d ≐ denominator S T d := by
  have h := toPR_eq (Γ := Γ) (denominator (var 0) (var 1) (var 2) : PTm 3) ![S, T, d]
  simpa [denominatorF, ap3] using h
theorem code_at (S T d : PTm n) : Γ ⊢[PRAAx] ap3 codeF S T d ≐ pairT (numerator S T d) (denominator S T d) := by
  have h := toPR_eq (Γ := Γ) (rationalHausdorff (var 0) (var 1) (var 2) : PTm 3) ![S, T, d]
  simpa [codeF, ap3, rationalHausdorff] using h

theorem code_numerator (S T d : PTm n) : Γ ⊢[PRAAx] fstT (ap3 codeF S T d) ≐ numerator S T d :=
  (code_at S T d).fstE
theorem code_denominator (S T d : PTm n) : Γ ⊢[PRAAx] sndT (ap3 codeF S T d) ≐ denominator S T d :=
  (code_at S T d).sndE
theorem code_positive (S T d : PTm n) : Γ ⊢[PRAAx] le one (sndT (ap3 codeF S T d)) :=
  le_congr (.eqRefl _) (code_denominator S T d).eqSymm (commonDenominator_one_le _ _)

/-- The exported PR rational code, interpreted as numerator/positive
denominator, is the original-coordinate Hausdorff value. -/
theorem original_code_cover_iff (S T d A B : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] Fm.iff (originalClose S T d A B)
      (le (B * fstT (ap3 codeF S T d)) (A * sndT (ap3 codeF S T d))) :=
  .iffI (.impI (le_congr (congrMul (.eqRefl _) (code_numerator S T d).eqSymm)
    (congrMul (.eqRefl _) (code_denominator S T d).eqSymm) (bound_of_original_close S T d A B Prf.hyp0)))
    (.impI (original_close_of_bound S T d A B hS.wk hT.wk
      (le_congr (congrMul (.eqRefl _) (code_numerator S T d))
        (congrMul (.eqRefl _) (code_denominator S T d)) Prf.hyp0)))

def metadataFormula : Fm PTm 3 :=
  (ap3 leftF (var 0) (var 1) (var 2) ≐ grid .left (var 0) (var 1) (var 2)) ⋏
  ((ap3 rightF (var 0) (var 1) (var 2) ≐ grid .right (var 0) (var 1) (var 2)) ⋏
  ((ap3 numeratorF (var 0) (var 1) (var 2) ≐ numerator (var 0) (var 1) (var 2)) ⋏
  ((ap3 denominatorF (var 0) (var 1) (var 2) ≐ denominator (var 0) (var 1) (var 2)) ⋏
  ((ap3 codeF (var 0) (var 1) (var 2) ≐ pairT (numerator (var 0) (var 1) (var 2)) (denominator (var 0) (var 1) (var 2))) ⋏
    le one (sndT (ap3 codeF (var 0) (var 1) (var 2)))))))

theorem rational_hausdorff_programs : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 metadataFormula :=
  closeUniv 3 (.andI (left_at _ _ _) (.andI (right_at _ _ _) (.andI (numerator_at _ _ _)
    (.andI (denominator_at _ _ _) (.andI (code_at _ _ _) (code_positive _ _ _))))))

theorem normalized_block_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((length (normalizedBlock (var 0) (var 1) (var 2) (var 3)) ≐ var 3) ⋏
      (lt (var 4) (var 3) ⟶ (entry (normalizedBlock (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        entry (normalizedList (var 0) (var 1)) (var 2 + var 4)))) :=
  closeUniv 5 (.andI (normalizedBlock_length _ _ _ _) (.impI (normalizedBlock_lookup _ _ _ _ _ Prf.hyp0)))

theorem original_coordinate_preservation (s : Side) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (lt (var 3) (length (source s (var 0) (var 1))) ⟶ lt (var 4) (var 2) ⟶
        ZT.eq (ZT.ofNat (rationalDenominator (entry (source s (var 0) (var 1)) (var 3)) (var 4)) *
          coordinate (entry (grid s (var 0) (var 1) (var 2)) (var 3)) (var 4))
          (ZT.ofNat (denominator (var 0) (var 1) (var 2)) *
            rationalNumerator (entry (source s (var 0) (var 1)) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (grid_coordinate s _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- All five arguments are internal numerical data. `B≥1` is unnecessary
for this cleared algebraic equivalence; rational clients may retain it. -/
theorem original_cover_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
        Fm.iff (originalClose (var 0) (var 1) (var 2) (var 3) (var 4))
          (le (var 4 * numerator (var 0) (var 1) (var 2)) (var 3 * denominator (var 0) (var 1) (var 2)))) :=
  closeUniv 5 (.impI (.impI (original_cover_iff _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_code_cover_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
        Fm.iff (originalClose (var 0) (var 1) (var 2) (var 3) (var 4))
          (le (var 4 * fstT (ap3 codeF (var 0) (var 1) (var 2)))
            (var 3 * sndT (ap3 codeF (var 0) (var 1) (var 2))))) :=
  closeUniv 5 (.impI (.impI (original_code_cover_iff _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

#print axioms block_at
#print axioms code_positive
#print axioms original_code_cover_iff
#print axioms rational_hausdorff_programs
#print axioms normalized_block_closed
#print axioms original_coordinate_preservation
#print axioms original_cover_closed
#print axioms original_code_cover_closed

/-! ## The actual PR radius checker on original rational inputs -/

def apply5 (f : PR 5) (a b c d e : PTm n) : PTm n := ConciseIPRA.PTm.app f ![a, b, c, d, e]

@[simp] theorem subst_apply5 {m : ℕ} (σ : Fin n → PTm m) (f : PR 5) (a b c d e : PTm n) :
    Syn.subst σ (apply5 f a b c d e) = apply5 f (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ e) := by
  show ConciseIPRA.PTm.app _ _ = ConciseIPRA.PTm.app _ _
  congr 1; funext i; fin_cases i <;> rfl

def checkerTerm (S T d A B : PTm n) : PTm n :=
  eqb (monus (B * fstT (ap3 codeF S T d)) (A * sndT (ap3 codeF S T d))) zero
def checkerF : PR 5 := PTm.toPR (checkerTerm (var 0) (var 1) (var 2) (var 3) (var 4))

ipra_subst checkerTerm

theorem checker_at (S T d A B : PTm n) :
    Γ ⊢[PRAAx] apply5 checkerF S T d A B ≐ checkerTerm S T d A B := by
  have h := toPR_eq (Γ := Γ) (checkerTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![S, T, d, A, B]
  simpa [checkerF, apply5] using h

theorem checker_cases (S T d A B : PTm n) :
    Γ ⊢[PRAAx] (apply5 checkerF S T d A B ≐ zero) ⋎ (apply5 checkerF S T d A B ≐ one) := by
  refine .orE (BoundedReflection.eqb_cases
    (monus (B * fstT (ap3 codeF S T d)) (A * sndT (ap3 codeF S T d))) zero) ?_ ?_
  · exact .orI₁ ((checker_at S T d A B).eqTrans Prf.hyp0)
  · exact .orI₂ ((checker_at S T d A B).eqTrans Prf.hyp0)

theorem checker_sound (S T d A B : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] apply5 checkerF S T d A B ≐ one) : Γ ⊢[PRAAx] originalClose S T d A B := by
  have bound := BoundedReflection.eq_of_eqb ((checker_at S T d A B).eqSymm.eqTrans h)
  exact original_close_of_bound S T d A B hS hT
    (le_congr (congrMul (.eqRefl _) (code_numerator S T d))
      (congrMul (.eqRefl _) (code_denominator S T d)) bound)

theorem checker_complete (S T d A B : PTm n) (h : Γ ⊢[PRAAx] originalClose S T d A B) :
    Γ ⊢[PRAAx] apply5 checkerF S T d A B ≐ one := by
  have bound := le_congr (congrMul (.eqRefl _) (code_numerator S T d).eqSymm)
    (congrMul (.eqRefl _) (code_denominator S T d).eqSymm) (bound_of_original_close S T d A B h)
  exact (checker_at S T d A B).eqTrans (eqb_of_eq bound)

/-- `eq:finite-cover` on the original independently denominated vectors,
checked by actual PR Hausdorff comparison rather than a supplied checker law. -/
theorem checker_reflection (S T d A B : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] Fm.iff (apply5 checkerF S T d A B ≐ one) (originalClose S T d A B) :=
  .iffI (.impI (checker_sound S T d A B hS.wk hT.wk Prf.hyp0))
    (.impI (checker_complete S T d A B Prf.hyp0))

theorem checker_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ checkerTerm (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        ((apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zero) ⋎
          (apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one))) :=
  closeUniv 5 (.andI (checker_at _ _ _ _ _) (checker_cases _ _ _ _ _))

theorem checker_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
        Fm.iff (apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one)
          (originalClose (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (checker_reflection _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

#print axioms checker_at
#print axioms checker_cases
#print axioms checker_sound
#print axioms checker_complete
#print axioms checker_reflection
#print axioms checker_program_closed
#print axioms checker_closed

end LeanProofs.IPRA.Analysis.RationalHausdorff
