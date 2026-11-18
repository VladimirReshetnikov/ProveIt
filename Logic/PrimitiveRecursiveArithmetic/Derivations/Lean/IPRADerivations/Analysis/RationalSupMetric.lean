import IPRADerivations.Foundations.FiniteHausdorff
import IPRADerivations.Foundations.GapDecision
import IPRADerivations.Probability.TowerCommonDen

/-!
# Coded rational vectors: the actual sup metric and common scale

Finite-demand packet `lem:aggregate-calculus`. A grid vector is an encoded
sequence of signed numerator pairs. At runtime dimension `d` and positive
common denominator `D`, the distance is `max_{i<d}|x_i-y_i| / D`.
The metric numerator below is an actual PR finite-maximum fold. All codes
are read by the total sequence decoder, without assumptions about canonical
sequence length; only the first `d` decoded coordinates are used.

The normalization adapter below starts from arbitrary finite rational
coordinate data. A rational coordinate stores its signed numerator pair and
the predecessor of its positive denominator. Products and actual integer
quotients produce a common scale; no divisibility or normalization equation
is a hypothesis.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalSupMetric

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.FiniteQueryDemand
  (finiteMaximum finiteMaximum_at subst_finiteMaximum)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (maximum_bound sum_mono)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_tri zabs_neg subst_zabs)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Decode the integer coordinate from the actual total sequence entry. -/
def coordinate (x i : PTm n) : ZT n := ⟨fstT (entry x i), sndT (entry x i)⟩
def coordinateDifference (x y i : PTm n) : ZT n := coordinate x i - coordinate y i
def coordinateDistance (x y i : PTm n) : PTm n := zabs (coordinateDifference x y i)

@[simp] theorem subst_coordinate {k : ℕ} (σ : Fin n → PTm k) (x i : PTm n) :
    (coordinate x i).subst σ = coordinate (Syn.subst σ x) (Syn.subst σ i) := by
  simp [coordinate, ZT.subst]
@[simp] theorem subst_coordinateDifference {k : ℕ} (σ : Fin n → PTm k) (x y i : PTm n) :
    (coordinateDifference x y i).subst σ = coordinateDifference (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ i) := by
  simp only [coordinateDifference, ZT.subst_sub, subst_coordinate]
@[simp] theorem subst_coordinateDistance {k : ℕ} (σ : Fin n → PTm k) (x y i : PTm n) :
    Syn.subst σ (coordinateDistance x y i) = coordinateDistance (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ i) := by
  simp only [coordinateDistance, subst_zabs, subst_coordinateDifference]

def distanceBody : PTm 2 := coordinateDistance (fstT (var 1)) (sndT (var 1)) (var 0)
def supDistance (x y d : PTm n) : PTm n := finiteMaximum distanceBody d (pairT x y)

@[simp] theorem subst_supDistance {k : ℕ} (σ : Fin n → PTm k) (x y d : PTm n) :
    Syn.subst σ (supDistance x y d) = supDistance (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ d) := by
  simp only [supDistance, subst_finiteMaximum, subst_pairT]

theorem distanceBody_at (x y i : PTm n) :
    Γ ⊢[PRAAx] inst2 distanceBody i (pairT x y) ≐ coordinateDistance x y i := by
  have h := Prf.eqCongr (Γ := Γ) (coordinateDistance (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT x y), sndT (pairT x y), i]) (σ' := ![x, y, i])
    (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact snd_pair _ _
      · exact .eqRefl _)
  simpa [inst2, distanceBody] using h

theorem coordinate_bound (x y d i : PTm n) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] le (coordinateDistance x y i) (supDistance x y d) :=
  le_congr (distanceBody_at x y i) (.eqRefl _) (finiteMaximum_at distanceBody hi)

theorem supDistance_bound (x y d r : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift d) ⟶
      le (coordinateDistance (Syn.shift x) (Syn.shift y) (var 0)) (Syn.shift r))) :
    Γ ⊢[PRAAx] le (supDistance x y d) r := by
  apply maximum_bound
  refine .allI (.impI ?_)
  have value := Prf.impE h.allOpen.wk Prf.hyp0
  simpa only [Syn.shift, subst_pairT] using
    le_congr (distanceBody_at (Syn.shift x) (Syn.shift y) (var 0)).eqSymm (.eqRefl _) value

theorem coordinate_diagonal (x i : PTm n) : Γ ⊢[PRAAx] coordinateDistance x x i ≐ zero := by
  have eq : Γ ⊢[PRAAx] coordinateDistance x x i ≐ zabs (ZT.natLit 0) := by
    apply zabs_congr
    simp only [coordinateDifference, ZT.toZ_sub, ZT.toZ_natLit]
    ring
  exact eq.eqTrans ((congrAdd (monus_self zero) (monus_self zero)).eqTrans (zero_add zero))

theorem coordinate_symmetry (x y i : PTm n) :
    Γ ⊢[PRAAx] coordinateDistance x y i ≐ coordinateDistance y x i := by
  have opposite : ZT.toZ Γ (coordinateDifference x y i) = ZT.toZ Γ (-(coordinateDifference y x i)) := by
    simp only [coordinateDifference, ZT.toZ_sub, ZT.toZ_neg]
    ring
  exact (zabs_congr opposite).eqTrans (zabs_neg _)

theorem coordinate_triangle (x y z i : PTm n) :
    Γ ⊢[PRAAx] le (coordinateDistance x z i) (coordinateDistance x y i + coordinateDistance y z i) := by
  apply zabs_tri
  simp only [coordinateDifference, ZT.toZ_sub]
  ring

theorem sup_diagonal (x d : PTm n) : Γ ⊢[PRAAx] supDistance x x d ≐ zero := by
  apply le_antisymm
  · apply supDistance_bound
    refine .allI (.impI ?_)
    simpa only [Syn.shift, ConciseIPRA.PTm.subst_zero] using
      le_congr (coordinate_diagonal (Γ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift) (Syn.shift x) (var 0)).eqSymm
        (.eqRefl _) (le_refl zero)
  · exact zero_le _

theorem sup_le_reverse (x y d : PTm n) : Γ ⊢[PRAAx] le (supDistance x y d) (supDistance y x d) := by
  apply supDistance_bound
  refine .allI (.impI ?_)
  have value := le_congr (coordinate_symmetry (Syn.shift x) (Syn.shift y) (var 0)).eqSymm (.eqRefl _)
    (coordinate_bound (Syn.shift y) (Syn.shift x) (Syn.shift d) (var 0)
      (Prf.hyp0 : lt (var 0) (Syn.shift d) :: Γ.map Fm.shift ⊢[PRAAx] _))
  simpa only [Syn.shift, subst_supDistance] using value

theorem sup_symmetry (x y d : PTm n) : Γ ⊢[PRAAx] supDistance x y d ≐ supDistance y x d :=
  le_antisymm (sup_le_reverse x y d) (sup_le_reverse y x d)

theorem sup_triangle (x y z d : PTm n) :
    Γ ⊢[PRAAx] le (supDistance x z d) (supDistance x y d + supDistance y z d) := by
  apply supDistance_bound
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have value : Δ ⊢[PRAAx] le (coordinateDistance (Syn.shift x) (Syn.shift z) (var 0))
      (supDistance (Syn.shift x) (Syn.shift y) (Syn.shift d) + supDistance (Syn.shift y) (Syn.shift z) (Syn.shift d)) :=
    le_trans (coordinate_triangle _ _ _ _) (sum_mono
      (coordinate_bound _ _ _ _ Prf.hyp0) (coordinate_bound _ _ _ _ Prf.hyp0))
  simpa only [Δ, Syn.shift, PTm.subst_add, subst_supDistance] using value

private theorem value_zero_of_abs (u : ZT n) (h : Γ ⊢[PRAAx] zabs u ≐ zero) :
    ZT.toZ Γ u = 0 := by
  have left : Γ ⊢[PRAAx] monus u.pos u.neg ≐ zero := le_antisymm
    (le_congr (.eqRefl _) h (le_add_right _ _)) (zero_le _)
  have right : Γ ⊢[PRAAx] monus u.neg u.pos ≐ zero := le_antisymm
    (le_congr (.eqRefl _) h (le_add_left _ _)) (zero_le _)
  have same := natEq (le_antisymm left right)
  simp only [ZT.toZ]
  rw [same]
  ring

/-- Zero distance identifies geometric coordinates, rather than their
potentially noncanonical natural-number encodings. -/
def sameCoordinates (x y d : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift d) ⟶ ZT.eq (coordinate (Syn.shift x) (var 0)) (coordinate (Syn.shift y) (var 0)))

theorem sup_zero_sound (x y d : PTm n) (h : Γ ⊢[PRAAx] supDistance x y d ≐ zero) :
    Γ ⊢[PRAAx] sameCoordinates x y d := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have zero : Δ ⊢[PRAAx] supDistance (Syn.shift x) (Syn.shift y) (Syn.shift d) ≐ ConciseIPRA.PTm.zero := by
    simpa only [Fm.shift, Fm.subst_eq, subst_supDistance, ConciseIPRA.PTm.subst_zero, Syn.shift] using h.shift.wk
  have absZero : Δ ⊢[PRAAx] coordinateDistance (Syn.shift x) (Syn.shift y) (var 0) ≐ ConciseIPRA.PTm.zero :=
    le_antisymm (le_congr (.eqRefl _) zero (coordinate_bound _ _ _ _ Prf.hyp0)) (zero_le _)
  apply ZT.derive
  have value := value_zero_of_abs (coordinateDifference (Syn.shift x) (Syn.shift y) (var 0)) absZero
  simp only [coordinateDifference, ZT.toZ_sub] at value
  linear_combination value

theorem sup_zero_complete (x y d : PTm n) (h : Γ ⊢[PRAAx] sameCoordinates x y d) :
    Γ ⊢[PRAAx] supDistance x y d ≐ zero := by
  apply le_antisymm
  · apply supDistance_bound
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
    have equal : Δ ⊢[PRAAx] ZT.eq (coordinate (Syn.shift x) (var 0)) (coordinate (Syn.shift y) (var 0)) :=
      .impE h.allOpen.wk Prf.hyp0
    have zero : Δ ⊢[PRAAx] coordinateDistance (Syn.shift x) (Syn.shift y) (var 0) ≐ ConciseIPRA.PTm.zero := by
      have value := ZT.toZ_eq equal
      have abs := zabs_congr (u := coordinateDifference (Syn.shift x) (Syn.shift y) (var 0))
        (v := ZT.natLit 0) (by simp only [coordinateDifference, ZT.toZ_sub, ZT.toZ_natLit]; rw [value]; ring)
      exact abs.eqTrans ((congrAdd (monus_self _) (monus_self _)).eqTrans (zero_add _))
    simpa only [Δ, Syn.shift, ConciseIPRA.PTm.subst_zero] using le_congr zero.eqSymm (.eqRefl _) (le_refl ConciseIPRA.PTm.zero)
  · exact zero_le _

/-- The parameter is `(runtime dimension, common rational denominator)`.
Only the numerator uses the dimension; rational interpretation requires the
separately supplied positivity of `sndT p`. -/
def metricF : PR 3 := PTm.toPR (supDistance (var 0) (var 1) (fstT (var 2)))

theorem metric_at (x y p : PTm n) :
    Γ ⊢[PRAAx] FiniteHausdorff.distance metricF x y p ≐ supDistance x y (fstT p) := by
  have h := toPR_eq (Γ := Γ) (supDistance (var 0) (var 1) (fstT (var 2)) : PTm 3) ![x, y, p]
  simpa [metricF, FiniteHausdorff.distance, ap3] using h

theorem metric_diagonal (x p : PTm n) : Γ ⊢[PRAAx] FiniteHausdorff.distance metricF x x p ≐ zero :=
  (metric_at x x p).eqTrans (sup_diagonal x (fstT p))

theorem metric_symmetry (x y p : PTm n) :
    Γ ⊢[PRAAx] FiniteHausdorff.distance metricF x y p ≐ FiniteHausdorff.distance metricF y x p :=
  (metric_at x y p).eqTrans ((sup_symmetry _ _ _).eqTrans (metric_at y x p).eqSymm)

theorem metric_triangle (x y z p : PTm n) :
    Γ ⊢[PRAAx] le (FiniteHausdorff.distance metricF x z p)
      (FiniteHausdorff.distance metricF x y p + FiniteHausdorff.distance metricF y z p) :=
  le_congr (metric_at x z p).eqSymm (congrAdd (metric_at x y p).eqSymm (metric_at y z p).eqSymm)
    (sup_triangle x y z (fstT p))

theorem metric_triangle_law (p : PTm n) : Γ ⊢[PRAAx] FiniteHausdorff.triangleLaw metricF p := by
  refine .allI (.allI (.allI ?_))
  exact metric_triangle _ _ _ _

theorem metric_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((FiniteHausdorff.distance metricF (var 0) (var 0) (var 3) ≐ zero) ⋏
      ((FiniteHausdorff.distance metricF (var 0) (var 1) (var 3) ≐ FiniteHausdorff.distance metricF (var 1) (var 0) (var 3)) ⋏
        le (FiniteHausdorff.distance metricF (var 0) (var 2) (var 3))
          (FiniteHausdorff.distance metricF (var 0) (var 1) (var 3) + FiniteHausdorff.distance metricF (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.andI (metric_diagonal _ _) (.andI (metric_symmetry _ _ _) (metric_triangle _ _ _ _)))

/-- The actual rational-vector metric discharges the finite Hausdorff
triangle contract; there is no metric-law hypothesis. -/
theorem hausdorff_triangle (S T U p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hU : Γ ⊢[PRAAx] le one (length U)) :
    Γ ⊢[PRAAx] le (FiniteHausdorff.hausdorff metricF S U p)
      (FiniteHausdorff.hausdorff metricF S T p + FiniteHausdorff.hausdorff metricF T U p) :=
  FiniteHausdorff.hausdorff_triangle metricF S T U p hS hT hU (metric_triangle_law p)

#print axioms sup_diagonal
#print axioms sup_symmetry
#print axioms sup_triangle
#print axioms metric_closed
#print axioms hausdorff_triangle

/-! ## Arbitrary rational coordinate data and a computed common denominator -/

def numeratorOf (c : PTm n) : ZT n := ⟨fstT (fstT c), sndT (fstT c)⟩
def denominatorOf (c : PTm n) : PTm n := succ (sndT c)
def rationalNumerator (v i : PTm n) : ZT n := numeratorOf (entry v i)
def rationalDenominator (v i : PTm n) : PTm n := denominatorOf (entry v i)

@[simp] theorem subst_numeratorOf {k : ℕ} (σ : Fin n → PTm k) (c : PTm n) :
    (numeratorOf c).subst σ = numeratorOf (Syn.subst σ c) := by simp [numeratorOf, ZT.subst]
@[simp] theorem subst_denominatorOf {k : ℕ} (σ : Fin n → PTm k) (c : PTm n) :
    Syn.subst σ (denominatorOf c) = denominatorOf (Syn.subst σ c) := by simp [denominatorOf]
@[simp] theorem subst_rationalNumerator {k : ℕ} (σ : Fin n → PTm k) (v i : PTm n) :
    (rationalNumerator v i).subst σ = rationalNumerator (Syn.subst σ v) (Syn.subst σ i) := by
  simp only [rationalNumerator, subst_numeratorOf, MasterCertificate.subst_entry]
@[simp] theorem subst_rationalDenominator {k : ℕ} (σ : Fin n → PTm k) (v i : PTm n) :
    Syn.subst σ (rationalDenominator v i) = rationalDenominator (Syn.subst σ v) (Syn.subst σ i) := by
  simp only [rationalDenominator, subst_denominatorOf, MasterCertificate.subst_entry]

/-- Every signed numerator and every positive denominator can be encoded. -/
def rationalCode (a : ZT n) (b : PTm n) : PTm n := pairT (pairT a.pos a.neg) (pred b)

theorem rationalCode_numerator (a : ZT n) (b : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (numeratorOf (rationalCode a b)) a := by
  apply ZT.derive
  have hp := natEq ((congrFst (fst_pair (Γ := Γ) (pairT a.pos a.neg) (pred b))).eqTrans (fst_pair a.pos a.neg))
  have hn := natEq ((congrSnd (fst_pair (Γ := Γ) (pairT a.pos a.neg) (pred b))).eqTrans (snd_pair a.pos a.neg))
  simp only [numeratorOf, rationalCode, ZT.toZ]
  rw [hp, hn]

theorem rationalCode_denominator (a : ZT n) (b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] denominatorOf (rationalCode a b) ≐ b :=
  (congrSucc (snd_pair _ _)).eqTrans (FiniteHausdorff.positive_length hb).eqSymm

def denominatorBody : PTm 2 := rationalDenominator (var 1) (var 0)
def rowDenominator (v d : PTm n) : PTm n := ap2 (prodF denominatorBody) d v
def denominatorRows : PTm 2 := rowDenominator (entry (sndT (var 1)) (var 0)) (fstT (var 1))
def commonDenominator (P d : PTm n) : PTm n := ap2 (prodF denominatorRows) (length P) (pairT d P)

@[simp] theorem subst_rowDenominator {k : ℕ} (σ : Fin n → PTm k) (v d : PTm n) :
    Syn.subst σ (rowDenominator v d) = rowDenominator (Syn.subst σ v) (Syn.subst σ d) := by simp [rowDenominator]
@[simp] theorem subst_commonDenominator {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (commonDenominator P d) = commonDenominator (Syn.subst σ P) (Syn.subst σ d) := by
  simp only [commonDenominator, subst_ap2, SequenceComposition.subst_length, subst_pairT]

theorem denominatorBody_at (v i : PTm n) : inst2 denominatorBody i v = rationalDenominator v i := by
  simp [denominatorBody, inst2]

theorem denominatorBody_positive (v i : PTm n) :
    Γ ⊢[PRAAx] inst2 denominatorBody i v ≐ succ (pred (inst2 denominatorBody i v)) := by
  rw [denominatorBody_at]
  exact pos_of_eq_succ (.eqRefl _)

theorem rowDenominator_positive (v d : PTm n) :
    Γ ⊢[PRAAx] rowDenominator v d ≐ succ (pred (rowDenominator v d)) := by
  apply prod_pos_bounded
  exact .allI (.impI (denominatorBody_positive _ _))

theorem denominatorRows_at (P d j : PTm n) :
    Γ ⊢[PRAAx] inst2 denominatorRows j (pairT d P) ≐ rowDenominator (entry P j) d := by
  simp only [denominatorRows, inst2, subst_rowDenominator, MasterCertificate.subst_entry,
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact congrAp2 (prodF denominatorBody) (fst_pair _ _) (entry_congr (snd_pair _ _) (.eqRefl _))

theorem denominatorRows_positive (data j : PTm n) :
    Γ ⊢[PRAAx] inst2 denominatorRows j data ≐ succ (pred (inst2 denominatorRows j data)) := by
  simpa [denominatorRows, inst2] using rowDenominator_positive (Γ := Γ) (entry (sndT data) j) (fstT data)

theorem commonDenominator_positive (P d : PTm n) :
    Γ ⊢[PRAAx] commonDenominator P d ≐ succ (pred (commonDenominator P d)) := by
  apply prod_pos_bounded
  exact .allI (.impI (denominatorRows_positive _ _))

theorem commonDenominator_one_le (P d : PTm n) : Γ ⊢[PRAAx] le one (commonDenominator P d) :=
  le_congr (.eqRefl _) (commonDenominator_positive P d).eqSymm
    ((succ_monus_succ zero _).eqTrans (zero_le _))

theorem inner_quotient_clears (v d i : PTm n) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] rowDenominator v d ≐ rationalDenominator v i * quo (rowDenominator v d) (rationalDenominator v i) := by
  have hd := Probability.TowerCommonDen.dvd_prod_term denominatorBody
    (x := v) (M := d) (i := i) (denominatorBody_positive _ _) hi
  simpa only [denominatorBody_at, rowDenominator] using
    DiophantineNumberTheory.Coprime.eq_of_dvd' (denominatorBody_positive v i) hd

theorem outer_quotient_clears (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P)) :
    Γ ⊢[PRAAx] commonDenominator P d ≐ rowDenominator (entry P j) d *
      quo (commonDenominator P d) (rowDenominator (entry P j) d) := by
  have hd := Probability.TowerCommonDen.dvd_prod_term denominatorRows
    (x := pairT d P) (M := length P) (i := j) (denominatorRows_positive _ _) hj
  have e := DiophantineNumberTheory.Coprime.eq_of_dvd' (denominatorRows_positive (pairT d P) j) hd
  exact e.eqTrans (congrMul (denominatorRows_at P d j)
    (congrAp2 quoF (.eqRefl _) (denominatorRows_at P d j)))

/-- Actual two-stage integer quotient multiplier for each input coordinate. -/
def cofactor (P d j i : PTm n) : PTm n :=
  quo (commonDenominator P d) (rowDenominator (entry P j) d) *
    quo (rowDenominator (entry P j) d) (rationalDenominator (entry P j) i)

@[simp] theorem subst_cofactor {k : ℕ} (σ : Fin n → PTm k) (P d j i : PTm n) :
    Syn.subst σ (cofactor P d j i) = cofactor (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ j) (Syn.subst σ i) := by
  simp [cofactor]

theorem cofactor_clears (P d j i : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length P)) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] rationalDenominator (entry P j) i * cofactor P d j i ≐ commonDenominator P d := by
  have inner := natEq (inner_quotient_clears (entry P j) d i hi)
  have outer := natEq (outer_quotient_clears P d j hj)
  unfold cofactor
  apply deriveNat
  ipra_simps
  linear_combination -outer +
    -(Groth.ι (Q.mk Γ (quo (commonDenominator P d) (rowDenominator (entry P j) d)))) * inner

#print axioms rationalCode_denominator
#print axioms commonDenominator_one_le
#print axioms cofactor_clears

/-! ## Actual normalized vectors and finite point lists -/

def normalizedCoordinateCode (P d j i : PTm n) : PTm n :=
  pairT ((rationalNumerator (entry P j) i).pos * cofactor P d j i)
    ((rationalNumerator (entry P j) i).neg * cofactor P d j i)

@[simp] theorem subst_normalizedCoordinateCode {k : ℕ} (σ : Fin n → PTm k) (P d j i : PTm n) :
    Syn.subst σ (normalizedCoordinateCode P d j i) = normalizedCoordinateCode
      (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ j) (Syn.subst σ i) := by
  simp [normalizedCoordinateCode, rationalNumerator, numeratorOf]

def normalizedCoordinateBody : PTm 2 := normalizedCoordinateCode (fstT (var 1))
  (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def normalizedVector (P d j : PTm n) : PTm n :=
  sequence normalizedCoordinateBody d (pairT P (pairT d j))

@[simp] theorem subst_normalizedVector {k : ℕ} (σ : Fin n → PTm k) (P d j : PTm n) :
    Syn.subst σ (normalizedVector P d j) = normalizedVector (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ j) := by
  simp [normalizedVector]

def normalizedVectorBody : PTm 2 := normalizedVector (fstT (var 1)) (sndT (var 1)) (var 0)
def normalizedList (P d : PTm n) : PTm n := sequence normalizedVectorBody (length P) (pairT P d)

@[simp] theorem subst_normalizedList {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (normalizedList P d) = normalizedList (Syn.subst σ P) (Syn.subst σ d) := by
  simp [normalizedList]

theorem normalizedCoordinateBody_at (P d j i : PTm n) :
    Γ ⊢[PRAAx] inst2 normalizedCoordinateBody i (pairT P (pairT d j)) ≐ normalizedCoordinateCode P d j i := by
  have h := Prf.eqCongr (Γ := Γ) (normalizedCoordinateCode (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (pairT P (pairT d j)), fstT (sndT (pairT P (pairT d j))),
      sndT (sndT (pairT P (pairT d j))), i]) (σ' := ![P, d, j, i])
    (fun k => by
      fin_cases k
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa [inst2, normalizedCoordinateBody] using h

theorem normalizedVectorBody_at (P d j : PTm n) :
    Γ ⊢[PRAAx] inst2 normalizedVectorBody j (pairT P d) ≐ normalizedVector P d j := by
  have h := Prf.eqCongr (Γ := Γ) (normalizedVector (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT P d), sndT (pairT P d), j]) (σ' := ![P, d, j])
    (fun k => by
      fin_cases k
      · exact fst_pair _ _
      · exact snd_pair _ _
      · exact .eqRefl _)
  simpa [inst2, normalizedVectorBody] using h

theorem normalizedVector_length (P d j : PTm n) : Γ ⊢[PRAAx] length (normalizedVector P d j) ≐ d :=
  MasterCertificate.sequence_length _ _ _
theorem normalizedList_length (P d : PTm n) : Γ ⊢[PRAAx] length (normalizedList P d) ≐ length P :=
  MasterCertificate.sequence_length _ _ _

theorem normalizedVector_lookup (P d j i : PTm n) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] entry (normalizedVector P d j) i ≐ normalizedCoordinateCode P d j i :=
  (sequence_decode normalizedCoordinateBody hi).eqTrans (normalizedCoordinateBody_at P d j i)

theorem normalizedList_lookup (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P)) :
    Γ ⊢[PRAAx] entry (normalizedList P d) j ≐ normalizedVector P d j :=
  (sequence_decode normalizedVectorBody hj).eqTrans (normalizedVectorBody_at P d j)

theorem normalized_lookup (P d j i : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length P)) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] entry (entry (normalizedList P d) j) i ≐ normalizedCoordinateCode P d j i :=
  (entry_congr (normalizedList_lookup P d j hj) (.eqRefl _)).eqTrans (normalizedVector_lookup P d j i hi)

/-- The actual decoded normalized coordinate has the computed scaled value. -/
theorem normalized_coordinate_value (P d j i : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length P)) (hi : Γ ⊢[PRAAx] lt i d) :
    ZT.toZ Γ (coordinate (entry (normalizedList P d) j) i) =
      ZT.toZ Γ (rationalNumerator (entry P j) i * ZT.ofNat (cofactor P d j i)) := by
  have code := normalized_lookup P d j i hj hi
  have hp : Γ ⊢[PRAAx] fstT (entry (entry (normalizedList P d) j) i) ≐
      (rationalNumerator (entry P j) i).pos * cofactor P d j i :=
    (congrFst code).eqTrans (fst_pair _ _)
  have hn : Γ ⊢[PRAAx] sndT (entry (entry (normalizedList P d) j) i) ≐
      (rationalNumerator (entry P j) i).neg * cofactor P d j i :=
    (congrSnd code).eqTrans (snd_pair _ _)
  rw [ZT.toZ_mul, ZT.toZ_ofNat]
  simp only [coordinate, ZT.toZ]
  rw [natEq hp, natEq hn]
  simp only [Q.mk_mul, map_mul]
  ring

/-- Every arbitrary input rational coordinate is preserved at the computed
positive common scale. No common-denominator correctness is a premise. -/
theorem normalized_coordinate (P d j i : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length P)) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (rationalDenominator (entry P j) i) * coordinate (entry (normalizedList P d) j) i)
      (ZT.ofNat (commonDenominator P d) * rationalNumerator (entry P j) i) := by
  have factor := natEq (cofactor_clears P d j i hj hi)
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_ofNat]
  rw [normalized_coordinate_value P d j i hj hi]
  simp only [ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at factor ⊢
  linear_combination (ZT.toZ Γ (rationalNumerator (entry P j) i)) * factor

/-- Coordinate differences have exactly the original rational cross value,
uniformly for any two input points and any runtime coordinate. -/
theorem normalized_difference (P d j k i : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length P)) (hk : Γ ⊢[PRAAx] lt k (length P)) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (rationalDenominator (entry P j) i * rationalDenominator (entry P k) i) *
        coordinateDifference (entry (normalizedList P d) j) (entry (normalizedList P d) k) i)
      (ZT.ofNat (commonDenominator P d) *
        (rationalNumerator (entry P j) i * ZT.ofNat (rationalDenominator (entry P k) i) -
          rationalNumerator (entry P k) i * ZT.ofNat (rationalDenominator (entry P j) i))) := by
  have a := ZT.toZ_eq (normalized_coordinate P d j i hj hi)
  have b := ZT.toZ_eq (normalized_coordinate P d k i hk hi)
  apply ZT.derive
  simp only [coordinateDifference, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at a b ⊢
  linear_combination (Groth.ι (Q.mk Γ (rationalDenominator (entry P k) i))) * a -
    (Groth.ι (Q.mk Γ (rationalDenominator (entry P j) i))) * b

def metricData (P d : PTm n) : PTm n := pairT d (commonDenominator P d)

theorem metricData_positive (P d : PTm n) : Γ ⊢[PRAAx] le one (sndT (metricData P d)) :=
  le_congr (.eqRefl _) (snd_pair _ _).eqSymm (commonDenominator_one_le P d)

theorem metricData_distance (P d x y : PTm n) :
    Γ ⊢[PRAAx] FiniteHausdorff.distance metricF x y (metricData P d) ≐ supDistance x y d :=
  (metric_at x y (metricData P d)).eqTrans
    (congrAp2 (FiniteQueryDemand.maximumF distanceBody) (fst_pair _ _) (.eqRefl _))

#print axioms normalizedList_lookup
#print axioms normalized_coordinate
#print axioms normalized_difference
#print axioms metricData_positive

/-! ## Uniform fixed PR normalization symbols and closed adapter endpoints -/

def commonDenominatorF : PR 2 := PTm.toPR (commonDenominator (var 0) (var 1))
def normalizeF : PR 2 := PTm.toPR (normalizedList (var 0) (var 1))
def metricDataF : PR 2 := PTm.toPR (metricData (var 0) (var 1))

@[simp] theorem subst_metricData {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (metricData P d) = metricData (Syn.subst σ P) (Syn.subst σ d) := by simp [metricData]

theorem commonDenominator_at (P d : PTm n) :
    Γ ⊢[PRAAx] ap2 commonDenominatorF P d ≐ commonDenominator P d := by
  have h := toPR_eq (Γ := Γ) (commonDenominator (var 0) (var 1) : PTm 2) ![P, d]
  simpa [commonDenominatorF, ap2] using h
theorem normalize_at (P d : PTm n) : Γ ⊢[PRAAx] ap2 normalizeF P d ≐ normalizedList P d := by
  have h := toPR_eq (Γ := Γ) (normalizedList (var 0) (var 1) : PTm 2) ![P, d]
  simpa [normalizeF, ap2] using h
theorem metricData_at (P d : PTm n) : Γ ⊢[PRAAx] ap2 metricDataF P d ≐ metricData P d := by
  have h := toPR_eq (Γ := Γ) (metricData (var 0) (var 1) : PTm 2) ![P, d]
  simpa [metricDataF, ap2] using h

theorem normalization_programs_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((ap2 commonDenominatorF (var 0) (var 1) ≐ commonDenominator (var 0) (var 1)) ⋏
      ((ap2 normalizeF (var 0) (var 1) ≐ normalizedList (var 0) (var 1)) ⋏
        (ap2 metricDataF (var 0) (var 1) ≐ metricData (var 0) (var 1)))) :=
  closeUniv 2 (.andI (commonDenominator_at _ _) (.andI (normalize_at _ _) (metricData_at _ _)))

def normalizationFormula : Fm PTm 4 :=
  (le one (commonDenominator (var 0) (var 1))) ⋏
    ((length (normalizedList (var 0) (var 1)) ≐ length (var 0)) ⋏
    (lt (var 2) (length (var 0)) ⟶ lt (var 3) (var 1) ⟶
      ZT.eq (ZT.ofNat (rationalDenominator (entry (var 0) (var 2)) (var 3)) *
        coordinate (entry (normalizedList (var 0) (var 1)) (var 2)) (var 3))
        (ZT.ofNat (commonDenominator (var 0) (var 1)) * rationalNumerator (entry (var 0) (var 2)) (var 3))))

theorem normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 normalizationFormula :=
  closeUniv 4 (.andI (commonDenominator_one_le _ _) (.andI (normalizedList_length _ _)
    (.impI (.impI (normalized_coordinate _ _ _ _ Prf.hyp1 Prf.hyp0)))))

theorem metric_separation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (Fm.iff (supDistance (var 0) (var 1) (var 2) ≐ zero) (sameCoordinates (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.iffI (.impI (sup_zero_sound _ _ _ Prf.hyp0)) (.impI (sup_zero_complete _ _ _ Prf.hyp0)))

theorem rational_hausdorff_triangle_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (length (var 2)) ⟶
        le (FiniteHausdorff.hausdorff metricF (var 0) (var 2) (var 3))
          (FiniteHausdorff.hausdorff metricF (var 0) (var 1) (var 3) +
            FiniteHausdorff.hausdorff metricF (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (hausdorff_triangle _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

#print axioms sup_zero_sound
#print axioms sup_zero_complete
#print axioms normalization_programs_closed
#print axioms normalization_closed
#print axioms metric_separation_closed
#print axioms rational_hausdorff_triangle_closed

end LeanProofs.IPRA.Analysis.RationalSupMetric
