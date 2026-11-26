import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalCubeMinimum

/-!
# Actual numerical cube midpoints

The coordinate producer uses original decoded denominators and positive
numerator parts. On the source cube it is proved literally equal to the
canonical signed rational midpoint. The actual sequence has numerical
length d, is canonically presented and remains in the cube.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeMidpoint

open_ipra
open RationalSupMetric (numeratorOf denominatorOf)
open RationalCubeGrid (interval cube)
open RationalCubeMinimum (presentedCube)
open RationalIntegerNormalization (normalize positivePart)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters (midpoint)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def fraction (P D : PTm n) : PTm n := normalize (ZT.ofNat P) D
def numerator (q r : PTm n) : PTm n := positivePart (numeratorOf q)*denominatorOf r+positivePart (numeratorOf r)*denominatorOf q
def denominator (q r : PTm n) : PTm n := two*denominatorOf q*denominatorOf r
def coordinate (q r : PTm n) : PTm n := fraction (numerator q r) (denominator q r)
def body : PTm 2 := coordinate (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0))
def point (d y z : PTm n) : PTm n := sequence body d (pairT y z)

ipra_subst fraction
ipra_subst numerator
ipra_subst denominator [two, one]
ipra_subst coordinate
ipra_subst point

theorem fraction_represents (P D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fraction P D) (ZT.ofNat P) D := RationalIntegerNormalization.normalize_preserves_value _ _ hD
theorem fraction_negative_zero (P D : PTm n) : Γ ⊢[PRAAx] (numeratorOf (fraction P D)).neg ≐ zero := by
  have e := Prf.andE₂ (RationalNormalForm.code_parts (Γ := Γ)
    (RationalIntegerNormalization.reducedNumerator (ZT.ofNat P) D) (RationalIntegerNormalization.reducedDenominator (ZT.ofNat P) D))
  exact e.eqTrans ((congrAp2 quoF (zero_monus P) (.eqRefl _)).eqTrans (quo_zero _))
theorem fraction_interval (P D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hP : Γ ⊢[PRAAx] le P D) : Γ ⊢[PRAAx] interval (fraction P D) := by
  have hn := fraction_negative_zero (Γ := Γ) P D
  have clear : Γ ⊢[PRAAx] D*(numeratorOf (fraction P D)).pos ≐ P*denominatorOf (fraction P D) := by
    have e := ZT.toZ_eq (fraction_represents P D hD)
    have z := natEq hn
    apply deriveNat
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e
    simp only [ZT.toZ] at e
    ipra_simps
    linear_combination -e+𝔞(D)*z
  have upper : Γ ⊢[PRAAx] le (numeratorOf (fraction P D)).pos (denominatorOf (fraction P D)) :=
    RationalValueBounds.positive_cancel hD
      (le_congr clear.eqSymm (.eqRefl _) (mul_le_mul_right (denominatorOf (fraction P D)) hP))
  exact .andI (le_congr hn.eqSymm (.eqRefl _) (zero_le _))
    (le_congr (.eqRefl _) ((congrAdd hn (.eqRefl _)).eqTrans (zero_add _)).eqSymm upper)

theorem denominator_positive (q r : PTm n) : Γ ⊢[PRAAx] le one (denominator q r) :=
  RationalAlgebra.positive_product (RationalAlgebra.positive_product (le_of_eq_add (d := one) (by ipra_ring))
    (RationalArgmin.denominator_positive q)) (RationalArgmin.denominator_positive r)
theorem coordinate_canonical (q r : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (coordinate q r) :=
  RationalNormalForm.normalize_well_formed _ _ (denominator_positive q r)
theorem numerator_bound (q r : PTm n) (hq : Γ ⊢[PRAAx] interval q) (hr : Γ ⊢[PRAAx] interval r) :
    Γ ⊢[PRAAx] le (numerator q r) (denominator q r) :=
  le_congr (.eqRefl _) (by unfold denominator; ipra_ring)
    (Foundations.FiniteHausdorff.sum_mono
      (mul_le_mul_right (denominatorOf r) (RationalCubeGrid.positive_part_bound q hq))
      (mul_le_mul_right (denominatorOf q) (RationalCubeGrid.positive_part_bound r hr)))
theorem coordinate_interval (q r : PTm n) (hq : Γ ⊢[PRAAx] interval q) (hr : Γ ⊢[PRAAx] interval r) :
    Γ ⊢[PRAAx] interval (coordinate q r) := fraction_interval _ _ (denominator_positive q r) (numerator_bound q r hq hr)

theorem nonnegative_numerator (q : PTm n) (hq : Γ ⊢[PRAAx] interval q) : Γ ⊢[PRAAx]
    ZT.eq (numeratorOf q) (ZT.ofNat (positivePart (numeratorOf q))) := by
  have e := natEq (eq_add_of_le (.andE₁ hq))
  apply ZT.derive
  rw [ZT.toZ_ofNat]
  simp only [ZT.toZ,positivePart]
  ipra_simps
  linear_combination e

/-- On original cube coordinates, the returned code is the true signed mean. -/
theorem coordinate_midpoint (q r : PTm n) (hq : Γ ⊢[PRAAx] interval q) (hr : Γ ⊢[PRAAx] interval r) :
    Γ ⊢[PRAAx] coordinate q r ≐ midpoint q r := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (coordinate_canonical q r)
    (RationalNormalForm.normalize_well_formed _ _ (LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters.midpoint_denominator_positive q r))
    (fraction_represents _ _ (denominator_positive q r)) (RationalAlgebra.midpoint_value q r)
    (denominator_positive q r)
    (RationalAlgebra.positive_product (le_of_eq_add (d := one) (by ipra_ring)) (RationalArithmetic.product_denominator_positive q r))
  have eq := ZT.toZ_eq (nonnegative_numerator q hq)
  have er := ZT.toZ_eq (nonnegative_numerator r hr)
  apply ZT.derive
  simp only [numerator,denominator,RationalArithmetic.addNumerator,RationalArithmetic.productDenominator,
    ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at eq er ⊢
  simp only [ZT.toZ] at eq er ⊢
  ipra_simps
  linear_combination -(2*𝔞(denominatorOf q)*𝔞(denominatorOf r))*(𝔞(denominatorOf r)*eq+𝔞(denominatorOf q)*er)

theorem coordinate_congr {q q' r r' : PTm n} (hq : Γ ⊢[PRAAx] q ≐ q') (hr : Γ ⊢[PRAAx] r ≐ r') :
    Γ ⊢[PRAAx] coordinate q r ≐ coordinate q' r' := by
  ipra_congr (coordinate (var 0) (var 1) : PTm 2) with [hq, hr]

theorem point_length (d y z : PTm n) : Γ ⊢[PRAAx] length (point d y z) ≐ d := Foundations.MasterCertificate.sequence_length _ _ _
theorem point_lookup (d y z i : PTm n) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    entry (point d y z) i ≐ coordinate (entry y i) (entry z i) := by
  refine (sequence_decode (Γ := Γ) body (x := pairT y z) hi).eqTrans ?_
  simp only [body,inst2,subst_coordinate,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact coordinate_congr (Foundations.SequenceComposition.entry_congr (fst_pair _ _) (.eqRefl _))
    (Foundations.SequenceComposition.entry_congr (snd_pair _ _) (.eqRefl _))

theorem point_cube (d y z : PTm n) (hy : Γ ⊢[PRAAx] cube y d) (hz : Γ ⊢[PRAAx] cube z d) : Γ ⊢[PRAAx] cube (point d y z) d := by
  refine .andI (point_length d y z) (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have a : Δ ⊢[PRAAx] cube (Syn.shift y) (Syn.shift d) := by simpa only [Fm.shift,RationalCubeGrid.subst_cube,Syn.shift] using hy.shift.wk
  have b : Δ ⊢[PRAAx] cube (Syn.shift z) (Syn.shift d) := by simpa only [Fm.shift,RationalCubeGrid.subst_cube,Syn.shift] using hz.shift.wk
  simpa only [Δ,Syn.shift,subst_point] using RationalCubeGrid.interval_congr
    (point_lookup (Syn.shift d) (Syn.shift y) (Syn.shift z) (var 0) Prf.hyp0).eqSymm
    (coordinate_interval _ _ (RationalCubeGrid.cube_at _ _ _ a Prf.hyp0) (RationalCubeGrid.cube_at _ _ _ b Prf.hyp0))

theorem point_presented (d y z : PTm n) (hy : Γ ⊢[PRAAx] presentedCube y d) (hz : Γ ⊢[PRAAx] presentedCube z d) :
    Γ ⊢[PRAAx] presentedCube (point d y z) d := by
  refine .andI (point_cube d y z (.andE₁ hy) (.andE₁ hz)) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_point] using RationalCubeMinimum.well_formed_congr
    (point_lookup (Syn.shift d) (Syn.shift y) (Syn.shift z) (var 0) Prf.hyp0).eqSymm (coordinate_canonical _ _)

theorem point_midpoint_at (d y z i : PTm n) (hy : Γ ⊢[PRAAx] cube y d) (hz : Γ ⊢[PRAAx] cube z d)
    (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx] entry (point d y z) i ≐ midpoint (entry y i) (entry z i) :=
  (point_lookup d y z i hi).eqTrans (coordinate_midpoint _ _ (RationalCubeGrid.cube_at _ _ _ hy hi) (RationalCubeGrid.cube_at _ _ _ hz hi))


def outputF : PR 3 := PTm.toPR (point (var 0) (var 1) (var 2))
def run (d y z : PTm n) : PTm n := app outputF ![d,y,z]
ipra_subst run

theorem program_at (d y z : PTm n) : Γ ⊢[PRAAx] run d y z ≐ point d y z := by
  simpa [run,outputF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using toPR_eq (Γ := Γ) (point (var 0) (var 1) (var 2) : PTm 3) ![d,y,z]
theorem returned_length (d y z : PTm n) : Γ ⊢[PRAAx] length (run d y z) ≐ d :=
  (congrFst (program_at d y z)).eqTrans (point_length d y z)
theorem returned_midpoint_at (d y z i : PTm n) (hy : Γ ⊢[PRAAx] cube y d) (hz : Γ ⊢[PRAAx] cube z d)
    (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx] entry (run d y z) i ≐ midpoint (entry y i) (entry z i) :=
  (Foundations.SequenceComposition.entry_congr (program_at d y z) (.eqRefl _)).eqTrans (point_midpoint_at d y z i hy hz hi)
theorem returned_presented (d y z : PTm n) (hy : Γ ⊢[PRAAx] presentedCube y d) (hz : Γ ⊢[PRAAx] presentedCube z d) :
    Γ ⊢[PRAAx] presentedCube (run d y z) d := by
  have proof := Prf.eqSubst (Γ := Γ) (presentedCube (var 0) (var 1) : Fm PTm 2)
    ![point d y z,d] ![run d y z,d] (fun i => by fin_cases i; exact (program_at d y z).eqSymm; exact .eqRefl _)
    (by simpa using point_presented (Γ := Γ) d y z hy hz)
  simpa using proof

theorem actual_positive_fraction_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶ interval (fraction (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (fraction_interval (var 0) (var 1) Prf.hyp1 Prf.hyp0)))
theorem actual_scalar_cube_midpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (interval (var 0) ⟶ interval (var 1) ⟶ coordinate (var 0) (var 1) ≐ midpoint (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (coordinate_midpoint (var 0) (var 1) Prf.hyp1 Prf.hyp0)))
theorem actual_cube_midpoint_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (point (var 0) (var 1) (var 2)) ≐ var 0) := closeUniv 3 (point_length (var 0) (var 1) (var 2))
theorem actual_cube_midpoint_coordinates_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (cube (var 1) (var 0) ⟶ cube (var 2) (var 0) ⟶ lt (var 3) (var 0) ⟶
      entry (point (var 0) (var 1) (var 2)) (var 3) ≐ midpoint (entry (var 1) (var 3)) (entry (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (point_midpoint_at (var 0) (var 1) (var 2) (var 3) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_cube_midpoint_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (presentedCube (var 1) (var 0) ⟶ presentedCube (var 2) (var 0) ⟶ presentedCube (point (var 0) (var 1) (var 2)) (var 0)) :=
  closeUniv 3 (.impI (.impI (point_presented (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0)))
theorem actual_cube_midpoint_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ point (var 0) (var 1) (var 2)) := closeUniv 3 (program_at (var 0) (var 1) (var 2))
theorem actual_returned_cube_midpoint_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (presentedCube (var 1) (var 0) ⟶ presentedCube (var 2) (var 0) ⟶ presentedCube (run (var 0) (var 1) (var 2)) (var 0)) :=
  closeUniv 3 (.impI (.impI (returned_presented (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalCubeMidpoint
