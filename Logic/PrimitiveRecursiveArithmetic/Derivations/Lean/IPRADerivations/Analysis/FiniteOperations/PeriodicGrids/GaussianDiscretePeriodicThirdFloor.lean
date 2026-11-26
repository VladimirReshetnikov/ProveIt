import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianDiscretePeriodicDerivativeSchedule
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantPairAlgebra

/-!
# Signed floor from the actual third derivative's real coordinates

On a lattice with denominator L*(2D+1), a real lower bound of
-1/(3L) on each actual third derivative observation pays the
rounded signed floor - (2D+1), provided D is positive. This leaves
the analytic derivative sign and decay as explicit input certificates.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicThirdFloor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDiscretePeriodicDerivativeSchedule (padding)
open GaussianDiscreteDerivativeRounding (body latticeScale sample_at)
open SignedDiscreteDerivativeOperators (divisor subst_divisor)
open SignedDiscreteDerivativeBounds (floorOn)
open GaussianSignedObservationGrid (rounded)
open GaussianSignedObservationOrder (lower)
open GaussianRationalHorner (qzero zero_represents positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_represents)
open ComplexLogarithmRemainder (re zeroCode)
open GaussianRootAlgebra (equal_re re_scale re_zero)
open RationalValueBounds (upper upper_mono)
open SignedGridStepBounds (neg_order)
open PolynomialBisection (zle_congr zle_trans)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem rounded_zero (S : PTm n) :
    ZT.toZ Γ (rounded qzero S) = 0 := by
  let z : PTm n := qzero
  let a := re (rawGaussian z)
  have value := equal_re (GaussianDominantPairAlgebra.represents_cross (Γ := Γ)
    z (rawGaussian z) zeroCode (rawDen z) one (raw_represents z) (zero_represents one))
  have vanish : ZT.toZ Γ a = 0 := by
    simp only [re_scale,re_zero,Q.mk_one,map_one] at value
    change ZT.toZ Γ (re (rawGaussian z)) = 0
    linear_combination value
  have eq : Γ ⊢[PRAAx] a.pos ≐ a.neg := by
    apply deriveNat
    simp only [ZT.toZ] at vanish
    linear_combination vanish
  have rounding : Γ ⊢[PRAAx] quo (S*a.pos) (rawDen z) ≐ quo (S*a.neg) (rawDen z) :=
    congrAp2 quoF (congrMul (.eqRefl _) eq) (.eqRefl _)
  change Groth.ι (IPRA.Q.mk Γ (quo (S*a.pos) (rawDen z))) -
      Groth.ι (IPRA.Q.mk Γ (quo (S*a.neg) (rawDen z))) = 0
  rw [natEq rounding]
  ring

theorem rounded_floor (q S E : PTm n) (h : Γ ⊢[PRAAx] upper (fstT (qzero : PTm n)) (fstT q) E S) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (E+two)) (rounded q S) :=
  zle_congr rfl (by rw [ZT.toZ_sub,rounded_zero]; ring) (lower q qzero S E h)

theorem floor_at (q D L S : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hL : Γ ⊢[PRAAx] le one L) (hS : Γ ⊢[PRAAx] S ≐ L*padding D)
    (h : Γ ⊢[PRAAx] upper (fstT (qzero : PTm n)) (fstT q) one (num 3*L)) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (padding D)) (rounded q S) := by
  have hThree : Γ ⊢[PRAAx] le one (num 3 : PTm n) := le_of_eq_add (d := two) (by ipra_ring)
  have pay : Γ ⊢[PRAAx] le (padding D) (num 3*D) :=
    le_congr (by unfold padding; ipra_ring) (by ipra_ring) (add_le_add_right (two*D) hD)
  have resource : Γ ⊢[PRAAx] le (one*S) (D*(num 3*L)) := by
    have same : Γ ⊢[PRAAx] padding D*L ≐ one*S :=
      ((mul_comm _ _).eqTrans hS.eqSymm).eqTrans (one_mul _).eqSymm
    exact le_congr same (by ipra_ring) (mul_le_mul_right L pay)
  have hq := rounded_floor q S D (upper_mono _ _ _ _ _ _
    (positive_product _ _ hThree hL) h resource)
  have reserve : Γ ⊢[PRAAx] le (D+two) (padding D) :=
    le_congr (by ipra_ring) (by unfold padding; ipra_ring) (add_le_add_right (D+one) hD)
  have cmp : Γ ⊢[PRAAx] zle (ZT.ofNat (D+two)) (ZT.ofNat (padding D)) :=
    le_congr (add_zero _).eqSymm (add_zero _).eqSymm reserve
  exact zle_trans (neg_order cmp) hq

def source (f : PTm 2) (x K L : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift K) ⟶ upper (fstT qzero) (fstT (inst2 f (var 0) (Syn.shift x))) one (num 3*Syn.shift L))

theorem floor_on (f : PTm 2) (x K L : PTm n)
    (hD : Γ ⊢[PRAAx] le one (divisor x)) (hL : Γ ⊢[PRAAx] le one L)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ L*padding (divisor x)) (h : Γ ⊢[PRAAx] source f x K L) :
    Γ ⊢[PRAAx] floorOn (body f) x K (padding (divisor x)) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh K) :: Γ.map Fm.shift
  have hd : Δ ⊢[PRAAx] le one (divisor (sh x)) := by
    simpa only [Δ,i,sh,Fm.shift,Syn.shift,subst_le,subst_divisor,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hD.shift.wk
  have hl : Δ ⊢[PRAAx] le one (sh L) := by
    simpa only [Δ,i,sh,Fm.shift,Syn.shift,subst_le,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hL.shift.wk
  have hs : Δ ⊢[PRAAx] latticeScale (sh x) ≐ sh L*padding (divisor (sh x)) := by
    simpa [Δ,i,sh,Fm.shift,Syn.shift,padding,two,one] using hS.shift.wk
  have row : Δ ⊢[PRAAx] upper (fstT qzero) (fstT (inst2 f i (sh x))) one (num 3*sh L) :=
    .impE h.allOpen.wk Prf.hyp0
  have shiftPadding : Syn.shift (padding (divisor x)) = padding (divisor (sh x)) := by
    simp [padding,sh,Syn.shift,two,one]
  rw [shiftPadding,sample_at]
  exact floor_at _ _ _ _ hd hl hs row

theorem actual_Gaussian_third_observation_floor_closed (f : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let x := var 0
       let K := var 1
       let L := var 2
       le one (divisor x) ⟶ le one L ⟶ latticeScale x ≐ L*padding (divisor x) ⟶ source f x K L ⟶
         floorOn (body f) x K (padding (divisor x))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (floor_on f _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicThirdFloor
