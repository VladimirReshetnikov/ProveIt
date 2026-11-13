import DiophantineConsistency.ArithmeticCarrier94Indices
import FreshCarrierSpheres

/-! UNCOMPILED DRAFT.  No declaration in this file is a checked result.

This isolates the ordinary-Pell residue used by the proposed 72/46 shear,
plus ring/order lemmas for the two positivity directions. The candidate's
literal graph evaluator, extraction of norm hypotheses from its zero, and
model/iPRA bridge are still absent. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sheared7246Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPeriodicity
open ArithmeticPellResidueClasses ArithmeticPellClassification
open ArithmeticPellIndexDivisibility ArithmeticPellHalfIndex
open ArithmeticPellFirstIndex

section Residue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Extract the proof-local residue from `ordinary_half_index`.
The ordinary strong equation alone does not suffice: the main Pell norm and
large-ordinate hypothesis are essential inputs to `relaxed_auxiliary`. -/
theorem ordinary_strong_mod_c (a c d f i : V)
    (hc : 0 < c) (hi : 0 < i) (hf : 0 < f)
    (hmain : d*d = 1 + delta a*c*c)
    (hord : (i*c*c)*(i*c*c) + delta a = delta a*f*f)
    (hbig : (a+2)*delta a*delta a < c) :
    (f*f)%c = (1:V)%c := by
  obtain ⟨p,_,_,hcp⟩ := solution_index a d c hmain
  have hp : 0<p := pos_iff_ne_zero.mpr (fun hz => (ne_of_gt hc) (by simpa [hz] using hcp.symm))
  have hord' : (i*c*c)*(i*c*c)+delta a=delta a*(f*f) := by simpa only [mul_assoc] using hord
  obtain ⟨m,_,hfm,hpm,_,_⟩ := relaxed_auxiliary a c p i f hp hi hf hcp.symm hord' hbig
  have hn := norm m a
  obtain ⟨t,ht⟩ : c∣ycoord m a := by
    rw [← hcp]
    exact (ArithmeticPellStrongDivisibility.y_dvd_iff a p m).mpr hpm
  have he : f*f=1+c*(delta a*t*ycoord m a) := by
    rw [hfm,hn]
    nth_rewrite 1 [ht]
    ring
  rw [he,mod_add_mul' _ _ hc]
end Residue

section OrderedRing
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Exact parent auxiliary factor after substituting `y_old = V + y`. -/
theorem auxiliary_shear (A V y : R) :
    A*(V^2-(V+y)^2)+(V+y)^2 = (V+y)^2-A*y*((V+y)+V) := by
  ring

/-- From the unit auxiliary norm, the only obstruction to `y > V` is `V=1`.
The caller must supply the separately proved ordinary-Pell residue/window
argument excluding `V=1`; positivity alone does not rule it out. -/
theorem positive_shear_of_unit_norm (A V y : R)
    (hA : 1 ≤ A) (hy : 1 ≤ y)
    (hnorm : A*(V^2-y^2)+y^2=1) (hV : V ≠ 1) : 0 < y-V := by
  by_contra h
  have hle : y ≤ V := le_of_not_gt (by simpa using h)
  have hd : 0 ≤ V^2-y^2 := by nlinarith [sq_nonneg (V-y), sq_nonneg (V+y)]
  have hp : 0 ≤ (A-1)*(V^2-y^2) := mul_nonneg (sub_nonneg.mpr hA) hd
  have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y-1)]
  have hy2eq : y^2=1 := by nlinarith [hp]
  have hyeq : y=1 := by nlinarith [sq_nonneg (y-1)]
  have hdeq : V^2-y^2=0 := by nlinarith [hp]
  have hVeq : V=1 := by nlinarith [sq_nonneg (V-1)]
  exact hV hVeq

/-- The sign of a nonzero parent ordinate can be chosen positive without
changing the auxiliary factor. -/
theorem auxiliary_abs (A V z : R) :
    A*(V^2-(|z|)^2)+(|z|)^2 = A*(V^2-z^2)+z^2 := by
  simp only [sq_abs]

/-- A proposed zero cannot have `V+y=0` under the indicated elementary
bounds. `hA` must be obtained from `f ≥ 1` and the positivity of Delta;
`hI` comes from positive `i,c` and the current port bounds. -/
theorem shifted_ordinate_ne_zero (P QW A I V y : R)
    (hy : 1 ≤ y) (hI : 2 ≤ I) (hA : A=0 ∨ 2 ≤ A)
    (hz : P^2 + (A*(V^2-(V+y)^2)+(V+y)^2)^2 +
      (QW-1)^2 + (I^2-A)^2 - 2 = 0) : V+y ≠ 0 := by
  intro hzero
  have hv2 : 1 ≤ V^2 := by nlinarith [sq_nonneg (y-1)]
  have hi2 : 4 ≤ I^2 := by nlinarith [sq_nonneg (I-2)]
  have he : A*(V^2-(V+y)^2)+(V+y)^2=A*V^2 := by rw [hzero]; ring
  rw [he] at hz
  rcases hA with ha | ha
  · have hs : 4 ≤ I^2-A := by rw [ha]; simpa using hi2
    have hs2 : 16 ≤ (I^2-A)^2 := by nlinarith [sq_nonneg (I^2-A-4)]
    nlinarith [sq_nonneg P, sq_nonneg (A*V^2), sq_nonneg (QW-1)]
  · have hm : 0 ≤ (A-2)*(V^2-1) := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hv2)
    have hv : 2 ≤ A*V^2 := by nlinarith [hm]
    have hv4 : 4 ≤ (A*V^2)^2 := by nlinarith [sq_nonneg (A*V^2-2)]
    nlinarith [sq_nonneg P, sq_nonneg (QW-1), sq_nonneg (I^2-A)]
end OrderedRing
end DiophantineConsistency.Sheared7246Draft
