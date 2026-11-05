import FreshCarrierSpheres
import DiophantineConsistency.Carrier94Value

/-! Generic model-ring identity between ordinary 71/60 and 67/94 values. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.OrdinarySphere7160Generic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
open FreshCarrierSpheres
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

section Ring
variable {R : Type*} [CommRing R]
def value71 (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let d := Carrier65.core p v
  let I := d.i*d.c^2
  let strong := I^2-d.delta*(d.f^2-1)
  d.P^2 + (auxiliary d)^2 + (d.Q*d.W-1)^2 + strong^2 - 2

end Ring

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable (F : Facts R) (p : Fin 4 → R) (v : Fin 14 → R)
variable (hb : 0 < p 0) (hv : ∀ j, 0 < v j)
include F hb hv

omit hb hv in
theorem ordinary_strong_ne_neg_one :
    1 + ((Carrier65.core p v).i*(Carrier65.core p v).c^2)^2 -
      (Carrier65.core p v).delta*((Carrier65.core p v).f^2-1) ≠ -1 := by
  obtain ⟨φ⟩ := F.mod4
  rw [Carrier65.delta_shape]
  intro h
  have hm := congrArg φ h
  simp only [map_sub, map_mul, map_pow, map_add, map_one, map_neg, map_ofNat] at hm
  have bad : ∀ a i f : ZMod 4, 1+i^2-((a+2)^2-1)*(f^2-1) ≠ -1 := by decide
  exact bad _ _ _ hm

theorem zero_iff94 : value71 p v = 0 ↔ Carrier94Value.value94 p v = 0 := by
  let d := Carrier65.core p v
  let I := d.i*d.c^2
  let Z := 1+I^2-d.delta*(d.f^2-1)
  have hnP : d.P ≠ -1 := (negative_unit_exclusions F p v hb hv).1
  have hnQ : d.Q ≠ -1 := (negative_unit_exclusions F p v hb hv).2.1
  have hnZ : Z ≠ -1 := ordinary_strong_ne_neg_one F p v
  have hp : 1 ≤ d.P^2 := square_ge_one F (first_ne_zero F p v hb hv)
  have hu : 1 ≤ (auxiliary d)^2 := square_ge_one F (auxiliary_ne_zero F p v hb hv)
  have hUneg (hz : Z=1) : auxiliary d ≠ -1 := by
    have he : I^2=d.delta*(d.f^2-1) := by dsimp [Z] at hz; linear_combination hz
    have eqU : auxiliary d=I^2*(d.V^2-d.y^2)+d.y^2 := by
      unfold auxiliary; rw [he]
    rw [eqU]
    exact square_aux_ne_neg_one F _ _ _
  constructor
  · intro hz
    have hq := sq_nonneg (d.Q*d.W-1)
    have hs := sq_nonneg (I^2-d.delta*(d.f^2-1))
    change d.P^2+(auxiliary d)^2+(d.Q*d.W-1)^2+
      (I^2-d.delta*(d.f^2-1))^2-2=0 at hz
    have hps : d.P^2=1 := by nlinarith only [hz,hp,hu,hq,hs]
    have hus : (auxiliary d)^2=1 := by nlinarith only [hz,hp,hu,hq,hs]
    have hqs : (d.Q*d.W-1)^2=0 := by nlinarith only [hz,hp,hu,hq,hs]
    have hss : (I^2-d.delta*(d.f^2-1))^2=0 := by nlinarith only [hz,hp,hu,hq,hs]
    have hqw : d.Q*d.W=1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hqs)
    have hZ : Z=1 := by dsimp [Z]; have e := pow_eq_zero_iff two_ne_zero |>.mp hss; linear_combination e
    have hP := sq_one hnP hps
    have hU := sq_one (hUneg hZ) hus
    obtain ⟨hQ,hW⟩ := unit_factors F hqw hnQ
    change d.P*d.Q*(auxiliary d)*d.W*Z-1=0
    rw [hP,hQ,hU,hW,hZ]; ring
  · intro hz
    change d.P*d.Q*(auxiliary d)*d.W*Z-1=0 at hz
    have hproduct : d.P*d.Q*(auxiliary d)*d.W*Z=1 := sub_eq_zero.mp hz
    have hZ : Z=1 := unit_eq_one F.discrete
      (show Z*(d.P*d.Q*(auxiliary d)*d.W)=1 by linear_combination hproduct) hnZ
    have hP : d.P=1 := unit_eq_one F.discrete
      (show d.P*(d.Q*(auxiliary d)*d.W*Z)=1 by linear_combination hproduct) hnP
    have hQ : d.Q=1 := unit_eq_one F.discrete
      (show d.Q*(d.P*(auxiliary d)*d.W*Z)=1 by linear_combination hproduct) hnQ
    have hU : auxiliary d=1 := unit_eq_one F.discrete
      (show (auxiliary d)*(d.P*d.Q*d.W*Z)=1 by linear_combination hproduct) (hUneg hZ)
    have hW : d.W=1 := by rw [hP,hQ,hU,hZ] at hproduct; linear_combination hproduct
    change d.P^2+(auxiliary d)^2+(d.Q*d.W-1)^2+
      (I^2-d.delta*(d.f^2-1))^2-2=0
    have he : I^2-d.delta*(d.f^2-1)=0 := by dsimp [Z] at hZ; linear_combination hZ
    rw [hP,hQ,hU,hW,he]; ring
end Generic

#print axioms ordinary_strong_ne_neg_one
#print axioms zero_iff94
end DiophantineConsistency.OrdinarySphere7160Generic
