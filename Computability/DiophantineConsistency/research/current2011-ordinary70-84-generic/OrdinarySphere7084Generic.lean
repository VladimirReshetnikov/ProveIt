import OrdinarySphere7160Generic

/-! Generic 70/84 ordinary-strong sphere and 67/94 zero equivalence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.OrdinarySphere7084Generic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
open FreshCarrierSpheres OrdinarySphere7160Generic
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

section Ring
variable {R : Type*} [CommRing R]
def value70 (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let d := Carrier65.core p v
  let I := d.i*d.c^2
  let strong := I^2-d.delta*(d.f^2-1)
  (auxiliary d)^2 + (d.P*d.Q*d.W-1)^2 + strong^2 - 1
end Ring

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable (F : Facts R) (p : Fin 4 → R) (v : Fin 14 → R)
variable (hb : 0 < p 0) (hv : ∀ j, 0 < v j)
include F hb hv

theorem zero_iff94 : value70 p v = 0 ↔ Carrier94Value.value94 p v = 0 := by
  let d := Carrier65.core p v
  let I := d.i*d.c^2
  let Z := 1+I^2-d.delta*(d.f^2-1)
  have hnP : d.P ≠ -1 := (negative_unit_exclusions F p v hb hv).1
  have hnQ : d.Q ≠ -1 := (negative_unit_exclusions F p v hb hv).2.1
  have hnZ : Z ≠ -1 := ordinary_strong_ne_neg_one F p v
  have hu : 1 ≤ (auxiliary d)^2 := square_ge_one F (auxiliary_ne_zero F p v hb hv)
  have hUneg (hz : Z=1) : auxiliary d ≠ -1 := by
    have he : I^2=d.delta*(d.f^2-1) := by dsimp [Z] at hz; linear_combination hz
    have eqU : auxiliary d=I^2*(d.V^2-d.y^2)+d.y^2 := by
      unfold auxiliary; rw [he]
    rw [eqU]
    exact square_aux_ne_neg_one F _ _ _
  constructor
  · intro hz
    have hq := sq_nonneg (d.P*d.Q*d.W-1)
    have hs := sq_nonneg (I^2-d.delta*(d.f^2-1))
    change (auxiliary d)^2+(d.P*d.Q*d.W-1)^2+
      (I^2-d.delta*(d.f^2-1))^2-1=0 at hz
    have hus : (auxiliary d)^2=1 := by nlinarith only [hz,hu,hq,hs]
    have hqs : (d.P*d.Q*d.W-1)^2=0 := by nlinarith only [hz,hu,hq,hs]
    have hss : (I^2-d.delta*(d.f^2-1))^2=0 := by nlinarith only [hz,hu,hq,hs]
    have hpqw : d.P*d.Q*d.W=1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hqs)
    have hZ : Z=1 := by dsimp [Z]; have e := pow_eq_zero_iff two_ne_zero |>.mp hss; linear_combination e
    have hU := sq_one (hUneg hZ) hus
    have hP : d.P=1 := unit_eq_one F.discrete
      (show d.P*(d.Q*d.W)=1 by linear_combination hpqw) hnP
    have hQ : d.Q=1 := unit_eq_one F.discrete
      (show d.Q*(d.P*d.W)=1 by linear_combination hpqw) hnQ
    have hW : d.W=1 := by rw [hP,hQ] at hpqw; linear_combination hpqw
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
    change (auxiliary d)^2+(d.P*d.Q*d.W-1)^2+
      (I^2-d.delta*(d.f^2-1))^2-1=0
    have he : I^2-d.delta*(d.f^2-1)=0 := by dsimp [Z] at hZ; linear_combination hZ
    rw [hP,hQ,hU,hW,he]; ring
end Generic

#print axioms zero_iff94
end DiophantineConsistency.OrdinarySphere7084Generic
