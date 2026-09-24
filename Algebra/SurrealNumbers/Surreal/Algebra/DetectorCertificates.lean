import Surreal.Algebra.IntersectiveWitnessPolynomials

/-!
# The printed detector certificates

The elementary identities in `odg:def:ex:certificates`, valid for any
purely infinite input rather than just omega. Only the coefficient
field scalar two is divided in the second example.
-/

namespace Surreal.IntersectivePolynomial

noncomputable section

/-- The displayed degree-five witness for an input of constant term one. -/
def oneShiftS {R : Type*} [CommRing R] (x : R) : R :=
  13 * (x - 1) * (13 * x ^ 2 - 17) * (13 * x ^ 2 - 221)

/-- The literal printed identity for 1+x, with t=-r*x and r²=13. -/
theorem oneShift_identity {R : Type*} [CommRing R] (r x : R) (hr : r ^ 2 = 13) :
    (1 + x) * oneShiftS x = value (-r * x) := by
  simp only [oneShiftS, value, mul_pow, neg_sq, hr]
  ring

/-- Any ring-valued augmentation sends the printed s to -48841 when x has augmentation zero. -/
theorem oneShiftS_augmentation {R S : Type*} [CommRing R] [CommRing S]
    (ε : R →+* S) (x : R) (hx : ε x = 0) : ε (oneShiftS x) = -48841 := by
  norm_num [oneShiftS, map_mul, map_sub, map_pow, map_ofNat, hx]

variable {K H : Type*} [Field K] [CharZero K] [CommRing H] [Algebra K H]

/-- The slope in the printed constant-term-two example. -/
def twoShiftSlope (r : K) : K := (1 - r) / 2

/-- The affine witness for 2+x is literally 1+alpha*x. -/
theorem twoShiftT_formula (r : K) (x : H) :
    AugmentationRootDetector.affineWitness r (twoShiftSlope r) (2 + x) =
      1 + algebraMap K H (twoShiftSlope r) * x := by
  have he : r + twoShiftSlope r * 2 = 1 := by
    dsimp [twoShiftSlope]
    field_simp
    ring
  have hm := congrArg (algebraMap K H) he
  simp only [map_add, map_mul, map_ofNat, map_one] at hm
  dsimp [AugmentationRootDetector.affineWitness]
  linear_combination hm

/-- The chosen modular value gives constant coefficients one and -21120, and a certificate. -/
theorem twoShift_augmentation (ε : H →ₐ[K] K) (r : K) (hr : r ^ 2 = 13)
    (x : H) (hx : ε x = 0) :
    let t := (witnessTPolynomial r (twoShiftSlope r)).eval₂ (algebraMap K H) (2 + x)
    let s := (witnessSPolynomial r (twoShiftSlope r)).eval₂ (algebraMap K H) (2 + x)
    ε t = 1 ∧ ε s = -21120 ∧ (2 + x) * s = value t := by
  have hm := witnessPolynomials_augmentation ε (Int.castRingHom K) r hr
    1 2 (-21120) (by norm_num) (by norm_num [value]) (2 + x) (by simp [map_ofNat, hx])
  simpa only [Int.coe_castRingHom, Int.cast_one, Int.cast_ofNat, Int.cast_neg, twoShiftSlope] using hm

end
end Surreal.IntersectivePolynomial
