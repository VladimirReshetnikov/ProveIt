import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
A proof kernel for the fixed-prime-support refactor of
CurrentControllerUnits2011. This file imports no ProveIt modules;
it checks the generic transport step, not the concrete current coefficient.
-/
namespace ControllerPrimeSupport
set_option Elab.async false

/-- A unit modulo d*p stays a unit after thickening the p factor.  The
parameter n=0 is included; no primality or squarefreeness is needed here. -/
theorem coprime_thickening {x b d p : ℕ}
    (h : (x : ZMod (d*p)) = (b : ZMod (d*p)))
    (hb : Nat.Coprime b (d*p)) (n : ℕ) : Nat.Coprime x (d*p^n) := by
  have hx : Nat.Coprime x (d*p) := by
    rw [← ZMod.isUnit_iff_coprime, h]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hb
  obtain ⟨hd, hp⟩ := Nat.coprime_mul_iff_right.mp hx
  exact hd.mul_right (hp.pow_right n)

/-- The exact factor pattern of CurrentControllerUnits2011.Gamma, with
R = radix^977, q = B^(auxiliary^n), and w = B^(auxiliary^rw). -/
def rankFactor (R q K w : ℕ) : ℕ := R*(q^2-1)*(1+q*(K+w))

/-- Repeated numerical nonzero tests can be factored through this single
polynomial congruence. The natural-subtraction bounds stay explicit. -/
theorem rankFactor_cast_congr {m R q K w B : ℕ}
    (hq1 : 1 ≤ q^2) (hB1 : 1 ≤ B^2)
    (hq : (q : ZMod m) = (B : ZMod m))
    (hw : (w : ZMod m) = (B : ZMod m)) :
    (rankFactor R q K w : ZMod m) = (rankFactor R B K B : ZMod m) := by
  simp only [rankFactor, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub hq1, Nat.cast_sub hB1, Nat.cast_pow]
  rw [hq, hw]

/-- The family of varying coefficients needs one fixed unit certificate. -/
theorem rankFactor_coprime_thickening {R q K w B d p : ℕ}
    (hq1 : 1 ≤ q^2) (hB1 : 1 ≤ B^2)
    (hq : (q : ZMod (d*p)) = (B : ZMod (d*p)))
    (hw : (w : ZMod (d*p)) = (B : ZMod (d*p)))
    (hbase : Nat.Coprime (rankFactor R B K B) (d*p)) (n : ℕ) :
    Nat.Coprime (rankFactor R q K w) (d*p^n) :=
  coprime_thickening (rankFactor_cast_congr hq1 hB1 hq hw) hbase n

-- Regression controls: the zero exponent and a composite thickened factor
-- are intentional. The generic theorem must not require p prime.
example : Nat.Coprime 35 (6*4^0) :=
  coprime_thickening (b := 11) (by decide) (by decide) 0
example : Nat.Coprime 35 (6*4^3) :=
  coprime_thickening (b := 11) (by decide) (by decide) 3
example : (rankFactor 2 17 4 32 : ZMod 15) =
    (rankFactor 2 2 4 2 : ZMod 15) :=
  rankFactor_cast_congr (by decide) (by decide) (by decide) (by decide)

#print axioms coprime_thickening
#print axioms rankFactor_cast_congr
#print axioms rankFactor_coprime_thickening
end ControllerPrimeSupport
