import DiophantineConsistency.ArithmeticConstructionKernel
import DiophantineConsistency.WangTiles942PhysicalOrder
import DiophantineConsistency.CurrentControllerData2011

/-!
# Modular values of the actual length2011 kernel

The abstract selector sum is reindexed through the proved physical
permutation. A verified Horner accumulator then evaluates that same sum;
the numerical data do not replace the literal kernel by a new port.
-/
namespace DiophantineConsistency.CurrentKernelResidues2011

open WangTiles942 WangTiles942PhysicalData WangTiles942PhysicalOrder
open CurrentKernel2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- High-to-low evaluation of the doubled selector weights. -/
def evaluate {R : Type*} [Semiring R] (r : R) : List (ℕ × ℕ) → R
  | [] => 0
  | a :: l => 2 * (a.2 : R) * r ^ l.length + evaluate r l

private theorem evaluate_eq_shared {R : Type*} [Semiring R] (r : R)
    (l : List (ℕ × ℕ)) : evaluate r l = ArithmeticConstructionKernel.evaluate r l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [evaluate, ArithmeticConstructionKernel.evaluate, ih]

theorem evaluate_append {R : Type*} [CommSemiring R] (r : R)
    (l v : List (ℕ × ℕ)) :
    evaluate r (l ++ v) = evaluate r l * r ^ v.length + evaluate r v := by
  simpa only [evaluate_eq_shared] using ArithmeticConstructionKernel.evaluate_append r l v

theorem evaluate_sum {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ)) :
    evaluate r l = ∑ j : Fin l.length,
      2 * (l[j.val].2 : R) * r ^ (l.length - 1 - j.val) := by
  simpa only [evaluate_eq_shared] using ArithmeticConstructionKernel.evaluate_sum r l

/-- The complete physical selector polynomial, including protected Start. -/
theorem selector_reflection {R : Type*} [CommSemiring R] (r : R) :
    (∑ i : Fin 942, 2 * (selectorWeight (tile i) : R) * r ^ (1005-physicalPosition i)) =
      2 * (selectorWeight start : R) * r ^ 1005 + evaluate r rows * r ^ 64 := by
  exact ArithmeticConstructionKernel.selector_reflection r

/-- The34 true packed color controls, in west/north/east/south order. -/
def controlReflection {R : Type*} [CommSemiring R] (r : R) : R :=
    (∑ j : Fin 8, 2 * ((2^(10+j.val) : ℕ) : R) * r^(1005-(978+j.val))) +
    ((∑ j : Fin 9, 2 * ((2^(18+j.val) : ℕ) : R) * r^(1005-(960+j.val))) +
    ((∑ j : Fin 8, 2 * ((2^(27+j.val) : ℕ) : R) * r^(1005-(969+j.val))) +
     (∑ j : Fin 9, 2 * ((2^(35+j.val) : ℕ) : R) * r^(1005-(942+j.val)))))

/-- Exact whole-kernel identity over every commutative semiring. -/
theorem rawWord_cast {R : Type*} [CommSemiring R] (r : ℕ) :
    (rawWord r : R) =
      (r : R)^18 + (r : R)^1004 + (r : R)^2020 +
      (2 * (selectorWeight start : R) * (r : R)^1005 +
       evaluate (r : R) rows * (r : R)^64 + controlReflection (r : R)) := by
  exact ArithmeticConstructionKernel.rawWord_cast r

/- The literal ordered row list is certified by a linear Horner accumulator.
The original evaluate definition and its semantic bridge are unchanged. -/
def run {R : Type*} [Semiring R] (r : R) : List (ℕ × ℕ) → R → R
  | [], z => z
  | a :: l, z => run r l (z * r + 2 * (a.2 : R))

private theorem run_eq_shared {R : Type*} [Semiring R] (r : R)
    (l : List (ℕ × ℕ)) (z : R) : run r l z = ArithmeticConstructionKernel.run r l z := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih => simpa only [run, ArithmeticConstructionKernel.run] using ih (z * r + 2 * (a.2 : R))

theorem run_eq {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ)) (z : R) :
    run r l z = z * r ^ l.length + evaluate r l := by
  simpa only [run_eq_shared, evaluate_eq_shared] using ArithmeticConstructionKernel.run_eq r l z

theorem evaluate_eq_run {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ)) : evaluate r l = run r l 0 := by
  simpa only [run_eq_shared, evaluate_eq_shared] using ArithmeticConstructionKernel.evaluate_eq_run r l

/-- One common-modulus certificate, projected to every required factor. -/
theorem K_cast_common : (K : ZMod 11360848883) = 1491904576 := by
  exact ArithmeticConstructionKernel.K_cast_common

theorem K_cast_47 : (K : ZMod 47) = 26 := by
  exact ArithmeticConstructionKernel.K_cast_47

theorem K_cast_2011 : (K : ZMod 2011) = 1995 := by
  exact ArithmeticConstructionKernel.K_cast_2011

theorem K_cast_auxiliary : (K : ZMod 120199) = 114787 := by
  exact ArithmeticConstructionKernel.K_cast_auxiliary

private theorem transport_modulus (a m n r : ℕ) (hm : m = n)
    (h : a % m = r) : a % n = r := hm ▸ h

attribute [local irreducible] CurrentKernel2011.K CurrentControllerData2011.B

theorem K_mod_47 : K % 47 = 26 := ArithmeticConstructionKernel.K_mod_47
theorem K_mod_2011 : K % 2011 = 1995 := ArithmeticConstructionKernel.K_mod_2011
theorem K_mod_auxiliary : K % 120199 = 114787 :=
  ArithmeticConstructionKernel.K_mod_auxiliary

/-- The formerly conditional controller H residues are now unconditional. -/
theorem Hs_mod_47 :
    (1+CurrentControllerData2011.B*K+CurrentControllerData2011.B^2) % 47 = 29 :=
  CurrentControllerData2011.Hs_mod_47 K_mod_47

theorem Hs_mod_2011 :
    (1+CurrentControllerData2011.B*K+CurrentControllerData2011.B^2) % 2011 = 674 :=
  CurrentControllerData2011.Hs_mod_2011 K_mod_2011

theorem Hs_mod_auxiliary :
    (1+CurrentControllerData2011.B*K+CurrentControllerData2011.B^2) % 120199 = 36379 :=
  transport_modulus _ CurrentControllerData2011.auxiliary 120199 36379 rfl
    (CurrentControllerData2011.Hs_mod_auxiliary
      (transport_modulus K 120199 CurrentControllerData2011.auxiliary 114787 rfl
        K_mod_auxiliary))

end DiophantineConsistency.CurrentKernelResidues2011
