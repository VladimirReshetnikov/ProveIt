import GRHArticle.ProgressionFree.IntegerDyadicArithmetic

/-!
# Integer block certificate for the exchange prime-square estimate

A block covers 8192 consecutive integers. All tests below use bounded
integer arithmetic. The analytic interpretation is in
`IntegerBoundaryPrimeSieve`.
-/

namespace GRHArticle.ProgressionFree

namespace IntegerBoundarySieve

def scale : Nat := 10^15

/-- The product of the primes from 17 through 311. -/
def sieveDivisor : Nat := 6497967364470800349733221346172236193024881815547431427854945541658635781011346849868214763384279578411171502739322418639

def weight (p : Nat) : Nat :=
  if 6619 < p && (Nat.gcd p 30030 == 1) && (Nat.gcd p sieveDivisor == 1) then scale/p^2+1 else 0

def block (i : Nat) := integerDyadicSum weight 13 (8192*i)

/-- Upward-rounded weights in the successive blocks. -/
def budget (i : Nat) : Nat :=
  ([3195514317, 6552779595, 2046754619, 976726485, 580305040, 379990475, 270518657, 194010893,
    152970008, 120471115, 97226606, 80560927, 68525999, 57892089, 51777368, 44893895,
    39999393, 35751854, 32411726, 28503409, 25813587, 24046094, 21813410, 20060578,
    18307815, 17407868, 15876070, 14897829, 13427889, 13086163, 12128797, 11132314,
    10864939, 10053362, 9477550, 8715544, 8455763, 8047144, 7790845, 7412529,
    6923981, 6559423, 6377931, 5979531, 5741367, 5447507, 5271892, 5143884,
    4797072, 4620579, 4476493, 4316323, 4238219, 4000144, 3873840, 3657911,
    3538832, 3556812, 3388757, 3240308, 3187960, 3026220, 2922934, 2935464] : List Nat)[i]?.getD 0

set_option Elab.async false
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem blocks_checked (i : Nat) (hi : i < 64) : block i ≤ budget i := by
  iterate 64
    rcases i with _ | i
    · as_aux_lemma => decide +kernel
  omega

end IntegerBoundarySieve
end GRHArticle.ProgressionFree
