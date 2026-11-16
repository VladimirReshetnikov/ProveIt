import Std

/-!
Checked native Lean arithmetic for the accompanying Siegel/Runge report.
These are theorems of Lean, not deeply embedded `Prf PRAAx` objects.
The full Siegel theorem is neither assumed nor proved here.
-/
namespace SiegelIPRA

theorem positive_product_sum (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a + b ≤ a * b + 1 := by
  cases a with
  | zero => omega
  | succ a =>
    have h : a ≤ a * b := by
      simpa using Nat.mul_le_mul_left a hb
    simp only [Nat.succ_mul]
    omega

theorem factor_natAbs_sum (u v d : Int) (hd : d ≠ 0) (h : u * v = d) :
    u.natAbs + v.natAbs ≤ d.natAbs + 1 := by
  have hu : u ≠ 0 := by
    intro hu
    simp [hu] at h
    exact hd h.symm
  have hv : v ≠ 0 := by
    intro hv
    simp [hv] at h
    exact hd h.symm
  have hp := positive_product_sum u.natAbs v.natAbs
    (Int.natAbs_pos.mpr hu) (Int.natAbs_pos.mpr hv)
  simpa [← Int.natAbs_mul, h] using hp

theorem difference_of_squares (z a : Int) :
    (z - a) * (z + a) = z * z - a * a := by
  simp only [Int.sub_mul, Int.mul_add, Int.mul_comm a z]
  omega

/-- The integer gap which drives the elementary Runge proof. -/
theorem square_gap (z a r : Int) (hr : r ≠ 0)
    (h : z * z = a * a + r) : a.natAbs ≤ r.natAbs := by
  have hf : (z-a)*(z+a)=r := by
    rw [difference_of_squares]
    omega
  have hs := factor_natAbs_sum (z-a) (z+a) r hr hf
  have ht := Int.natAbs_sub_le (z+a) (z-a)
  have he : (z+a)-(z-a)=2*a := by omega
  rw [he, Int.natAbs_mul] at ht
  have hpos : 0 < r.natAbs := Int.natAbs_pos.mpr hr
  omega

theorem quartic_factorization (a b x y : Int)
    (h : y*y = x*x*x*x + a*x*x + b) :
    (2*x*x+a-2*y)*(2*x*x+a+2*y) = a*a-4*b := by
  rw [difference_of_squares]
  have he := congrArg (fun z : Int => 4*z) h
  simp only [Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at he ⊢
  simp only [← Int.mul_assoc, Int.reduceMul] at he ⊢
  omega

/-- A sharper bound for biquadratic curves; a negative right side excludes points. -/
theorem quartic_bounds (a b x y : Int) (hd : a*a-4*b ≠ 0)
    (h : y*y = x*x*x*x + a*x*x + b) :
    4*x*x ≤ ((a*a-4*b).natAbs : Int)+1-2*a ∧
      4*y.natAbs ≤ (a*a-4*b).natAbs+1 := by
  let u := 2*x*x+a-2*y
  let v := 2*x*x+a+2*y
  have hs := factor_natAbs_sum u v (a*a-4*b) hd
    (quartic_factorization a b x y h)
  have hu : u ≤ (u.natAbs : Int) := Int.le_natAbs
  have hv : v ≤ (v.natAbs : Int) := Int.le_natAbs
  have he : u+v=4*x*x+2*a := by
    dsimp [u,v]
    simp only [Int.mul_assoc]
    omega
  have ht := Int.natAbs_sub_le v u
  have he' : v-u=4*y := by dsimp [u,v]; omega
  rw [he', Int.natAbs_mul] at ht
  constructor <;> omega

/-- Strictly between consecutive nonnegative integer squares there is no square. -/
theorem no_square_between (n k : Nat) (hlo : n*n < k*k)
    (hhi : k*k < (n+1)*(n+1)) : False := by
  by_cases h : k ≤ n
  · have hm := Nat.mul_le_mul h h
    omega
  · have hnk : n+1 ≤ k := by omega
    have hm := Nat.mul_le_mul hnk hnk
    omega

end SiegelIPRA
