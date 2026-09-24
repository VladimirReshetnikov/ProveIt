import Diophantine.Paper1976.Theorem39Elimination
import Diophantine.Common.RadicalBounds

/-!
# Polynomial weights for the refined relation-combining construction

The weights bound complex square roots on every natural assignment. In
particular, the signed capital expressions `K`, `L`, `R`, and `G` are not
assumed nonnegative. The formulas use the article's parameter `k`; the
prime-polynomial construction can substitute `k + 1` afterwards.

An integer square-bound certificate permits multiplication of radicands
without making any choice of roots. The displayed weight expressions are
integer polynomials, suitable for subsequent degree certificates.
-/

namespace JSWW1976.RefinedWeightBounds

open Diophantine

/-- A polynomial weight leaves one unit of room beyond every square root. -/
structure Majorant (a V : ℤ) : Prop where
  one_le : 1 ≤ V
  sq_bound : |a| ≤ (V - 1) ^ 2

theorem Majorant.norm_le {a V : ℤ} (h : Majorant a V) {z : ℂ}
    (hz : z ^ 2 = (a : ℂ)) : ‖z‖ ≤ (V : ℝ) - 1 := by
  have hs : |(a : ℝ)| ≤ ((V : ℝ) - 1) ^ 2 := by exact_mod_cast h.sq_bound
  have hV : (1 : ℝ) ≤ V := by exact_mod_cast h.one_le
  have hn := RadicalBounds.norm_sq_of_sq_eq_int hz
  nlinarith only [hs, hV, hn, norm_nonneg z]

theorem Majorant.mono {a V W : ℤ} (h : Majorant a V) (hVW : V ≤ W) :
    Majorant a W := by
  refine ⟨h.one_le.trans hVW, h.sq_bound.trans ?_⟩
  exact pow_le_pow_left₀ (sub_nonneg.mpr h.one_le) (sub_le_sub_right hVW 1) 2

/-- Multiplying weights bounds the square root of the product, with the same
one-unit margin. No sign assumption on the radicands is needed. -/
theorem Majorant.mul {a b V W : ℤ} (ha : Majorant a V) (hb : Majorant b W) :
    Majorant (a * b) (V * W) := by
  have hV := ha.one_le
  have hW := hb.one_le
  have hnonneg : 0 ≤ (V - 1) * (W - 1) :=
    mul_nonneg (sub_nonneg.mpr hV) (sub_nonneg.mpr hW)
  have hVW : 1 ≤ V * W := by nlinarith only [hV, hW, hnonneg]
  refine ⟨hVW, ?_⟩
  calc
    |a * b| = |a| * |b| := abs_mul a b
    _ ≤ (V - 1) ^ 2 * (W - 1) ^ 2 :=
      mul_le_mul ha.sq_bound hb.sq_bound (abs_nonneg b) (sq_nonneg (V - 1))
    _ = ((V - 1) * (W - 1)) ^ 2 := (mul_pow _ _ 2).symm
    _ ≤ (V * W - 1) ^ 2 :=
      pow_le_pow_left₀ hnonneg (by nlinarith only [hV, hW]) 2

/-- The elementary bound for a Pell-shaped integer radicand, including
negative radicands and signed parameters. -/
theorem pell_majorant (α β : ℤ) :
    Majorant ((α ^ 2 - 1) * β ^ 2 + 1) ((|α| + 1) * |β| + 2) := by
  have ha := abs_nonneg α
  have hb := abs_nonneg β
  have hab := mul_nonneg ha hb
  have habb := mul_nonneg hab hb
  have hV : 1 ≤ (|α| + 1) * |β| + 2 := by
    have hmul := mul_nonneg (show 0 ≤ |α| + 1 by omega) hb
    omega
  refine ⟨hV, ?_⟩
  have htriangle : |(α ^ 2 - 1) * β ^ 2 + 1| ≤ α ^ 2 * β ^ 2 + β ^ 2 + 1 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [mul_nonneg (sq_nonneg α) (sq_nonneg β)]
    · nlinarith only [sq_nonneg β]
  apply htriangle.trans
  rw [← sq_abs α, ← sq_abs β]
  nlinarith only [hb, hab, habb]

/-- Replacing absolute values by larger nonnegative polynomial expressions
preserves the Pell bound. -/
theorem pell_majorant_of_bounds {α β A B : ℤ} (hA : |α| ≤ A) (hB : |β| ≤ B) :
    Majorant ((α ^ 2 - 1) * β ^ 2 + 1) ((A + 1) * B + 2) := by
  apply (pell_majorant α β).mono
  have hm : (|α| + 1) * |β| ≤ (A + 1) * B :=
    mul_le_mul (by omega : |α| + 1 ≤ A + 1) hB (abs_nonneg β)
    (by have := abs_nonneg α; omega)
  omega

/-- The analytic form of the signed Pell bound. -/
theorem norm_pell_le {α β : ℤ} {z : ℂ}
    (hz : z ^ 2 = (((α ^ 2 - 1) * β ^ 2 + 1 : ℤ) : ℂ)) :
    ‖z‖ ≤ |(α : ℝ) * (β : ℝ)| + |(β : ℝ)| + 1 := by
  have h := (pell_majorant α β).norm_le hz
  have he : (((|α| + 1) * |β| + 2 : ℤ) : ℝ) - 1 =
      |(α : ℝ) * (β : ℝ)| + |(β : ℝ)| + 1 := by
    push_cast
    rw [abs_mul]
    ring
  rwa [he] at h

/-- The degree-three weight for `U(a,b)`. -/
def uWeight (a b : ℤ) : ℤ := (a + 4) * (a + 2) * (b + 1) + 2

theorem u_majorant {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Majorant (elim39U a b) (uWeight a b) := by
  have hα : 0 ≤ a + 3 := by omega
  have hβ : 0 ≤ (a + 2) * (b + 1) := by positivity
  have h := pell_majorant_of_bounds
    (α := a + 3) (β := (a + 2) * (b + 1))
    (A := a + 3) (B := (a + 2) * (b + 1))
    (le_of_eq (abs_of_nonneg hα)) (le_of_eq (abs_of_nonneg hβ))
  convert h using 1 <;> dsimp [elim39U, uWeight] <;> ring

/-- Polynomial bounds for the four possibly signed capitals. -/
def kBound (k n p M : ℤ) : ℤ := n + k + 1 + p * (M + 1)
def lBound (k l M x : ℤ) : ℤ := k + 1 + l * (M * x + 1)
def rBound (k r M n x : ℤ) : ℤ := k + 1 + r * (M * n * x + 1)
def gBound (A F : ℤ) : ℤ := A + F * (F + A)

private theorem abs_sub_bound {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ≤ a + b := by
  simpa only [abs_of_nonneg ha, abs_of_nonneg hb] using abs_sub a b

theorem abs_k_le {k n p M : ℤ} (hk : 0 ≤ k) (hn : 0 ≤ n)
    (hp : 0 ≤ p) (hM : 0 ≤ M) :
    |n + 1 + p * (M - 1) - k| ≤ kBound k n p M := by
  have h := abs_sub_bound (a := n + 1 + p * M) (b := p + k)
    (by positivity) (by omega)
  calc
    |n + 1 + p * (M - 1) - k| = |(n + 1 + p * M) - (p + k)| :=
      congrArg abs (by ring)
    _ ≤ (n + 1 + p * M) + (p + k) := h
    _ = kBound k n p M := by dsimp [kBound]; ring

theorem abs_l_le {k l M x : ℤ} (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hM : 0 ≤ M) (hx : 0 ≤ x) :
    |k + 1 + l * (M * x - 1)| ≤ lBound k l M x := by
  have h := abs_sub_bound (a := k + 1 + l * (M * x)) (b := l)
    (by positivity) hl
  calc
    |k + 1 + l * (M * x - 1)| = |(k + 1 + l * (M * x)) - l| :=
      congrArg abs (by ring)
    _ ≤ (k + 1 + l * (M * x)) + l := h
    _ = lBound k l M x := by dsimp [lBound]; ring

theorem abs_r_le {k r M n x : ℤ} (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hn : 0 ≤ n) (hx : 0 ≤ x) :
    |k + 1 + r * (M * n * x - 1)| ≤ rBound k r M n x := by
  simpa only [lBound, rBound, mul_assoc] using
    (abs_l_le (k := k) (l := r) (M := M * n) (x := x)
      hk hr (mul_nonneg hM hn) hx)

theorem abs_g_le {A F : ℤ} (hA : 0 ≤ A) (hF : 0 ≤ F) :
    |A + F * (F - A)| ≤ gBound A F := by
  calc
    |A + F * (F - A)| ≤ |A| + |F * (F - A)| := abs_add_le _ _
    _ = A + F * |F - A| := by rw [abs_mul, abs_of_nonneg hA, abs_of_nonneg hF]
    _ ≤ A + F * (F + A) := by
      have := mul_le_mul_of_nonneg_left (abs_sub_bound hF hA) hF
      linarith
    _ = gBound A F := rfl

/-- The six polynomial weights, in the order of `elim39Squares`. -/
def weights (k n x w m i j p l r z : ℤ) : Fin 6 → ℤ :=
  let v := elim39Values k n x w m i j p l r z
  ![uWeight (2 * k) n, uWeight (2 * n) x,
    ((v.A + 1) * v.C + 2) * ((v.A + 1) * v.E + 2) *
      ((gBound v.A v.F + 1) * v.H + 2),
    (v.M + 1) * kBound k n p v.M + 2,
    (v.M * x + 1) * lBound k l v.M x + 2,
    (v.M * n * x + 1) * rBound k r v.M n x + 2]

/-- All six bounds hold independently of the square, divisibility, or
inequality conditions in the prime criterion. -/
theorem weights_majorant (k n x w m i j p l r z : ℕ) (idx : Fin 6) :
    Majorant (elim39Squares k n x w m i j p l r z idx)
      (weights k n x w m i j p l r z idx) := by
  let v := elim39Values k n x w m i j p l r z
  have hM : 1 ≤ v.M := by
    change 1 ≤ 16 * (n : ℤ) * x * (w + 2) + 1
    have h : 0 ≤ 16 * (n : ℤ) * x * (w + 2) := by positivity
    omega
  have hM0 : 0 ≤ v.M := by omega
  have hA : 1 ≤ v.A := by
    change 1 ≤ v.M * ((x : ℤ) + 1)
    have h := mul_nonneg hM0 (show (0 : ℤ) ≤ x by positivity)
    nlinarith only [hM, h]
  have hA0 : 0 ≤ v.A := by omega
  have hC : 0 ≤ v.C := by
    change 0 ≤ (m : ℤ) + ((n : ℤ) + 1)
    positivity
  have hA2 : 0 ≤ v.A ^ 2 - 1 := by nlinarith only [hA]
  have hD : 0 ≤ v.D := by
    change 0 ≤ (v.A ^ 2 - 1) * v.C ^ 2 + 1
    have h := mul_nonneg hA2 (sq_nonneg v.C)
    omega
  have hE : 0 ≤ v.E := by
    change 0 ≤ 2 * ((i : ℤ) + 1) * v.D * v.C ^ 2
    positivity
  have hF : 0 ≤ v.F := by
    change 0 ≤ (v.A ^ 2 - 1) * v.E ^ 2 + 1
    have h := mul_nonneg hA2 (sq_nonneg v.E)
    omega
  have hH : 0 ≤ v.H := by
    change 0 ≤ ((n : ℤ) + 1) + 2 * ((j : ℤ) + 1) * v.C
    positivity
  have hK : |v.K| ≤ kBound k n p v.M :=
    abs_k_le (by positivity) (by positivity) (by positivity) hM0
  have hL : |v.L| ≤ lBound k l v.M x :=
    abs_l_le (by positivity) (by positivity) hM0 (by positivity)
  have hR : |v.R| ≤ rBound k r v.M n x :=
    abs_r_le (by positivity) (by positivity) hM0 (by positivity) (by positivity)
  have hG : |v.G| ≤ gBound v.A v.F := abs_g_le hA0 hF
  have hDmajor : Majorant v.D ((v.A + 1) * v.C + 2) :=
    pell_majorant_of_bounds (le_of_eq (abs_of_nonneg hA0)) (le_of_eq (abs_of_nonneg hC))
  have hFmajor : Majorant v.F ((v.A + 1) * v.E + 2) :=
    pell_majorant_of_bounds (le_of_eq (abs_of_nonneg hA0)) (le_of_eq (abs_of_nonneg hE))
  have hImajor : Majorant v.I ((gBound v.A v.F + 1) * v.H + 2) :=
    pell_majorant_of_bounds hG (le_of_eq (abs_of_nonneg hH))
  fin_cases idx
  · exact u_majorant (by positivity) (by positivity)
  · exact u_majorant (by positivity) (by positivity)
  · exact (hDmajor.mul hFmajor).mul hImajor
  · exact pell_majorant_of_bounds (le_of_eq (abs_of_nonneg hM0)) hK
  · exact pell_majorant_of_bounds
      (le_of_eq (abs_of_nonneg (mul_nonneg hM0 (show (0 : ℤ) ≤ x by positivity)))) hL
  · exact pell_majorant_of_bounds
      (le_of_eq (abs_of_nonneg (mul_nonneg
        (mul_nonneg hM0 (show (0 : ℤ) ≤ n by positivity))
        (show (0 : ℤ) ≤ x by positivity)))) hR

theorem one_le_weights (k n x w m i j p l r z : ℕ) (idx : Fin 6) :
    1 ≤ weights k n x w m i j p l r z idx :=
  (weights_majorant k n x w m i j p l r z idx).one_le

theorem norm_root_le (k n x w m i j p l r z : ℕ) {roots : Fin 6 → ℂ}
    (hroots : ∀ idx, roots idx ^ 2 =
      (elim39Squares k n x w m i j p l r z idx : ℂ)) (idx : Fin 6) :
    ‖roots idx‖ ≤ (weights k n x w m i j p l r z idx : ℝ) - 1 :=
  (weights_majorant k n x w m i j p l r z idx).norm_le (hroots idx)

/-- The replacement first radicand from equation (24). -/
def mergedRadicand (k n x : ℤ) : ℤ :=
  let T := elim39U (2 * k) n
  T * (16 * T * (T - 1) * (n + 1) ^ 2 * (x + 1) ^ 2 + 1)

/-- The degree-eleven polynomial weight for the replacement radicand. -/
def mergedWeight (k n x : ℤ) : ℤ :=
  let T := elim39U (2 * k) n
  uWeight (2 * k) n * (4 * T * (n + 1) * (x + 1) + 2)

theorem merged_majorant (k n x : ℕ) :
    Majorant (mergedRadicand k n x) (mergedWeight k n x) := by
  let T := elim39U (2 * (k : ℤ)) n
  have hT : 1 ≤ T := by
    dsimp [T, elim39U]
    have h : 0 ≤ (2 * (k : ℤ) + 2) ^ 3 * (2 * (k : ℤ) + 4) * ((n : ℤ) + 1) ^ 2 :=
      by positivity
    omega
  have hα : 0 ≤ 2 * T - 1 := by omega
  have hβ : 0 ≤ 2 * ((n : ℤ) + 1) * ((x : ℤ) + 1) := by positivity
  have hsecond := pell_majorant_of_bounds (le_of_eq (abs_of_nonneg hα))
    (le_of_eq (abs_of_nonneg hβ))
  have hsecond' :
      Majorant (16 * T * (T - 1) * ((n : ℤ) + 1) ^ 2 * ((x : ℤ) + 1) ^ 2 + 1)
        (4 * T * ((n : ℤ) + 1) * ((x : ℤ) + 1) + 2) := by
    convert hsecond using 1 <;> ring
  exact (u_majorant (a := 2 * (k : ℤ)) (b := n) (by positivity) (by positivity)).mul hsecond'

/-- Five radicands with the replacement test first. This definition is a size
interface only; it makes no claim about equivalence of the prime criteria. -/
def fiveRadicands (k n x w m i j p l r z : ℤ) : Fin 5 → ℤ :=
  let a := elim39Squares k n x w m i j p l r z
  ![mergedRadicand k n x, a 2, a 3, a 4, a 5]

def fiveWeights (k n x w m i j p l r z : ℤ) : Fin 5 → ℤ :=
  let V := weights k n x w m i j p l r z
  ![mergedWeight k n x, V 2, V 3, V 4, V 5]

theorem fiveWeights_majorant (k n x w m i j p l r z : ℕ) (idx : Fin 5) :
    Majorant (fiveRadicands k n x w m i j p l r z idx)
      (fiveWeights k n x w m i j p l r z idx) := by
  fin_cases idx
  · exact merged_majorant k n x
  · exact weights_majorant k n x w m i j p l r z 2
  · exact weights_majorant k n x w m i j p l r z 3
  · exact weights_majorant k n x w m i j p l r z 4
  · exact weights_majorant k n x w m i j p l r z 5

theorem one_le_fiveWeights (k n x w m i j p l r z : ℕ) (idx : Fin 5) :
    1 ≤ fiveWeights k n x w m i j p l r z idx :=
  (fiveWeights_majorant k n x w m i j p l r z idx).one_le

theorem norm_five_root_le (k n x w m i j p l r z : ℕ) {roots : Fin 5 → ℂ}
    (hroots : ∀ idx, roots idx ^ 2 =
      (fiveRadicands k n x w m i j p l r z idx : ℂ)) (idx : Fin 5) :
    ‖roots idx‖ ≤ (fiveWeights k n x w m i j p l r z idx : ℝ) - 1 :=
  (fiveWeights_majorant k n x w m i j p l r z idx).norm_le (hroots idx)

end JSWW1976.RefinedWeightBounds
