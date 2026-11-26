import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Two-sided bounds in a commutative ring with a cone

iPRA has natural numbers only. A signed quantity is a difference of two terms, an element of the ring of
differences `Groth (Q Γ)`, and the elements of that ring that are values of terms form a set closed under sums and
products (`Nonneg Γ` of `Core/OrderCertificates`). An estimate `|y| ≤ T` between signed quantities is the pair of
facts that `T − y` and `T + y` are values of terms.

This module is the algebra of such estimates, with no reference to iPRA: `R` is a commutative ring and `P` a
subset of it that is a *cone* (`Cone P`: it contains `0` and `1`, is closed under `+` and `·`, `2x ∈ P` implies
`x ∈ P`, and `x, −x ∈ P` implies `x = 0`). `Foundations/SignedNorms` proves that `Nonneg Γ` is a cone, so every
lemma here is a rule for deriving inequalities between integer terms.

* `Bd P y T` is `|y| ≤ T`: `T − y ∈ P` and `T + y ∈ P`;
* `Bd.add`, `Bd.sub`, `Bd.neg`, `Bd.sum`: the triangle inequality; `Bd.smul`, `Bd.mul`: products
  (`|m y| ≤ a T` from `|m| ≤ a`, `|y| ≤ T`, by `2 (a T − m y) = (a − m)(T + y) + (a + m)(T − y)` and halving);
  `Bd.mono`, `Bd.half`, `Bd.eq_zero` (`|y| ≤ 0` gives `y = 0`);
* `RowBd P M A` is the row-sum bound `‖M‖ ≤ A` of a matrix: majorants `a i k` of the entries with
  `∑_k a i k ≤ A` in every row; `RowBd.mulVec` is `‖M y‖ ≤ ‖M‖ ‖y‖` for the maximum norm of vectors.

The finite sums are Mathlib `Finset` sums over `Fin d` for a fixed dimension `d`.
-/

namespace LeanProofs.IPRA.Foundations.SignedCone

variable {R : Type*} [CommRing R]

/-- A cone of a commutative ring: the "nonnegative" elements. -/
structure Cone (P : R → Prop) : Prop where
  zero : P 0
  one : P 1
  add : ∀ {x y : R}, P x → P y → P (x + y)
  mul : ∀ {x y : R}, P x → P y → P (x * y)
  half : ∀ {x : R}, P (2 * x) → P x
  anti : ∀ {x : R}, P x → P (-x) → x = 0

namespace Cone

variable {P : R → Prop}

omit [CommRing R] in
theorem of_eq {x y : R} (h : P x) (e : x = y) : P y := e ▸ h

theorem two (hP : Cone P) : P (2 : R) := of_eq (hP.add hP.one hP.one) (by ring)

theorem sum (hP : Cone P) {ι : Type*} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, P (f i)) :
    P (∑ i ∈ s, f i) :=
  Finset.sum_induction f P (fun _ _ => hP.add) hP.zero h

theorem pow (hP : Cone P) {x : R} (h : P x) : ∀ k : ℕ, P (x ^ k)
  | 0 => of_eq hP.one (pow_zero x).symm
  | k + 1 => of_eq (hP.mul (pow hP h k) h) (pow_succ x k).symm

end Cone

/-- `|y| ≤ T`: both `T − y` and `T + y` are in the cone. -/
def Bd (P : R → Prop) (y T : R) : Prop := P (T - y) ∧ P (T + y)

namespace Bd

variable {P : R → Prop} {y y' T T' : R}

theorem congr (h : Bd P y T) (ey : y = y') (eT : T = T') : Bd P y' T' := ey ▸ eT ▸ h

/-- The bound of a two-sided estimate is nonnegative. -/
theorem nonneg (hP : Cone P) (h : Bd P y T) : P T :=
  hP.half (Cone.of_eq (hP.add h.1 h.2) (by ring))

theorem neg (h : Bd P y T) : Bd P (-y) T :=
  ⟨Cone.of_eq h.2 (by ring), Cone.of_eq h.1 (by ring)⟩

theorem mono (hP : Cone P) (h : Bd P y T) (hT : P (T' - T)) : Bd P y T' :=
  ⟨Cone.of_eq (hP.add h.1 hT) (by ring), Cone.of_eq (hP.add h.2 hT) (by ring)⟩

theorem add (hP : Cone P) (h : Bd P y T) (h' : Bd P y' T') : Bd P (y + y') (T + T') :=
  ⟨Cone.of_eq (hP.add h.1 h'.1) (by ring), Cone.of_eq (hP.add h.2 h'.2) (by ring)⟩

theorem sub (hP : Cone P) (h : Bd P y T) (h' : Bd P y' T') : Bd P (y - y') (T + T') :=
  (h.add hP h'.neg).congr (by ring) rfl

/-- A nonnegative element bounds itself. -/
theorem self (hP : Cone P) (h : P T) : Bd P T T :=
  ⟨Cone.of_eq hP.zero (by ring), Cone.of_eq (hP.add h h) (by ring)⟩

/-- `|0| ≤ T` for nonnegative `T`. -/
theorem zero (h : P T) : Bd P 0 T :=
  ⟨Cone.of_eq h (by ring), Cone.of_eq h (by ring)⟩

/-- Multiplication by a nonnegative scalar. -/
theorem smul (hP : Cone P) {c : R} (hc : P c) (h : Bd P y T) : Bd P (c * y) (c * T) :=
  ⟨Cone.of_eq (hP.mul hc h.1) (by ring), Cone.of_eq (hP.mul hc h.2) (by ring)⟩

/-- `|m| ≤ a` and `|y| ≤ T` give `|m y| ≤ a T`. -/
theorem mul (hP : Cone P) {m a : R} (hm : Bd P m a) (h : Bd P y T) : Bd P (m * y) (a * T) :=
  ⟨hP.half (Cone.of_eq (hP.add (hP.mul hm.1 h.2) (hP.mul hm.2 h.1)) (by ring)),
    hP.half (Cone.of_eq (hP.add (hP.mul hm.1 h.1) (hP.mul hm.2 h.2)) (by ring))⟩

theorem half (hP : Cone P) (h : Bd P (2 * y) (2 * T)) : Bd P y T :=
  ⟨hP.half (Cone.of_eq h.1 (by ring)), hP.half (Cone.of_eq h.2 (by ring))⟩

/-- `|y| ≤ 0` gives `y = 0`. -/
theorem eq_zero (hP : Cone P) (h : Bd P y 0) : y = 0 :=
  hP.anti (Cone.of_eq h.2 (by ring)) (Cone.of_eq h.1 (by ring))

theorem sum (hP : Cone P) {ι : Type*} (s : Finset ι) {f g : ι → R} (h : ∀ i ∈ s, Bd P (f i) (g i)) :
    Bd P (∑ i ∈ s, f i) (∑ i ∈ s, g i) :=
  ⟨Cone.of_eq (hP.sum s _ fun i hi => (h i hi).1) (by rw [Finset.sum_sub_distrib]),
    Cone.of_eq (hP.sum s _ fun i hi => (h i hi).2) (by rw [Finset.sum_add_distrib])⟩

end Bd

/-! ## Row-sum bounds of matrices -/

/-- `‖M‖ ≤ A` for the maximum absolute row sum: the entries have majorants whose row sums are at most `A`. -/
def RowBd {d : ℕ} (P : R → Prop) (M : Fin d → Fin d → R) (A : R) : Prop :=
  ∃ a : Fin d → Fin d → R, (∀ i k, Bd P (M i k) (a i k)) ∧ ∀ i, P (A - ∑ k, a i k)

namespace RowBd

variable {P : R → Prop} {d : ℕ} {M : Fin d → Fin d → R} {A : R}

/-- `‖M y‖ ≤ ‖M‖ ‖y‖`: if `‖M‖ ≤ A` and `|y_k| ≤ T` for all `k`, then `|(M y)_i| ≤ A T`. -/
theorem mulVec (hP : Cone P) (hM : RowBd P M A) {y : Fin d → R} {T : R} (hT : P T)
    (hy : ∀ k, Bd P (y k) T) (i : Fin d) : Bd P (∑ k, M i k * y k) (A * T) := by
  obtain ⟨a, ha, hA⟩ := hM
  have h1 : Bd P (∑ k, M i k * y k) (∑ k, a i k * T) :=
    Bd.sum hP _ fun k _ => (ha i k).mul hP (hy k)
  refine h1.mono hP (Cone.of_eq (hP.mul (hA i) hT) ?_)
  rw [← Finset.sum_mul]; ring

/-- A matrix with the bound `0` annihilates every bounded vector. -/
theorem mulVec_zero (hP : Cone P) (hM : RowBd P M 0) {y : Fin d → R} {T : R} (hT : P T)
    (hy : ∀ k, Bd P (y k) T) (i : Fin d) : ∑ k, M i k * y k = 0 :=
  ((hM.mulVec hP hT hy i).congr rfl (zero_mul T)).eq_zero hP

theorem mono (hP : Cone P) (hM : RowBd P M A) {A' : R} (h : P (A' - A)) : RowBd P M A' := by
  obtain ⟨a, ha, hA⟩ := hM
  exact ⟨a, ha, fun i => Cone.of_eq (hP.add (hA i) h) (by ring)⟩

end RowBd

/-! ## Linearity of finite dot products -/

section Dot

variable {d : ℕ}

theorem dot_smul (m y : Fin d → R) (s : R) : ∑ k, m k * (s * y k) = s * ∑ k, m k * y k := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_cross (m x w : Fin d → R) (q D : R) :
    ∑ k, m k * (x k * q - w k * D) = q * ∑ k, m k * x k - D * ∑ k, m k * w k := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_comb (m m' y : Fin d → R) (c b : R) :
    ∑ k, (c * m k - b * m' k) * y k = c * ∑ k, m k * y k - b * ∑ k, m' k * y k := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_add (m y z : Fin d → R) (c b : R) :
    ∑ k, m k * (c * y k + b * z k) = c * ∑ k, m k * y k + b * ∑ k, m k * z k := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end Dot

end LeanProofs.IPRA.Foundations.SignedCone
