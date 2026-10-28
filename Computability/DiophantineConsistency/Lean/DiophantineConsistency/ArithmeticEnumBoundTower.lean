import BusyBeaver.ZFC.ArithmeticTemplates254
import BusyBeaver.ZFC.ArithmeticProofConstructors222

/-! # A two-level exponential tower closed under the C222 code constructors

`tower j n = 2^(2^(j+n))` with an internal base level `j` and a standard
offset `n`. Squaring raises the offset by one, so every fixed-depth
composition of Cantor pairing, tagged formula codes, base-12 proof nodes and
template circuits raises the offset by a standard amount. These are bound
lemmas only; no run, checker or halting statement is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumBoundTower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCode254

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The explicit elementary bound `2^(2^(j+n))`. -/
noncomputable def tower (j : V) (n : ℕ) : V := Exp.exp (Exp.exp (j + n))

theorem tower_succ (j : V) (n : ℕ) : tower j (n+1) = tower j n * tower j n := by
  unfold tower
  rw [Nat.cast_succ, ← add_assoc, exp_succ, exp_even, sq]

theorem tower_mono (j : V) {n m : ℕ} (h : n ≤ m) : tower j n ≤ tower j m := by
  unfold tower
  apply exp_monotone_le.mpr
  apply exp_monotone_le.mpr
  exact _root_.add_le_add le_rfl (Nat.mono_cast h)

theorem le_tower_of {x j : V} {n m : ℕ} (hx : x ≤ tower j n) (h : n ≤ m) :
    x ≤ tower j m := le_trans hx (tower_mono j h)

theorem tower_base_mono {j k : V} (h : j ≤ k) (n : ℕ) : tower j n ≤ tower k n := by
  unfold tower
  apply exp_monotone_le.mpr
  apply exp_monotone_le.mpr
  exact _root_.add_le_add h le_rfl

theorem two_le_tower (j : V) : 2 ≤ tower j 0 := by
  unfold tower
  have h : Exp.exp (1 : V) ≤ Exp.exp (Exp.exp (j + ((0 : ℕ) : V))) :=
    exp_monotone_le.mpr (one_le_exp _)
  simpa only [exp_one] using h

theorem sq_ge {a b : V} (ha : b ≤ a) : b * b ≤ a * a :=
  mul_le_mul ha ha (Arithmetic.zero_le b) (Arithmetic.zero_le a)

theorem four_le_tower (j : V) : 4 ≤ tower j 1 := by
  rw [tower_succ]
  have h := sq_ge (two_le_tower j)
  have h4 : (2 : V) * 2 = 4 := by norm_num
  rwa [h4] at h

theorem sixteen_le_tower (j : V) : 16 ≤ tower j 2 := by
  rw [tower_succ]
  have h := sq_ge (four_le_tower j)
  have h16 : (4 : V) * 4 = 16 := by norm_num
  rwa [h16] at h

theorem sixteen_le_tower_of (j : V) {n : ℕ} (hn : 2 ≤ n) : 16 ≤ tower j n :=
  le_trans (sixteen_le_tower j) (tower_mono j hn)

theorem one_le_tower (j : V) (n : ℕ) : 1 ≤ tower j n :=
  le_trans (by norm_num : (1 : V) ≤ 2) (le_trans (two_le_tower j) (tower_mono j (Nat.zero_le n)))

/-- `c * T ≤ T * T` once the fixed coefficient is below the tower value. -/
theorem mul_le_sq {c T : V} (h : c ≤ T) : c * T ≤ T * T :=
  mul_le_mul_of_nonneg_right h (Arithmetic.zero_le T)

theorem numeral_le_tower (j : V) {n : ℕ} (hn : 2 ≤ n) {c : V} (hc : c ≤ 16) :
    c ≤ tower j n := le_trans hc (sixteen_le_tower_of j hn)

theorem add_le_tower {x y j : V} {n : ℕ} (hn : 2 ≤ n)
    (hx : x ≤ tower j n) (hy : y ≤ tower j n) : x + y + 1 ≤ tower j (n+1) := by
  set T := tower j n
  have h16 : 16 ≤ T := sixteen_le_tower_of j hn
  have h1 : (1 : V) ≤ T := le_trans (by norm_num) h16
  have h3 : x + y + 1 ≤ 3 * T := by
    have := _root_.add_le_add (_root_.add_le_add hx hy) h1
    calc x + y + 1 ≤ T + T + T := this
      _ = 3 * T := by ring
  rw [tower_succ]
  exact le_trans h3 (mul_le_sq (le_trans (by norm_num) h16))

theorem add_le_tower' {x y j : V} {n : ℕ} (hn : 2 ≤ n)
    (hx : x ≤ tower j n) (hy : y ≤ tower j n) : x + y ≤ tower j (n+1) :=
  le_trans le_self_add (add_le_tower hn hx hy)

theorem succ_le_tower {x j : V} {n : ℕ} (hn : 2 ≤ n) (hx : x ≤ tower j n) :
    x + 1 ≤ tower j (n+1) := by
  simpa only [add_zero] using add_le_tower hn hx (Arithmetic.zero_le (tower j n))

theorem cantor_le_tower {x y j : V} {n : ℕ} (hn : 2 ≤ n)
    (hx : x ≤ tower j n) (hy : y ≤ tower j n) : cantor x y ≤ tower j (n+2) := by
  have hs := add_le_tower hn hx hy
  have hc : cantor x y ≤ (x + y + 1) * (x + y + 1) := by
    refine le_trans (cantor_polybound x y) ?_
    have he : (x + y + 1) * (x + y + 1) = (x + y) * (x + y + 1) + (x + y + 1) := by ring
    rw [he]
    refine _root_.add_le_add le_rfl ?_
    calc y ≤ x + y := le_add_self
      _ ≤ x + y + 1 := le_self_add
  rw [tower_succ j (n+1)]
  exact le_trans hc (sq_ge hs)

theorem tagged_le_tower {k x y j : V} {n : ℕ} (hn : 2 ≤ n) (hk : k ≤ 3)
    (hx : x ≤ tower j n) (hy : y ≤ tower j n) : tagged k x y ≤ tower j (n+3) := by
  have hc := cantor_le_tower hn hx hy
  set C := tower j (n+2)
  have h16 : 16 ≤ C := sixteen_le_tower_of j (by omega)
  have h4 : tagged k x y ≤ 5 * C := by
    unfold tagged
    calc 4 * cantor x y + k ≤ 4 * C + C :=
          _root_.add_le_add (mul_le_mul_of_nonneg_left hc (Arithmetic.zero_le 4))
            (le_trans hk (le_trans (by norm_num) h16))
      _ = 5 * C := by ring
  rw [tower_succ j (n+2)]
  exact le_trans h4 (mul_le_sq (le_trans (by norm_num) h16))

theorem node_le_tower {t p j : V} {n : ℕ} (hn : 2 ≤ n) (ht : t ≤ 11)
    (hp : p ≤ tower j n) : ArithmeticProofConstructors222.node t p ≤ tower j (n+1) := by
  set T := tower j n
  have h16 : 16 ≤ T := sixteen_le_tower_of j hn
  have h13 : ArithmeticProofConstructors222.node t p ≤ 13 * T := by
    unfold ArithmeticProofConstructors222.node
    have ht1 : t + 1 ≤ T := le_trans (_root_.add_le_add ht le_rfl)
      (le_trans (by norm_num) h16)
    calc 12 * p + t + 1 = 12 * p + (t + 1) := by ring
      _ ≤ 12 * T + T := _root_.add_le_add
          (mul_le_mul_of_nonneg_left hp (Arithmetic.zero_le 12)) ht1
      _ = 13 * T := by ring
  rw [tower_succ]
  exact le_trans h13 (mul_le_sq (le_trans (by norm_num) h16))

/-! ## Template circuits -/

open ArithmeticTemplates254 in
/-- Standard depth of a fixed template circuit. -/
def depth : Circuit → ℕ
  | .node _ x y => max (depth x) (depth y) + 1
  | _ => 0

open ArithmeticTemplates254 in
theorem tag_value_le (k : Tag) : (k.value : V) ≤ 3 := by
  cases k <;> norm_num [Tag.value]

open ArithmeticTemplates254 in
/-- Each circuit level costs three tower offsets. -/
theorem eval_le_tower (e : Circuit) {a b c u j : V} {n : ℕ} (hn : 2 ≤ n)
    (ha : a ≤ tower j n) (hb : b ≤ tower j n) (hc : c ≤ tower j n) (hu : u ≤ tower j n) :
    e.eval a b c u ≤ tower j (n + 3 * depth e) := by
  induction e with
  | input0 => simpa [depth] using ha
  | input1 => simpa [depth] using hb
  | input2 => simpa [depth] using hc
  | input3 => simpa [depth] using hu
  | one => simpa [depth, Circuit.eval] using numeral_le_tower j hn (by norm_num : (1 : V) ≤ 16)
  | node k x y ihx ihy =>
    have hx := le_tower_of ihx (show n + 3 * depth x ≤ n + 3 * max (depth x) (depth y) by
      have := le_max_left (depth x) (depth y); omega)
    have hy := le_tower_of ihy (show n + 3 * depth y ≤ n + 3 * max (depth x) (depth y) by
      have := le_max_right (depth x) (depth y); omega)
    have h := tagged_le_tower (by omega) (tag_value_le k) hx hy
    have he : n + 3 * max (depth x) (depth y) + 3 = n + 3 * depth (.node k x y) := by
      simp only [depth]; ring
    rw [← he]
    exact h

end DiophantineConsistency.ArithmeticEnumBoundTower
