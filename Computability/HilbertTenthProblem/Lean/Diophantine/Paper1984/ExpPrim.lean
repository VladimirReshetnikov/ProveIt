import Diophantine.Paper1984.ExpDioph
import Diophantine.Paper1984.Identities
import Diophantine.Paper1984.Masking

/-!
# Jones–Matijasevič 1984, §2: the basic relations are singlefold unary exponential Diophantine

* (3) order: `a < b ↔ ∃ x, a + x + 1 = b` and `a ≤ b ↔ ∃ x, a + x = b`;
* (9) two-place exponentials by one-place ones: for `y ≥ 2`,
  `z = x^y ↔ ∃ d e w, d + x = 2^{xy}, 2^{xy²} = e d + z, z + w + 1 = d`;
* (8), Lucas' lemma and (13): `a ≼ b` via the base-`u` digits of `(u+1)^N`,
  `u = 2^N + 1`, `N = 4b + 3`, `K = 4a + 3`, requiring `C(N, K)` odd.

Every representation is singlefold: its unknowns are determined by the parameters.
-/

namespace JM1984
namespace Exp

open UTerm

namespace SFU

variable {α : Type}

/-- Lifting a parameter term past `k` unknowns. -/
def lift {k : ℕ} (t : UTerm α) : UTerm (α ⊕ Fin k) := t.subst fun i => var (Sum.inl i)

/-- The `j`-th unknown. -/
def unk {k : ℕ} (j : Fin k) : UTerm (α ⊕ Fin k) := var (Sum.inr j)

@[simp] theorem eval_lift {k : ℕ} (t : UTerm α) (a : α → ℕ) (y : Fin k → ℕ) :
    (lift t : UTerm (α ⊕ Fin k)).eval (join a y) = t.eval a := by
  simp [lift, eval_subst, join]

@[simp] theorem eval_unk {k : ℕ} (j : Fin k) (a : α → ℕ) (y : Fin k → ℕ) :
    (unk j : UTerm (α ⊕ Fin k)).eval (join a y) = y j := rfl

/-- A representation given directly by a list of equations. -/
theorem of_holds {k : ℕ} (E : List (UTerm (α ⊕ Fin k) × UTerm (α ⊕ Fin k)))
    {S : (α → ℕ) → Prop} (hS : ∀ a, S a ↔ ∃ y, Holds E (join a y))
    (hu : ∀ a y z, Holds E (join a y) → Holds E (join a z) → y = z) : SFU S :=
  ⟨k, E, fun a => ⟨hS a, hu a⟩⟩

theorem holds_cons {ι : Type} (e : UTerm ι × UTerm ι) (E : List (UTerm ι × UTerm ι)) (v : ι → ℕ) :
    Holds (e :: E) v ↔ e.1.eval v = e.2.eval v ∧ Holds E v := by
  simp [Holds]

theorem holds_nil {ι : Type} (v : ι → ℕ) : Holds ([] : List (UTerm ι × UTerm ι)) v := by
  simp [Holds]

/-- `s < t`. -/
theorem lt (s t : UTerm α) : SFU (fun a => s.eval a < t.eval a) := by
  refine of_holds (k := 1) [(lift s + unk 0 + const 1, lift t)] (fun a => ?_) (fun a y z hy hz => ?_)
  · simp only [holds_cons, holds_nil, and_true, eval_add', eval_lift, eval_unk, eval_const]
    exact ⟨fun h => ⟨fun _ => t.eval a - s.eval a - 1, by simp; omega⟩, fun ⟨y, hy⟩ => by omega⟩
  · simp only [holds_cons, holds_nil, and_true, eval_add', eval_lift, eval_unk, eval_const] at hy hz
    funext j; fin_cases j; simp only [Fin.zero_eta]; omega

/-- `s ≤ t`. -/
theorem le (s t : UTerm α) : SFU (fun a => s.eval a ≤ t.eval a) := by
  refine of_holds (k := 1) [(lift s + unk 0, lift t)] (fun a => ?_) (fun a y z hy hz => ?_)
  · simp only [holds_cons, holds_nil, and_true, eval_add', eval_lift, eval_unk]
    exact ⟨fun h => ⟨fun _ => t.eval a - s.eval a, by simp; omega⟩, fun ⟨y, hy⟩ => by omega⟩
  · simp only [holds_cons, holds_nil, and_true, eval_add', eval_lift, eval_unk] at hy hz
    funext j; fin_cases j; simp only [Fin.zero_eta]; omega

/-- Two-place powers with exponent at least two, by one-place powers ((9)). -/
theorem pow (x y z : UTerm α) : SFU (fun a => 2 ≤ y.eval a ∧ z.eval a = x.eval a ^ y.eval a) := by
  let X : UTerm (α ⊕ Fin 4) := lift x
  let Y : UTerm (α ⊕ Fin 4) := lift y
  let Z : UTerm (α ⊕ Fin 4) := lift z
  refine of_holds (k := 4) [(Y, unk 0 + const 2), (unk 1 + X, pow2 (X * Y)),
    (pow2 (X * Y * Y), unk 2 * unk 1 + Z), (Z + unk 3 + const 1, unk 1)] (fun a => ?_)
    (fun a p q hp hq => ?_)
  · simp only [X, Y, Z, holds_cons, holds_nil, and_true, eval_add', eval_mul', eval_pow2, eval_lift,
      eval_unk, eval_const]
    set xv := x.eval a
    set yv := y.eval a
    set zv := z.eval a
    constructor
    · rintro ⟨hy, hz⟩
      rw [hz]
      have hx : xv < 2 ^ (xv * yv) := by
        calc xv < 2 ^ xv := Nat.lt_two_pow_self
          _ ≤ 2 ^ (xv * yv) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
      set d := 2 ^ (xv * yv) - xv
      have hd : 0 < d := by omega
      have hrem := rem_two_pow_eq_pow (x := xv) (y := yv) (by omega)
      have hlt : xv ^ yv < d := by rw [← hrem]; exact Nat.mod_lt _ hd
      refine ⟨![yv - 2, d, 2 ^ (xv * yv * yv) / d, d - xv ^ yv - 1], ?_⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [← hrem, show xv * yv ^ 2 = xv * yv * yv by ring]
      exact (Nat.div_add_mod' _ _).symm
    · rintro ⟨p, h0, h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      have hd : p 1 = 2 ^ (xv * yv) - xv := by omega
      have hrem := rem_two_pow_eq_pow (x := xv) (y := yv) (by omega)
      rw [← hd, show xv * yv ^ 2 = xv * yv * yv by ring, h2] at hrem
      rw [← hrem, Nat.mul_add_mod_of_lt (by omega)]
  · simp only [X, Y, Z, holds_cons, holds_nil, and_true, eval_add', eval_mul', eval_pow2, eval_lift,
      eval_unk, eval_const] at hp hq
    obtain ⟨p0, p1, p2, p3⟩ := hp
    obtain ⟨q0, q1, q2, q3⟩ := hq
    have e1 : p 1 = q 1 := by omega
    have e2 : p 2 = q 2 := by
      rw [e1] at p2
      have : p 2 * q 1 = q 2 * q 1 := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    funext j
    fin_cases j <;> simp <;> omega

/-- Shifting a mask by two binary digits. -/
theorem mask_shift (a b : ℕ) : 4 * a + 3 ≼ 4 * b + 3 ↔ a ≼ b := by
  have h := mask_add_pow_two_mul (Q := 4) (a := 3) (b := 3) (c := a) (d := b) ⟨2, rfl⟩
    (by norm_num) (by norm_num)
  rw [show 3 + a * 4 = 4 * a + 3 by ring, show 3 + b * 4 = 4 * b + 3 by ring] at h
  rw [← h]
  simp only [and_iff_right_iff_imp]
  intro _ i hi; exact hi

/-- A list of equations without unknowns. -/
theorem eqs (E : List (UTerm α × UTerm α)) : SFU (fun a => Holds E a) := by
  refine ⟨0, E.map (fun e => (e.1.subst fun i => var (Sum.inl i), e.2.subst fun i => var (Sum.inl i))),
    fun a => ⟨?_, fun x y _ _ => funext fun i => Fin.elim0 i⟩⟩
  rw [show (∃ x : Fin 0 → ℕ, Holds (E.map (fun e => (e.1.subst fun i => var (Sum.inl i),
      e.2.subst fun i => var (Sum.inl i)))) (join a x)) ↔ Holds E a from by
    simp only [holds_map]
    exact ⟨fun ⟨x, hx⟩ => by simpa [join] using hx, fun h => ⟨Fin.elim0, by simpa [join] using h⟩⟩]

/-- The masking condition of the binomial digits. -/
theorem choose_odd_unique {N K u : ℕ} (hu : 2 ^ N < u) (hK : K ≤ N) {w v m w' v' m' : ℕ}
    (h : (u + 1) ^ N = w * u ^ (K + 1) + m * u ^ K + v) (hv : v < u ^ K) (hm : m < u)
    (h' : (u + 1) ^ N = w' * u ^ (K + 1) + m' * u ^ K + v') (hv' : v' < u ^ K) (hm' : m' < u) :
    w = w' ∧ v = v' ∧ m = m' := by
  have e1 := choose_eq_of_digits hu hK h hv hm
  have e2 := choose_eq_of_digits hu hK h' hv' hm'
  have hmm : m = m' := e1.trans e2.symm
  subst hmm
  have hpos : 0 < u ^ K := pow_pos (by omega) _
  have k1 := (Nat.div_mod_unique hpos (a := (u + 1) ^ N) (d := w * u + m) (c := v)).2
    ⟨by rw [h, pow_succ]; ring, hv⟩
  have k2 := (Nat.div_mod_unique hpos (a := (u + 1) ^ N) (d := w' * u + m) (c := v')).2
    ⟨by rw [h', pow_succ]; ring, hv'⟩
  have hvv : v = v' := k1.2.symm.trans k2.2
  have hw : w * u = w' * u := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) hw, hvv, rfl⟩

/-- **Masking** `a ≼ b` ((8), Lucas' lemma, (13)). -/
theorem mask (a b : UTerm α) : SFU (fun ev => a.eval ev ≼ b.eval ev) := by
  let A : UTerm (α ⊕ Fin 10) := lift a
  let B : UTerm (α ⊕ Fin 10) := lift b
  let N : UTerm (α ⊕ Fin 10) := const 4 * B + const 3
  let K : UTerm (α ⊕ Fin 10) := const 4 * A + const 3
  let U : UTerm (α ⊕ Fin 10) := pow2 N + const 1
  let E : List (UTerm (α ⊕ Fin 10) × UTerm (α ⊕ Fin 10)) :=
    [(K + unk 0, N), (unk 1, unk 4 * unk 2 + unk 6 * unk 3 + unk 5),
     (unk 5 + unk 8 + const 1, unk 3), (unk 6 + unk 9 + const 1, U),
     (unk 6, const 2 * unk 7 + const 1)]
  let S' : (α ⊕ Fin 10 → ℕ) → Prop := fun v => Holds E v ∧
    (2 ≤ N.eval v ∧ (unk 1).eval v = (U + const 1).eval v ^ N.eval v) ∧
    (2 ≤ (K + const 1).eval v ∧ (unk 2).eval v = U.eval v ^ (K + const 1).eval v) ∧
    (2 ≤ K.eval v ∧ (unk 3).eval v = U.eval v ^ K.eval v)
  have hS' : SFU S' := (eqs E).and ((pow _ _ _).and ((pow _ _ _).and (pow _ _ _)))
  -- the semantics of `S'`
  have sem : ∀ (ev : α → ℕ) (y : Fin 10 → ℕ), S' (join ev y) ↔
      (4 * a.eval ev + 3 + y 0 = 4 * b.eval ev + 3 ∧
        y 1 = y 4 * y 2 + y 6 * y 3 + y 5 ∧ y 5 + y 8 + 1 = y 3 ∧
        y 6 + y 9 + 1 = 2 ^ (4 * b.eval ev + 3) + 1 ∧ y 6 = 2 * y 7 + 1) ∧
      y 1 = (2 ^ (4 * b.eval ev + 3) + 1 + 1) ^ (4 * b.eval ev + 3) ∧
      y 2 = (2 ^ (4 * b.eval ev + 3) + 1) ^ (4 * a.eval ev + 3 + 1) ∧
      y 3 = (2 ^ (4 * b.eval ev + 3) + 1) ^ (4 * a.eval ev + 3) := by
    intro ev y
    simp only [S', E, N, K, U, A, B, holds_cons, holds_nil, and_true, eval_add', eval_mul',
      eval_pow2, eval_lift, eval_unk, eval_const]
    constructor
    · rintro ⟨h1, ⟨-, h2⟩, ⟨-, h3⟩, ⟨-, h4⟩⟩; exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, ⟨by omega, h2⟩, ⟨by omega, h3⟩, ⟨by omega, h4⟩⟩
  have hex := hS'.exists_unique (fun ev y z hy hz => by
    rw [sem] at hy hz
    obtain ⟨⟨a0, a1, a2, a3, a4⟩, b1, b2, b3⟩ := hy
    obtain ⟨⟨c0, c1, c2, c3, c4⟩, d1, d2, d3⟩ := hz
    set bv := 4 * b.eval ev + 3
    set av := 4 * a.eval ev + 3
    have hu : 2 ^ bv < 2 ^ bv + 1 := Nat.lt_succ_self _
    have hK : av ≤ bv := by omega
    have e1 : y 1 = z 1 := by rw [b1, d1]
    have e2 : y 2 = z 2 := by rw [b2, d2]
    have e3 : y 3 = z 3 := by rw [b3, d3]
    obtain ⟨hw, hv, hm⟩ := choose_odd_unique (N := bv) (K := av) hu hK
      (by rw [← b1, ← b2, ← b3]; exact a1) (by rw [← b3]; omega) (by omega)
      (by rw [← d1, ← d2, ← d3]; exact c1) (by rw [← d3]; omega) (by omega)
    funext j
    fin_cases j <;> simp <;> omega)
  refine hex.congr (fun ev => ?_)
  simp only [sem]
  set bv := 4 * b.eval ev + 3 with hbv
  set av := 4 * a.eval ev + 3 with hav
  rw [← mask_shift]
  constructor
  · rintro ⟨y, ⟨a0, a1, a2, a3, a4⟩, b1, b2, b3⟩
    have hu : 2 ^ bv < 2 ^ bv + 1 := Nat.lt_succ_self _
    have hK : av ≤ bv := by omega
    have hm := choose_eq_of_digits hu hK (by rw [← b1, ← b2, ← b3]; exact a1) (by rw [← b3]; omega)
      (by omega)
    rw [mask_iff_choose_odd, ← hm]
    omega
  · intro hmask
    have hK : av ≤ bv := Mask.le hmask
    have hodd : bv.choose av % 2 = 1 := (mask_iff_choose_odd av bv).1 hmask
    have hu : 2 ^ bv < 2 ^ bv + 1 := Nat.lt_succ_self _
    obtain ⟨w, v, hwv, hv⟩ := binomial_digits hu hK
    have hC : bv.choose av < 2 ^ bv + 1 := Nat.lt_succ_of_le (Nat.choose_le_two_pow _ _)
    let y : Fin 10 → ℕ := ![bv - av, (2 ^ bv + 1 + 1) ^ bv, (2 ^ bv + 1) ^ (av + 1),
      (2 ^ bv + 1) ^ av, w, v, bv.choose av, bv.choose av / 2, (2 ^ bv + 1) ^ av - v - 1,
      2 ^ bv + 1 - bv.choose av - 1]
    have y0 : y 0 = bv - av := rfl
    have y1 : y 1 = (2 ^ bv + 1 + 1) ^ bv := rfl
    have y2 : y 2 = (2 ^ bv + 1) ^ (av + 1) := rfl
    have y3 : y 3 = (2 ^ bv + 1) ^ av := rfl
    have y4 : y 4 = w := rfl
    have y5 : y 5 = v := rfl
    have y6 : y 6 = bv.choose av := rfl
    have y7 : y 7 = bv.choose av / 2 := rfl
    have y8 : y 8 = (2 ^ bv + 1) ^ av - v - 1 := rfl
    have y9 : y 9 = 2 ^ bv + 1 - bv.choose av - 1 := rfl
    refine ⟨y, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      simp only [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9] <;>
      first | rfl | exact hwv | omega

end SFU

end Exp
end JM1984
