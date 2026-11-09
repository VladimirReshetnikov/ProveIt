import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! # A kernel-evaluable sparse polynomial arithmetic in four variables

A `Poly` is a list of terms `(m, k)` with a monomial `m = a^e₀ c^e₁ i^e₂ z^e₃` and an integer
coefficient `k`. Addition is a fuelled merge that adds the coefficients of equal monomials (and drops
a zero sum); multiplication merges the products of one factor's terms with the other factor. All
definitions are structural recursions on lists and a natural-number fuel, so `decide +kernel` can
evaluate them on literal data.

Soundness needs no invariant: `ev_add`, `ev_mul`, `ev_sub`, `ev_lit` hold for *every* list
(sortedness only makes the normal form canonical, so that cancellations are found; a missed
cancellation can only make a check fail, never lie).

`pos_of_check`: if `posCheck top M p = true` then `ev p > 0` whenever `a ≥ M`, `a, c, i, z ≥ 1` in
an ordered commutative ring. The check asks that every monomial divides `top`, that every negative
coefficient sits on a monomial of `a`-degree below that of `top`, and that `κ·M + ν > 0`, with `κ`
the coefficient of `top` and `ν` the sum of the negative coefficients; then
`ev p ≥ (κ a + ν) a^{e₀−1} c^{e₁} i^{e₂} z^{e₃}`. -/
set_option autoImplicit false
namespace Nine121.SP4

/-- The monomial `a^e0 * c^e1 * i^e2 * z^e3`. -/
structure Mon where
  e0 : ℕ
  e1 : ℕ
  e2 : ℕ
  e3 : ℕ

def Mon.mul (m n : Mon) : Mon := ⟨m.e0 + n.e0, m.e1 + n.e1, m.e2 + n.e2, m.e3 + n.e3⟩

/-- Lexicographic order (only used to find equal monomials). -/
def Mon.lt (m n : Mon) : Bool :=
  Nat.blt m.e0 n.e0 || (Nat.beq m.e0 n.e0 && (Nat.blt m.e1 n.e1 || (Nat.beq m.e1 n.e1 &&
    (Nat.blt m.e2 n.e2 || (Nat.beq m.e2 n.e2 && Nat.blt m.e3 n.e3)))))

def Mon.beq (m n : Mon) : Bool :=
  Nat.beq m.e0 n.e0 && Nat.beq m.e1 n.e1 && Nat.beq m.e2 n.e2 && Nat.beq m.e3 n.e3

/-- Componentwise divisibility of monomials. -/
def Mon.le (m n : Mon) : Bool :=
  Nat.ble m.e0 n.e0 && Nat.ble m.e1 n.e1 && Nat.ble m.e2 n.e2 && Nat.ble m.e3 n.e3

theorem Mon.eq_of_beq {m n : Mon} (h : m.beq n = true) : m = n := by
  obtain ⟨a, b, c, d⟩ := m
  obtain ⟨a', b', c', d'⟩ := n
  simp only [Mon.beq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  subst h0 h1 h2 h3; rfl

theorem Mon.le_spec {m n : Mon} (h : m.le n = true) :
    m.e0 ≤ n.e0 ∧ m.e1 ≤ n.e1 ∧ m.e2 ≤ n.e2 ∧ m.e3 ≤ n.e3 := by
  simp only [Mon.le, Bool.and_eq_true, Nat.ble_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

def isZ : ℤ → Bool
  | .ofNat n => Nat.beq n 0
  | .negSucc _ => false

theorem isZ_eq {k : ℤ} (h : isZ k = true) : k = 0 := by
  cases k with
  | ofNat n => simp only [isZ, Nat.beq_eq] at h; subst h; rfl
  | negSucc _ => simp [isZ] at h

def isNonneg : ℤ → Bool
  | .ofNat _ => true
  | .negSucc _ => false

theorem nonneg_of_isNonneg {k : ℤ} (h : isNonneg k = true) : 0 ≤ k := by
  cases k with
  | ofNat n => exact Int.natCast_nonneg n
  | negSucc _ => simp [isNonneg] at h

theorem neg_of_not_isNonneg {k : ℤ} (h : isNonneg k = false) : k < 0 := by
  cases k with
  | ofNat n => simp [isNonneg] at h
  | negSucc n => exact Int.negSucc_lt_zero n

def isPos : ℤ → Bool
  | .ofNat n => Nat.blt 0 n
  | .negSucc _ => false

theorem pos_of_isPos {k : ℤ} (h : isPos k = true) : 0 < k := by
  cases k with
  | ofNat n =>
    simp only [isPos, Nat.blt_eq] at h
    show (0 : ℤ) < (n : ℤ)
    exact_mod_cast h
  | negSucc _ => simp [isPos] at h

abbrev Term := Mon × ℤ

/-- One step of the fuelled merge (adds coefficients of equal monomials, drops zero sums), with
the recursive call `ih` as a parameter. -/
def mergeStep (ih : List Term → List Term → List Term) : List Term → List Term → List Term
  | [], q => q
  | s :: p, [] => s :: p
  | s :: p, t :: q =>
    bif s.1.lt t.1 then s :: ih p (t :: q)
    else bif t.1.lt s.1 then t :: ih (s :: p) q
    else bif s.1.beq t.1 then
      (bif isZ (s.2 + t.2) then ih p q else (s.1, s.2 + t.2) :: ih p q)
    else s :: t :: ih p q

/-- The merge, by the bare recursor on the fuel (no `brecOn` tables for the kernel to build). -/
def merge (n : ℕ) : List Term → List Term → List Term :=
  Nat.rec (motive := fun _ => List Term → List Term → List Term) (fun p q => p ++ q)
    (fun _ ih => mergeStep ih) n

theorem merge_zero (p q : List Term) : merge 0 p q = p ++ q := rfl
theorem merge_succ (n : ℕ) (p q : List Term) : merge (n + 1) p q = mergeStep (merge n) p q := rfl

/-- A sparse polynomial. -/
structure Poly where
  terms : List Term

def Poly.add (p q : Poly) : Poly := ⟨merge (p.terms.length + q.terms.length) p.terms q.terms⟩

def Poly.neg (p : Poly) : Poly := ⟨p.terms.map fun t => (t.1, -t.2)⟩

def Poly.sub (p q : Poly) : Poly := p.add q.neg

def mulT (t : Term) (q : List Term) : List Term := q.map fun s => (t.1.mul s.1, t.2 * s.2)

def mulL (q : List Term) (p : List Term) : List Term :=
  List.rec (motive := fun _ => List Term) []
    (fun t _ acc => merge (q.length + acc.length) (mulT t q) acc) p

theorem mulL_nil (q : List Term) : mulL q [] = [] := rfl
theorem mulL_cons (q : List Term) (t : Term) (p : List Term) :
    mulL q (t :: p) = merge (q.length + (mulL q p).length) (mulT t q) (mulL q p) := rfl

def Poly.mul (p q : Poly) : Poly := ⟨mulL q.terms p.terms⟩

def Poly.lit (k : ℤ) : Poly := bif isZ k then ⟨[]⟩ else ⟨[(⟨0, 0, 0, 0⟩, k)]⟩

def X0 : Poly := ⟨[(⟨1, 0, 0, 0⟩, 1)]⟩
def X1 : Poly := ⟨[(⟨0, 1, 0, 0⟩, 1)]⟩
def X2 : Poly := ⟨[(⟨0, 0, 1, 0⟩, 1)]⟩
def X3 : Poly := ⟨[(⟨0, 0, 0, 1⟩, 1)]⟩

/-! ## Evaluation -/

section Eval
variable {R : Type*} [CommRing R] (a c i z : R)

def evM (m : Mon) : R := a ^ m.e0 * c ^ m.e1 * i ^ m.e2 * z ^ m.e3

def evL : List Term → R
  | [] => 0
  | t :: p => (t.2 : R) * evM a c i z t.1 + evL p

def ev (p : Poly) : R := evL a c i z p.terms

theorem evM_mul (m n : Mon) : evM a c i z (m.mul n) = evM a c i z m * evM a c i z n := by
  simp only [evM, Mon.mul, pow_add]; ring

theorem evL_append (p q : List Term) : evL a c i z (p ++ q) = evL a c i z p + evL a c i z q := by
  induction p with
  | nil => simp [evL]
  | cons t p ih => simp only [List.cons_append, evL, ih]; ring

theorem evL_merge : ∀ (n : ℕ) (p q : List Term),
    evL a c i z (merge n p q) = evL a c i z p + evL a c i z q
  | 0, p, q => by simp only [merge_zero, evL_append]
  | _ + 1, [], q => by simp only [merge_succ, mergeStep, evL, zero_add]
  | _ + 1, s :: p, [] => by simp only [merge_succ, mergeStep, evL, add_zero]
  | n + 1, s :: p, t :: q => by
    simp only [merge_succ, mergeStep]
    cases h1 : s.1.lt t.1
    · cases h2 : t.1.lt s.1
      · cases h3 : s.1.beq t.1
        · simp only [cond_false, evL, evL_merge n]; ring
        · have e := Mon.eq_of_beq h3
          cases h4 : isZ (s.2 + t.2)
          · simp only [cond_true, cond_false, evL, evL_merge n, e, Int.cast_add]; ring
          · have hz : ((s.2 + t.2 : ℤ) : R) = 0 := by rw [isZ_eq h4, Int.cast_zero]
            rw [Int.cast_add] at hz
            simp only [cond_true, cond_false, evL, evL_merge n, e]
            linear_combination (-(evM a c i z t.1)) * hz
      · simp only [cond_true, cond_false, evL, evL_merge n]; ring
    · simp only [cond_true, evL, evL_merge n]; ring

theorem ev_add (p q : Poly) : ev a c i z (p.add q) = ev a c i z p + ev a c i z q :=
  evL_merge a c i z _ _ _

theorem ev_neg (p : Poly) : ev a c i z p.neg = -ev a c i z p := by
  obtain ⟨l⟩ := p
  simp only [ev, Poly.neg]
  induction l with
  | nil => simp [evL]
  | cons t l ih => simp only [List.map_cons, evL, ih, Int.cast_neg]; ring

theorem ev_sub (p q : Poly) : ev a c i z (p.sub q) = ev a c i z p - ev a c i z q := by
  rw [Poly.sub, ev_add, ev_neg]; ring

theorem evL_mulT (t : Term) (q : List Term) :
    evL a c i z (mulT t q) = (t.2 : R) * evM a c i z t.1 * evL a c i z q := by
  induction q with
  | nil => simp [mulT, evL]
  | cons s q ih =>
    simp only [mulT, List.map_cons, evL] at ih ⊢
    rw [ih, evM_mul, Int.cast_mul]; ring

theorem evL_mulL (q : List Term) : ∀ p : List Term,
    evL a c i z (mulL q p) = evL a c i z p * evL a c i z q
  | [] => by simp [mulL_nil, evL]
  | t :: p => by
    simp only [mulL_cons, evL_merge, evL_mulT, evL_mulL q p, evL]; ring

theorem ev_mul (p q : Poly) : ev a c i z (p.mul q) = ev a c i z p * ev a c i z q :=
  evL_mulL a c i z _ _

theorem ev_lit (k : ℤ) : ev a c i z (Poly.lit k) = (k : R) := by
  unfold Poly.lit
  cases h : isZ k
  · simp [ev, evL, evM]
  · simp [ev, evL, isZ_eq h]

theorem ev_X0 : ev a c i z X0 = a := by simp [ev, X0, evL, evM]
theorem ev_X1 : ev a c i z X1 = c := by simp [ev, X1, evL, evM]
theorem ev_X2 : ev a c i z X2 = i := by simp [ev, X2, evL, evM]
theorem ev_X3 : ev a c i z X3 = z := by simp [ev, X3, evL, evM]

end Eval

/-! ## A domination positivity certificate -/

/-- Every monomial divides `top`; a negative coefficient needs `a`-degree below `top`'s. -/
def domOk (top : Mon) (t : Term) : Bool :=
  t.1.le top && (t.1.beq top || isNonneg t.2 || Nat.blt t.1.e0 top.e0)

/-- The coefficient of `top`. -/
def topSum (top : Mon) : List Term → ℤ
  | [] => 0
  | t :: p => (bif t.1.beq top then t.2 else 0) + topSum top p

/-- The sum of the negative coefficients off `top`. -/
def negSum (top : Mon) : List Term → ℤ
  | [] => 0
  | t :: p => (bif t.1.beq top then 0 else bif isNonneg t.2 then 0 else t.2) + negSum top p

def posCheck (top : Mon) (M : ℕ) (p : Poly) : Bool :=
  p.terms.all (domOk top) && Nat.ble 1 top.e0 && isPos (topSum top p.terms * M + negSum top p.terms)

theorem negSum_nonpos (top : Mon) : ∀ p : List Term, negSum top p ≤ 0
  | [] => le_refl _
  | t :: p => by
    have ih := negSum_nonpos top p
    simp only [negSum]
    cases h1 : t.1.beq top
    · cases h2 : isNonneg t.2
      · have := neg_of_not_isNonneg h2
        simp only [cond_false]; omega
      · simp only [cond_false, cond_true]; omega
    · simp only [cond_true]; omega

section Order
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem evM_nonneg {a c i z : R} (ha : 0 ≤ a) (hc : 0 ≤ c) (hi : 0 ≤ i) (hz : 0 ≤ z) (m : Mon) :
    0 ≤ evM a c i z m := by
  unfold evM
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hc _)) (pow_nonneg hi _))
    (pow_nonneg hz _)

theorem evM_le {a c i z : R} (ha : 1 ≤ a) (hc : 1 ≤ c) (hi : 1 ≤ i) (hz : 1 ≤ z) {m n : Mon}
    (h0 : m.e0 ≤ n.e0) (h1 : m.e1 ≤ n.e1) (h2 : m.e2 ≤ n.e2) (h3 : m.e3 ≤ n.e3) :
    evM a c i z m ≤ evM a c i z n := by
  unfold evM
  have p0 := pow_le_pow_right₀ ha h0
  have p1 := pow_le_pow_right₀ hc h1
  have p2 := pow_le_pow_right₀ hi h2
  have p3 := pow_le_pow_right₀ hz h3
  have q0 : (0 : R) ≤ a ^ m.e0 := pow_nonneg (by linarith) _
  have q1 : (0 : R) ≤ c ^ m.e1 := pow_nonneg (by linarith) _
  have q2 : (0 : R) ≤ i ^ m.e2 := pow_nonneg (by linarith) _
  have q3 : (0 : R) ≤ z ^ m.e3 := pow_nonneg (by linarith) _
  have r0 : (0 : R) ≤ a ^ n.e0 := le_trans q0 p0
  have r1 : (0 : R) ≤ c ^ n.e1 := le_trans q1 p1
  have r2 : (0 : R) ≤ i ^ n.e2 := le_trans q2 p2
  exact mul_le_mul (mul_le_mul (mul_le_mul p0 p1 q1 r0) p2 q2 (mul_nonneg r0 r1)) p3 q3
    (mul_nonneg (mul_nonneg r0 r1) r2)

/-- The lower bound of `evL` by the top coefficient and the negative coefficients. -/
theorem evL_ge {a c i z : R} (ha : 1 ≤ a) (hc : 1 ≤ c) (hi : 1 ≤ i) (hz : 1 ≤ z) (top : Mon)
    (htop : 1 ≤ top.e0) :
    ∀ p : List Term, p.all (domOk top) = true →
      (topSum top p : R) * a * evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ +
        (negSum top p : R) * evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ ≤ evL a c i z p
  | [], _ => by simp [topSum, negSum, evL]
  | t :: p, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := evL_ge ha hc hi hz top htop p h.2
    set Q := evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ with hQ
    have hQ0 : 0 ≤ Q := evM_nonneg (by linarith) (by linarith) (by linarith) (by linarith) _
    have hd := h.1
    simp only [domOk, Bool.and_eq_true, Bool.or_eq_true] at hd
    obtain ⟨hle, hcase⟩ := hd
    obtain ⟨l0, l1, l2, l3⟩ := Mon.le_spec hle
    -- the per-term bound
    have key : ((bif t.1.beq top then t.2 else 0 : ℤ) : R) * a * Q +
        ((bif t.1.beq top then 0 else bif isNonneg t.2 then 0 else t.2 : ℤ) : R) * Q ≤
          (t.2 : R) * evM a c i z t.1 := by
      cases h1 : t.1.beq top
      · cases h2 : isNonneg t.2
        · -- a negative coefficient below the top `a`-degree
          have hneg := neg_of_not_isNonneg h2
          have hlt : Nat.blt t.1.e0 top.e0 = true := by
            rcases hcase with (h | h) | h
            · rw [h1] at h; exact absurd h (by simp)
            · rw [h2] at h; exact absurd h (by simp)
            · exact h
          rw [Nat.blt_eq] at hlt
          have hm : evM a c i z t.1 ≤ Q :=
            evM_le ha hc hi hz (n := ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩) (by simp only; omega)
              l1 l2 l3
          have hn : (t.2 : R) < 0 := by exact_mod_cast hneg
          simp only [cond_false, Int.cast_zero, zero_mul, zero_add]
          nlinarith
        · have hnn := nonneg_of_isNonneg h2
          have hn : (0 : R) ≤ t.2 := by exact_mod_cast hnn
          simp only [cond_false, cond_true, Int.cast_zero, zero_mul, zero_add]
          exact mul_nonneg hn (evM_nonneg (by linarith) (by linarith) (by linarith) (by linarith) _)
      · have e := Mon.eq_of_beq h1
        simp only [cond_true, Int.cast_zero, zero_mul, add_zero]
        rw [e, hQ]
        have : evM a c i z top = a * evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ := by
          simp only [evM]
          rw [show top.e0 = (top.e0 - 1) + 1 from (Nat.sub_add_cancel htop).symm, pow_succ]
          simp only [Nat.add_sub_cancel]
          ring
        rw [this]; exact le_of_eq (by ring)
    simp only [topSum, negSum, evL, Int.cast_add]
    linarith

/-- **Domination positivity.** -/
theorem pos_of_check (top : Mon) (M : ℕ) (p : Poly) (h : posCheck top M p = true)
    {a c i z : R} (haM : (M : R) ≤ a) (ha : 1 ≤ a) (hc : 1 ≤ c) (hi : 1 ≤ i) (hz : 1 ≤ z) :
    0 < ev a c i z p := by
  simp only [posCheck, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hall, htop⟩, hpos⟩ := h
  have hp := pos_of_isPos hpos
  have hge := evL_ge ha hc hi hz top htop p.terms hall
  set Q := evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    have := evM_le ha hc hi hz (m := ⟨0, 0, 0, 0⟩) (n := ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    simpa [evM] using this
  have hneg := negSum_nonpos top p.terms
  have hκ : 0 < topSum top p.terms := by
    by_contra hk
    have hk : topSum top p.terms ≤ 0 := not_lt.mp hk
    have : topSum top p.terms * (M : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk (Int.natCast_nonneg M)
    omega
  have hκR : (0 : R) < topSum top p.terms := by exact_mod_cast hκ
  have h1 : ((topSum top p.terms * M + negSum top p.terms : ℤ) : R) ≥ 1 := by
    have : (1 : ℤ) ≤ topSum top p.terms * M + negSum top p.terms := hp
    exact_mod_cast this
  push_cast at h1
  have h2 : (topSum top p.terms : R) * M ≤ (topSum top p.terms : R) * a :=
    mul_le_mul_of_nonneg_left haM hκR.le
  have h3 : (1 : R) ≤ (topSum top p.terms : R) * a + negSum top p.terms := by linarith
  have h4 : Q ≤ ((topSum top p.terms : R) * a + negSum top p.terms) * Q :=
    le_mul_of_one_le_left (by linarith) h3
  unfold ev
  nlinarith

end Order

end Nine121.SP4
