import Std

/-!
# Rigidity of the paraboloid digit code

A digit vector has type `Fin k → Nat` with its zeroth digit least significant.
The terminal block of an encoded vector is its sum of squared digits.
Everything below uses Lean's standard library.
-/

namespace DigitRigidity

/-- Pack k low digits in base B, followed by the terminal integer t. -/
def pack (B : Nat) : {k : Nat} → (Fin k → Nat) → Nat → Nat
  | 0, _, t => t
  | _ + 1, u, t => u 0 + B * pack B (fun i => u i.succ) t

def total : {k : Nat} → (Fin k → Nat) → Nat
  | 0, _ => 0
  | _ + 1, u => u 0 + total (fun i => u i.succ)

def squares {k : Nat} (u : Fin k → Nat) := total (fun i => u i ^ 2)

def code {k : Nat} (B : Nat) (u : Fin k → Nat) := pack B u (squares u)

/-- A weighted sum can be represented using weighted low digits and a weighted
terminal block, whether or not the resulting low digits fit in the base. -/
theorem pack_linear {k : Nat} (B a b : Nat) (u w : Fin k → Nat) (s t : Nat) :
    a * pack B u s + b * pack B w t =
    pack B (fun i => a * u i + b * w i) (a*s+b*t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := ih (fun i => u i.succ) (fun i => w i.succ)
    simp only [pack]
    grind

/-- Base decoding gives all the low digits and the terminal block, with no
bound required on the terminal blocks themselves. -/
theorem decode {k B : Nat} (hB : 0 < B) (u w : Fin k → Nat) (s t : Nat)
    (hu : ∀ i, u i < B) (hw : ∀ i, w i < B) (h : pack B u s = pack B w t) :
    u = w ∧ s = t := by
  induction k with
  | zero => exact ⟨funext (fun i => Fin.elim0 i), h⟩
  | succ k ih =>
    change u 0 + B * pack B (fun i => u i.succ) s =
      w 0 + B * pack B (fun i => w i.succ) t at h
    have heads := congrArg (fun x => x % B) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hu 0),
               Nat.mod_eq_of_lt (hw 0)] at heads
    have tails := congrArg (fun x => x / B) h
    simp only [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hu 0),
               Nat.div_eq_of_lt (hw 0), Nat.zero_add] at tails
    obtain ⟨heq, ht⟩ := ih _ _ (fun i => hu i.succ) (fun i => hw i.succ) tails
    exact ⟨funext (Fin.cases heads (fun i => congrFun heq i)), ht⟩

def gap (x y : Nat) := (x-y)^2 + (y-x)^2

private theorem digit_variance (a b x y : Nat) :
    (a+b)*(a*x^2+b*y^2) = (a*x+b*y)^2 + a*b*gap x y := by
  rcases Nat.le_total x y with h | h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [gap, Nat.sub_eq_zero_of_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    grind
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [gap, Nat.sub_eq_zero_of_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    grind

private theorem variance {k : Nat} (a b : Nat) (u w : Fin k → Nat) :
    (a+b)*(a*squares u+b*squares w) =
    squares (fun i => a*u i+b*w i) + a*b*total (fun i => gap (u i) (w i)) := by
  induction k with
  | zero => simp [squares, total]
  | succ k ih =>
    have h := ih (fun i => u i.succ) (fun i => w i.succ)
    have h0 := digit_variance a b (u 0) (w 0)
    simp only [squares, total] at h ⊢
    grind

private theorem squares_scale {k : Nat} (a : Nat) (u : Fin k → Nat) :
    squares (fun i => a * u i) = a^2*squares u := by
  induction k with
  | zero => simp [squares, total]
  | succ k ih =>
    have h := ih (fun i => u i.succ)
    simp only [squares, total] at h ⊢
    grind

private theorem gap_zero {k : Nat} (u w : Fin k → Nat)
    (h : total (fun i => gap (u i) (w i)) = 0) : u = w := by
  induction k with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ k ih =>
    change gap (u 0) (w 0) + total (fun i => gap (u i.succ) (w i.succ)) = 0 at h
    have h0 : gap (u 0) (w 0) = 0 := by omega
    have eq0 : u 0 = w 0 := by
      simp only [gap, Nat.add_eq_zero_iff, Nat.pow_eq_zero] at h0
      omega
    have ht := ih (fun i => u i.succ) (fun i => w i.succ) (by omega)
    exact funext (Fin.cases eq0 (fun i => congrFun ht i))

theorem strict_convexity {k a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (u v w : Fin k → Nat)
    (hd : ∀ i, (a+b)*v i = a*u i+b*w i)
    (hq : (a+b)*squares v = a*squares u+b*squares w) : u = v ∧ v = w := by
  have hv := variance a b u w
  rw [← funext hd, squares_scale, ← hq] at hv
  have hprod : a*b*total (fun i => gap (u i) (w i)) = 0 := by grind
  have ht : total (fun i => gap (u i) (w i)) = 0 := by
    rcases Nat.mul_eq_zero.mp hprod with hab | h
    · have := Nat.mul_pos ha hb
      omega
    · exact h
  have huw := gap_zero u w ht
  subst w
  have huv : v = u := by
    funext i
    apply Nat.eq_of_mul_eq_mul_left (Nat.add_pos_left ha b)
    rw [hd, Nat.add_mul]
  exact ⟨huv.symm, huv⟩


private theorem squares_le {k H : Nat} (u : Fin k → Nat) (hu : ∀ i, u i < H) :
    squares u ≤ k * (H-1)^2 := by
  induction k with
  | zero => simp [squares, total]
  | succ k ih =>
    have h := ih (fun i => u i.succ) (fun i => hu i.succ)
    have h0 := Nat.pow_le_pow_left (show u 0 ≤ H-1 by have := hu 0; omega) 2
    simp only [squares, total] at h ⊢
    rw [Nat.succ_mul]
    omega

private theorem mix_lt_base {a b L H x y : Nat} (hH : 0 < H) (hL : 0 < L)
    (hab : a+b ≤ L) (hx : x < H) (hy : y < H) : a*x+b*y < L*H := by
  have h₁ := Nat.mul_le_mul_left a (show x ≤ H-1 by omega)
  have h₂ := Nat.mul_le_mul_left b (show y ≤ H-1 by omega)
  have h₃ := Nat.mul_le_mul_right (H-1) hab
  rw [Nat.add_mul] at h₃
  have h₄ := Nat.mul_lt_mul_of_pos_left (show H-1 < H by omega) hL
  omega

private theorem pack_bound {k B D t : Nat} (u : Fin k → Nat) (hu : ∀ i, u i < B) (ht : t < D) :
    pack B u t < B^k * D := by
  induction k with
  | zero => simpa [pack] using ht
  | succ k ih =>
    have h := ih (fun i => u i.succ) (fun i => hu i.succ)
    have aux := Nat.mul_le_mul_left B (show pack B (fun i => u i.succ) t + 1 ≤ B^k*D by omega)
    rw [Nat.mul_add, Nat.mul_one] at aux
    rw [pack, Nat.pow_succ]
    have h0 := hu 0
    grind

private theorem mixed_bound {k H L a b : Nat} (hH : 0 < H) (hL : 0 < L)
    (hk : k ≤ L) (hab : a+b ≤ L) (u w : Fin k → Nat)
    (hu : ∀ i, u i < H) (hw : ∀ i, w i < H) :
    a*code (L*H) u + b*code (L*H) w < (L*H)^(k+2) := by
  let B := L*H
  have hlow (i : Fin k) : a*u i+b*w i < B := mix_lt_base hH hL hab (hu i) (hw i)
  have h₁ := Nat.mul_le_mul_left a (squares_le u hu)
  have h₂ := Nat.mul_le_mul_left b (squares_le w hw)
  have h₃ := Nat.mul_le_mul hab hk
  have h₄ := Nat.mul_le_mul_right ((H-1)^2) h₃
  have h₅ := Nat.mul_lt_mul_of_pos_left
    (Nat.pow_lt_pow_left (show H-1 < H by omega) (by decide : 2 ≠ 0))
    (Nat.mul_pos hL hL)
  have hhigh : a*squares u+b*squares w < B^2 := by
    dsimp [B]
    grind
  have bound := pack_bound (fun i => a*u i+b*w i) hlow hhigh
  simp only [code, pack_linear]
  change _ < B^(k+2)
  rw [Nat.pow_add]
  exact bound

/-- Exact rigidity modulo an arbitrary modulus with room for k+2 digits.
The equality at the end is equality of all coordinates. -/
theorem code_rigidity {k H L a b o : Nat} (hH : 0 < H) (hL : 0 < L)
    (hk : k ≤ L) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ L)
    (ho : (L*H)^(k+2) ≤ o) (u v w : Fin k → Nat)
    (hu : ∀ i, u i < H) (hv : ∀ i, v i < H) (hw : ∀ i, w i < H)
    (hc : ((a+b) * code (L*H) v) % o =
           (a*code (L*H) u + b*code (L*H) w) % o) : u = v ∧ v = w := by
  let B := L*H
  have hB : 0 < B := Nat.mul_pos hL hH
  have h₁ := Nat.lt_of_lt_of_le (mixed_bound hH hL hk hab v v hv hv) ho
  have h₂ := Nat.lt_of_lt_of_le (mixed_bound hH hL hk hab u w hu hw) ho
  rw [Nat.add_mul, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hc
  simp only [code, pack_linear] at hc
  have h := decode hB _ _ _ _ (fun i => mix_lt_base hH hL hab (hv i) (hv i))
                              (fun i => mix_lt_base hH hL hab (hu i) (hw i)) hc
  apply strict_convexity ha hb u v w
  · intro i
    simpa only [Nat.add_mul] using congrFun h.1 i
  · simpa only [Nat.add_mul] using h.2

/-- The terminal block contributes exactly B^k times its value. -/
theorem pack_eq_low_add_high {k : Nat} (B : Nat) (u : Fin k → Nat) (s : Nat) :
    pack B u s = pack B u 0 + B^k*s := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    have h := ih (fun i => u i.succ)
    simp only [pack, Nat.pow_succ]
    grind

/-- The low digits alone distinguish the codes of admissible vectors. -/
theorem code_injective {k H L : Nat} (hH : 0 < H) (hL : 0 < L)
    (u v : Fin k → Nat) (hu : ∀ i, u i < H) (hv : ∀ i, v i < H)
    (h : code (L*H) u = code (L*H) v) : u = v := by
  have hbase : H ≤ L*H := by
    have hmul := Nat.mul_le_mul_right H (show 1 ≤ L by omega)
    simpa using hmul
  exact (decode (Nat.mul_pos hL hH) u v _ _ (fun i => Nat.lt_of_lt_of_le (hu i) hbase)
    (fun i => Nat.lt_of_lt_of_le (hv i) hbase) h).1

/-- Each admissible code occupies a representative in the advertised range. -/
theorem code_lt_capacity {k H L : Nat} (hH : 0 < H) (hL : 0 < L) (hk : k ≤ L)
    (u : Fin k → Nat) (hu : ∀ i, u i < H) : code (L*H) u < (L*H)^(k+2) := by
  simpa using mixed_bound (a := 1) (b := 0) hH hL hk (by omega) u u hu hu

end DigitRigidity

#print axioms DigitRigidity.pack_eq_low_add_high
#print axioms DigitRigidity.code_lt_capacity
#print axioms DigitRigidity.code_injective
#print axioms DigitRigidity.decode
#print axioms DigitRigidity.strict_convexity
#print axioms DigitRigidity.code_rigidity
