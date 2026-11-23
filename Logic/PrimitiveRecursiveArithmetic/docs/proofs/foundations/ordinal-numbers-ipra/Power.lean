import OrdinalCore

/-! Executable omega-division and arbitrary-base powers for the same hereditary
Cantor forms as OrdinalCore. The quotient reconstruction theorem uses an
explicit multiplication-by-omega form. Correctness of its identification
with generic multiplication on canonical inputs is checked below. -/
namespace OrdinalPacket
open T

private theorem cmp_ge_trans {x y z : T} (xy : cmp x y ≠ .lt)
    (yz : cmp y z ≠ .lt) : cmp x z ≠ .lt := by
  intro xz
  cases c : cmp x y with
  | lt => exact xy c
  | eq => exact yz ((cmp_eq_iff x y).mp c ▸ xz)
  | gt =>
    have yx : cmp y x = .lt := by rw [cmp_swap, c]; rfl
    exact yz (cmp_trans _ _ _ yx xz)

theorem add_assoc (a b c : T) : add (add a b) c = add a (add b c) := by
  induction a with
  | nil => rfl
  | cons x xs _ ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      cases c with
      | nil => simp
      | cons z zs =>
        by_cases xy : cmp x y = .lt
        · by_cases yz : cmp y z = .lt
          · have xz := cmp_trans _ _ _ xy yz
            simp [add, xy, yz, xz]
          · simp [add, xy, yz]
        · by_cases yz : cmp y z = .lt
          · by_cases xz : cmp x z = .lt <;>
              simp [add, xy, yz, xz] at ih ⊢ <;> exact ih
          · have xz := cmp_ge_trans xy yz
            simp [add, xy, yz, xz] at ih ⊢
            exact ih

/-- The unique d with 1+d=e, for a positive canonical exponent e. -/
def unshift : T → T
  | nil => nil
  | cons nil tail => tail
  | cons (cons a b) t => cons (cons a b) t

/-- An exponent increment by addition on the left. -/
def shift (d : T) : T := add one d

theorem unshift_shift (d : T) : unshift (shift d) = d := by
  cases d with
  | nil => rfl
  | cons h t => cases h <;> rfl

/-- Quotient on the left by omega and natural remainder. -/
def omegaDiv : T → T × Nat
  | nil => (nil, 0)
  | cons h tail =>
    let (q, n) := omegaDiv tail
    match h with
    | nil => (q, n+1)
    | cons x y => (cons (unshift (cons x y)) q, n)

/-- Canonical word for omega*q + n, written directly on exponents. -/
def omegaBlocks : T → Nat → T
  | nil, n => fin n
  | cons h t, n => cons (shift h) (omegaBlocks t n)

@[simp] theorem omegaDiv_fin (n : Nat) : omegaDiv (fin n) = (nil, n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (match omegaDiv (fin n) with | (q, m) => (q, m+1)) = (nil, n+1)
    rw [ih]

theorem omegaDiv_blocks (q : T) (n : Nat) :
    omegaDiv (omegaBlocks q n) = (q, n) := by
  induction q with
  | nil => exact omegaDiv_fin n
  | cons h t _ ih =>
    cases h with
    | nil => simp [omegaBlocks, shift, one, principal, omegaDiv, unshift, ih]
    | cons a b =>
      cases a <;> simp [omegaBlocks, shift, one, principal, add, cmp,
                        omegaDiv, unshift, ih]

private theorem ok_head_tail {h t : T} (p : ok (cons h t) = true) :
    ok h = true ∧ ok t = true := by
  simp only [ok, Bool.and_eq_true] at p
  exact p.1

private theorem zeroHead_fin (t : T) (p : ok (cons nil t) = true) :
    ∃ n, cons nil t = fin n := by
  induction t with
  | nil => exact ⟨1, rfl⟩
  | cons h t _ ih =>
    cases h with
    | nil =>
      obtain ⟨n, hn⟩ := ih (ok_head_tail p).2
      exact ⟨n+1, congrArg (cons nil) hn⟩
    | cons a b => simp [ok, cmp] at p

private theorem shift_unshift_pos (a b : T) (p : ok (cons a b) = true) :
    shift (unshift (cons a b)) = cons a b := by
  cases a with
  | cons x y => rfl
  | nil =>
    cases b with
    | nil => rfl
    | cons c d => cases c with
      | nil => rfl
      | cons x y => simp [ok, cmp] at p

theorem blocks_omegaDiv (b : T) (p : ok b = true) :
    omegaBlocks (omegaDiv b).1 (omegaDiv b).2 = b := by
  induction b with
  | nil => rfl
  | cons h t _ ih =>
    cases h with
    | nil =>
      obtain ⟨n, hn⟩ := zeroHead_fin t p
      rw [hn, omegaDiv_fin]
      rfl
    | cons x y =>
      obtain ⟨hp, tp⟩ := ok_head_tail p
      simpa only [omegaDiv, omegaBlocks, shift_unshift_pos x y hp] using
        congrArg (cons (cons x y)) (ih tp)

theorem shift_cmp (a b : T) : cmp (shift a) (shift b) = cmp a b := by
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons h t => cases h <;> rfl
  | cons a as =>
    cases b with
    | nil => cases a <;> rfl
    | cons b bs => cases a <;> cases b <;> rfl

private theorem omegaBlock_single (a : T) :
    monomialProduct omega a = principal (shift a) := by cases a <;> rfl

private theorem insert_shift (h t : T) (p : ok (cons h t) = true) :
    add (principal (shift h)) (omegaBlocks t 0) =
      cons (shift h) (omegaBlocks t 0) := by
  cases t with
  | nil => rfl
  | cons e t =>
    have he : (cmp h e != .lt) = true := by
      simp only [ok, Bool.and_eq_true] at p
      exact p.2
    simp only [omegaBlocks, principal, add, shift_cmp]
    cases c : cmp h e <;> simp [c] at he ⊢

theorem mul_omega_left (q : T) (p : ok q = true) :
    mul omega q = omegaBlocks q 0 := by
  induction q with
  | nil => rfl
  | cons h t _ ih =>
    rw [mul, omegaBlock_single, ih (ok_head_tail p).2, insert_shift h t p]
    rfl

private theorem add_fin_eq_append (a : T) (n : Nat) :
    add a (fin n) = append a (fin n) := by
  induction a with
  | nil => rfl
  | cons h t _ ih =>
    cases n with
    | zero => simpa [fin, copies, append] using congrArg (cons h) ih
    | succ n =>
      cases h <;> simpa [fin, copies, add, cmp, append] using ih

private theorem append_omegaBlocks_fin (q : T) (n : Nat) :
    append (omegaBlocks q 0) (fin n) = omegaBlocks q n := by
  induction q with
  | nil => rfl
  | cons h t _ ih => exact congrArg (cons (shift h)) ih

theorem omega_mul_add_fin (q : T) (n : Nat) (p : ok q = true) :
    add (mul omega q) (fin n) = omegaBlocks q n := by
  rw [mul_omega_left q p, add_fin_eq_append, append_omegaBlocks_fin]

theorem omegaDiv_mul_add_fin (q : T) (n : Nat) (p : ok q = true) :
    omegaDiv (add (mul omega q) (fin n)) = (q,n) := by
  rw [omega_mul_add_fin q n p, omegaDiv_blocks]

private theorem unshift_ok (a b : T) (p : ok (cons a b) = true) :
    ok (unshift (cons a b)) = true := by
  cases a with
  | nil => exact (ok_head_tail p).2
  | cons x y => exact p

theorem omegaDiv_quot_ok (b : T) (p : ok b = true) :
    ok (omegaDiv b).1 = true := by
  induction b with
  | nil => rfl
  | cons h t _ ih =>
    obtain ⟨hp, tp⟩ := ok_head_tail p
    cases h with
    | nil =>
      obtain ⟨n, hn⟩ := zeroHead_fin t p
      rw [hn, omegaDiv_fin]
      rfl
    | cons a b =>
      change ok (cons (unshift (cons a b)) (omegaDiv t).1) = true
      simp only [ok, Bool.and_eq_true]
      refine ⟨⟨unshift_ok a b hp, ih tp⟩, ?_⟩
      cases t with
      | nil => rfl
      | cons c ts =>
        cases c with
        | nil =>
          obtain ⟨n, hn⟩ := zeroHead_fin ts tp
          rw [hn, omegaDiv_fin]
        | cons x y =>
          change (cmp (unshift (cons a b)) (unshift (cons x y)) != .lt) = true
          rw [← shift_cmp, shift_unshift_pos a b hp,
                           shift_unshift_pos x y (ok_head_tail tp).1]
          simp only [ok, Bool.and_eq_true] at p
          exact p.2

theorem omegaDiv_spec (b : T) (p : ok b = true) :
    add (mul omega (omegaDiv b).1) (fin (omegaDiv b).2) = b := by
  rw [omega_mul_add_fin _ _ (omegaDiv_quot_ok b p), blocks_omegaDiv b p]

def finitePower (a : T) : Nat → T
  | 0 => one
  | n+1 => mul (finitePower a n) a

def growth (a : T) : T :=
  match degree a with
  | nil => one
  | cons x y => mul (cons x y) omega

/-- For a positive quotient use a^omega = omega^growth(a), with the
two exceptional bases handled separately. -/
def power (a b : T) : T :=
  let (q,n) := omegaDiv b
  match q with
  | nil => finitePower a n
  | cons u v =>
    if a = nil then nil else if a = one then one else
      mul (principal (mul (growth a) (cons u v))) (finitePower a n)

@[simp] theorem power_fin (a : T) (n : Nat) :
    power a (fin n) = finitePower a n := by simp [power]

@[simp] theorem power_zero (a : T) : power a nil = one := rfl

theorem power_fin_succ (a : T) (n : Nat) :
    power a (fin (n+1)) = mul (power a (fin n)) a := by
  simp [finitePower]

example : power (fin 2) omega = omega := rfl
example : power (fin 2) (succ omega) = mul omega (fin 2) := rfl
example : power omega (principal omega) = principal (principal omega) := rfl
end OrdinalPacket
