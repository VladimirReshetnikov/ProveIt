import Diophantine.Paper1980.CounterProgram100

/-!
# A single-register Gödel machine simulating a three-counter program

The undecidability of the tag certificate's encoded-instance family is reduced, layer by
layer, from acceptance by a three-counter program (`CProgram.Accepts`, universal by
`TMCounter.accepts_iff` and `TMUniv.re_tm0`).  This first layer is Minsky's arithmetization:
the registers `(a, b, c)` are packed into `N = 2^a 3^b 5^c`, an increment of register `r`
multiplies by the prime `p_r`, and a zero-or-decrement test of `r` is a divisibility test by
`p_r` (divisible exactly when the register is positive, and the quotient is the decremented
packing).  An accepting halt first checks `N = 1`, i.e. all registers zero.

`GProg` machines have multiplications, divisibility tests with two successors and an accepting
halt.  `compile` places location `ℓ` of the counter program at `5ℓ`, its accept check at
`5ℓ + 1, 5ℓ + 2, 5ℓ + 3`, and a looping sink at the end.  `accepts_iff_reachesAcc` is the
equivalence.
-/

namespace Jones1980

/-- An instruction of a single-register machine. -/
inductive GInstr where
  /-- `N := k N`, go to `next`. -/
  | mul (k next : ℕ)
  /-- If `k ∣ N` then `N := N / k` and go to `yes`, else go to `no`. -/
  | div (k yes no : ℕ)
  /-- The accepting halt. -/
  | acc

/-- A single-register machine, entered at location zero. -/
structure GProg where
  /-- The number of locations. -/
  len : ℕ
  /-- The instructions. -/
  code : ℕ → GInstr

namespace GProg

variable (G : GProg)

/-- One step. -/
inductive Step (G : GProg) : ℕ × ℕ → ℕ × ℕ → Prop
  | mul {ℓ k nx N : ℕ} (hℓ : ℓ < G.len) (hc : G.code ℓ = .mul k nx) : Step G (ℓ, N) (nx, k * N)
  | yes {ℓ k y n N : ℕ} (hℓ : ℓ < G.len) (hc : G.code ℓ = .div k y n) (hd : k ∣ N) :
      Step G (ℓ, N) (y, N / k)
  | no {ℓ k y n N : ℕ} (hℓ : ℓ < G.len) (hc : G.code ℓ = .div k y n) (hd : ¬ k ∣ N) :
      Step G (ℓ, N) (n, N)

/-- The machine reaches an accepting halt from the register value `N₀`. -/
def ReachesAcc (N₀ : ℕ) : Prop :=
  ∃ ℓ N, ℓ < G.len ∧ G.code ℓ = .acc ∧ Relation.ReflTransGen G.Step (0, N₀) (ℓ, N)

end GProg

namespace CProgram

variable (M : CProgram)

/-- The prime of a register. -/
def prime3 (r : Fin 3) : ℕ := if r = 0 then 2 else if r = 1 then 3 else 5

/-- The packing `2^a 3^b 5^c`. -/
def pack (v : Fin 3 → ℕ) : ℕ := 2 ^ v 0 * 3 ^ v 1 * 5 ^ v 2

/-- The looping sink. -/
def sink : ℕ := 5 * M.len

/-- The compiled single-register machine. -/
def compile : GProg where
  len := 5 * M.len + 1
  code := fun ℓ' =>
    if ℓ' < 5 * M.len then
      match ℓ' % 5 with
      | 0 => match M.code (ℓ' / 5) with
        | .inc r nx => .mul (prime3 r) (5 * nx)
        | .test r z nz => .div (prime3 r) (5 * nz) (5 * z)
        | .accept => .div 2 (M.sink) (ℓ' + 1)
        | .stop => .mul 2 (M.sink)
      | 1 => match M.code (ℓ' / 5) with
        | .accept => .div 3 (M.sink) (ℓ' + 1)
        | _ => .mul 2 (M.sink)
      | 2 => match M.code (ℓ' / 5) with
        | .accept => .div 5 (M.sink) (ℓ' + 1)
        | _ => .mul 2 (M.sink)
      | 3 => match M.code (ℓ' / 5) with
        | .accept => .acc
        | _ => .mul 2 (M.sink)
      | _ => .mul 2 (M.sink)
    else .mul 2 (M.sink)

theorem pack_pos (v : Fin 3 → ℕ) : 0 < pack v := by unfold pack; positivity

/-- The packing without the factor of register `r`. -/
def rest (r : Fin 3) (v : Fin 3 → ℕ) : ℕ :=
  if r = 0 then 3 ^ v 1 * 5 ^ v 2 else if r = 1 then 2 ^ v 0 * 5 ^ v 2 else 2 ^ v 0 * 3 ^ v 1

theorem pack_split (r : Fin 3) (v : Fin 3 → ℕ) : pack v = prime3 r ^ v r * rest r v := by
  fin_cases r <;> simp [pack, prime3, rest] <;> ring

theorem not_dvd_rest (r : Fin 3) (v : Fin 3 → ℕ) : ¬ prime3 r ∣ rest r v := by
  fin_cases r
  · show ¬ 2 ∣ 3 ^ v 1 * 5 ^ v 2
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h; norm_num at this
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h; norm_num at this
  · show ¬ 3 ∣ 2 ^ v 0 * 5 ^ v 2
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h; norm_num at this
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h; norm_num at this
  · show ¬ 5 ∣ 2 ^ v 0 * 3 ^ v 1
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h; norm_num at this
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h; norm_num at this

/-- Divisibility by a register's prime detects a positive register. -/
theorem prime_dvd_pack (r : Fin 3) (v : Fin 3 → ℕ) : prime3 r ∣ pack v ↔ v r ≠ 0 := by
  rw [pack_split r]
  constructor
  · intro h hz
    rw [hz, pow_zero, one_mul] at h
    exact not_dvd_rest r v h
  · intro h
    exact Dvd.dvd.mul_right (dvd_pow_self _ h) _

theorem pack_inc (r : Fin 3) (v : Fin 3 → ℕ) :
    pack (Function.update v r (v r + 1)) = prime3 r * pack v := by
  unfold pack prime3
  fin_cases r <;> simp [Function.update_apply, pow_succ] <;> ring

theorem pack_dec (r : Fin 3) (v : Fin 3 → ℕ) (h : v r ≠ 0) :
    pack (Function.update v r (v r - 1)) = pack v / prime3 r := by
  have hp : 0 < prime3 r := by unfold prime3; split_ifs <;> norm_num
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
  have e : v = Function.update (Function.update v r (v r - 1)) r (Function.update v r (v r - 1) r + 1) := by
    funext i
    by_cases hi : i = r
    · subst hi; simp; omega
    · simp [Function.update_of_ne hi]
  conv_rhs => rw [e, pack_inc]
  rw [Nat.mul_div_cancel_left _ hp]

theorem pack_zero : pack (fun _ => 0) = 1 := by simp [pack]

theorem pack_start (x : ℕ) : pack (start x) = 2 ^ x := by simp [pack, start]

theorem code_base {ℓ : ℕ} (hℓ : ℓ < M.len) :
    (M.compile).code (5 * ℓ) = match M.code ℓ with
      | .inc r nx => .mul (prime3 r) (5 * nx)
      | .test r z nz => .div (prime3 r) (5 * nz) (5 * z)
      | .accept => .div 2 (M.sink) (5 * ℓ + 1)
      | .stop => .mul 2 (M.sink) := by
  show (if 5 * ℓ < 5 * M.len then _ else _) = _
  rw [if_pos (by omega), show 5 * ℓ % 5 = 0 by omega, show 5 * ℓ / 5 = ℓ by omega]
  rfl

theorem code_inc {ℓ : ℕ} {r : Fin 3} {nx : ℕ} (hℓ : ℓ < M.len) (hc : M.code ℓ = .inc r nx) :
    (M.compile).code (5 * ℓ) = .mul (prime3 r) (5 * nx) := by
  rw [M.code_base hℓ, hc]

theorem code_test {ℓ : ℕ} {r : Fin 3} {z nz : ℕ} (hℓ : ℓ < M.len)
    (hc : M.code ℓ = .test r z nz) :
    (M.compile).code (5 * ℓ) = .div (prime3 r) (5 * nz) (5 * z) := by
  rw [M.code_base hℓ, hc]

theorem code_accept {ℓ : ℕ} (hℓ : ℓ < M.len) (hc : M.code ℓ = .accept) :
    (M.compile).code (5 * ℓ) = .div 2 (M.sink) (5 * ℓ + 1) := by
  rw [M.code_base hℓ, hc]

theorem code_stop {ℓ : ℕ} (hℓ : ℓ < M.len) (hc : M.code ℓ = .stop) :
    (M.compile).code (5 * ℓ) = .mul 2 (M.sink) := by
  rw [M.code_base hℓ, hc]

theorem code_acc1 {ℓ : ℕ} (hℓ : ℓ < M.len) (hc : M.code ℓ = .accept) :
    (M.compile).code (5 * ℓ + 1) = .div 3 (M.sink) (5 * ℓ + 2) := by
  show (if 5 * ℓ + 1 < 5 * M.len then _ else _) = _
  rw [if_pos (by omega), show (5 * ℓ + 1) % 5 = 1 by omega, show (5 * ℓ + 1) / 5 = ℓ by omega]
  show (match M.code ℓ with | .accept => _ | _ => _) = _
  rw [hc]

theorem code_acc2 {ℓ : ℕ} (hℓ : ℓ < M.len) (hc : M.code ℓ = .accept) :
    (M.compile).code (5 * ℓ + 2) = .div 5 (M.sink) (5 * ℓ + 3) := by
  show (if 5 * ℓ + 2 < 5 * M.len then _ else _) = _
  rw [if_pos (by omega), show (5 * ℓ + 2) % 5 = 2 by omega, show (5 * ℓ + 2) / 5 = ℓ by omega]
  show (match M.code ℓ with | .accept => _ | _ => _) = _
  rw [hc]

theorem code_acc3 {ℓ : ℕ} (hℓ : ℓ < M.len) (hc : M.code ℓ = .accept) :
    (M.compile).code (5 * ℓ + 3) = .acc := by
  show (if 5 * ℓ + 3 < 5 * M.len then _ else _) = _
  rw [if_pos (by omega), show (5 * ℓ + 3) % 5 = 3 by omega, show (5 * ℓ + 3) / 5 = ℓ by omega]
  show (match M.code ℓ with | .accept => _ | _ => _) = _
  rw [hc]

theorem code_sink : (M.compile).code M.sink = .mul 2 M.sink := by
  show (if 5 * M.len < 5 * M.len then _ else _) = _
  rw [if_neg (lt_irrefl _)]

theorem step_sink {N : ℕ} {b : ℕ × ℕ} (hs : (M.compile).Step (M.sink, N) b) : b.1 = M.sink := by
  cases hs with
  | mul _ hc => rw [M.code_sink] at hc; cases hc; rfl
  | yes _ hc _ => rw [M.code_sink] at hc; cases hc
  | no _ hc _ => rw [M.code_sink] at hc; cases hc

theorem step_lt {ℓ N : ℕ} {b : ℕ × ℕ} (hs : (M.compile).Step (ℓ, N) b) :
    ℓ < 5 * M.len + 1 := by
  cases hs with
  | mul hl _ => exact hl
  | yes hl _ _ => exact hl
  | no hl _ _ => exact hl

/-- **The Gödel machine reaches its accepting halt exactly when the program accepts.** -/
theorem accepts_iff_reachesAcc (x : ℕ) : M.Accepts x ↔ (M.compile).ReachesAcc (2 ^ x) := by
  constructor
  · rintro ⟨ℓ, hℓ, hc, hr⟩
    -- every program step is a machine step on the packing
    have hsim : ∀ a b, Relation.ReflTransGen M.Step a b →
        Relation.ReflTransGen (M.compile).Step (5 * a.1, pack a.2) (5 * b.1, pack b.2) := by
      intro a b h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hs ih =>
        refine ih.tail ?_
        cases hs with
        | inc hℓ' hc' =>
          rw [pack_inc]
          exact GProg.Step.mul (show _ < 5 * M.len + 1 by omega) (M.code_inc hℓ' hc')
        | zero hℓ' hc' hv =>
          exact GProg.Step.no (show _ < 5 * M.len + 1 by omega) (M.code_test hℓ' hc')
            (by rw [prime_dvd_pack]; exact fun h => h hv)
        | dec hℓ' hc' hv =>
          rw [pack_dec _ _ hv]
          exact GProg.Step.yes (show _ < 5 * M.len + 1 by omega) (M.code_test hℓ' hc')
            ((prime_dvd_pack _ _).2 hv)
    have h1 := hsim _ _ hr
    simp only [Nat.mul_zero, pack_start, pack_zero] at h1
    -- the accept check on `N = 1`
    have ndvd : ∀ k, 2 ≤ k → ¬ k ∣ 1 := fun k hk h => by
      have := Nat.le_of_dvd one_pos h; omega
    have s1 := GProg.Step.no (G := M.compile) (N := 1)
      (show 5 * ℓ < 5 * M.len + 1 by omega) (M.code_accept hℓ hc) (ndvd 2 (by norm_num))
    have s2 := GProg.Step.no (G := M.compile) (N := 1)
      (show 5 * ℓ + 1 < 5 * M.len + 1 by omega) (M.code_acc1 hℓ hc) (ndvd 3 (by norm_num))
    have s3 := GProg.Step.no (G := M.compile) (N := 1)
      (show 5 * ℓ + 2 < 5 * M.len + 1 by omega) (M.code_acc2 hℓ hc) (ndvd 5 (by norm_num))
    exact ⟨5 * ℓ + 3, 1, show _ < 5 * M.len + 1 by omega, M.code_acc3 hℓ hc,
      ((h1.tail s1).tail s2).tail s3⟩
  · rintro ⟨ℓ', N, hℓ', hc', hr⟩
    -- the reachable machine configurations
    let Inv : ℕ × ℕ → Prop := fun c =>
      (∃ ℓ v, Relation.ReflTransGen M.Step (0, start x) (ℓ, v) ∧ c = (5 * ℓ, pack v)) ∨
      (∃ ℓ v i, Relation.ReflTransGen M.Step (0, start x) (ℓ, v) ∧ ℓ < M.len ∧
        M.code ℓ = .accept ∧ 1 ≤ i ∧ i ≤ 3 ∧ c = (5 * ℓ + i, pack v) ∧
        v 0 = 0 ∧ (2 ≤ i → v 1 = 0) ∧ (3 ≤ i → v 2 = 0)) ∨
      c.1 = M.sink
    have hinv : ∀ c, Relation.ReflTransGen (M.compile).Step (0, 2 ^ x) c → Inv c := by
      intro c h
      induction h with
      | refl => exact Or.inl ⟨0, start x, Relation.ReflTransGen.refl, by simp [pack_start]⟩
      | tail _ hs ih =>
        rcases ih with ⟨ℓ, v, hr, rfl⟩ | ⟨ℓ, v, i, hr, hℓ, hc, hi1, hi3, rfl, h0, h1, h2⟩ | hsink
        · have hlt := M.step_lt hs
          by_cases hℓ : ℓ < M.len
          swap
          · have e : 5 * ℓ = M.sink := by unfold sink; omega
            rw [e] at hs
            exact Or.inr (Or.inr (M.step_sink hs))
          cases hcode : M.code ℓ with
          | inc r nx =>
            have e := M.code_inc hℓ hcode
            cases hs with
            | mul _ hc => rw [e] at hc; cases hc
                          exact Or.inl ⟨nx, _, hr.tail (Step.inc hℓ hcode), by rw [pack_inc]⟩
            | yes _ hc _ => rw [e] at hc; cases hc
            | no _ hc _ => rw [e] at hc; cases hc
          | test r z nz =>
            have e := M.code_test hℓ hcode
            cases hs with
            | mul _ hc => rw [e] at hc; cases hc
            | yes _ hc hd =>
              rw [e] at hc; cases hc
              have hv := (prime_dvd_pack _ _).1 hd
              exact Or.inl ⟨nz, _, hr.tail (Step.dec hℓ hcode hv), by rw [pack_dec _ _ hv]⟩
            | no _ hc hd =>
              rw [e] at hc; cases hc
              have hv : v r = 0 := by
                by_contra h; exact hd ((prime_dvd_pack _ _).2 h)
              exact Or.inl ⟨z, v, hr.tail (Step.zero hℓ hcode hv), rfl⟩
          | accept =>
            have e := M.code_accept hℓ hcode
            cases hs with
            | mul _ hc => rw [e] at hc; cases hc
            | yes _ hc _ => rw [e] at hc; cases hc; exact Or.inr (Or.inr rfl)
            | no _ hc hd =>
              rw [e] at hc; cases hc
              have hv : v 0 = 0 := by
                by_contra h; exact hd ((prime_dvd_pack 0 v).2 h)
              exact Or.inr (Or.inl ⟨ℓ, v, 1, hr, hℓ, hcode, le_rfl, by norm_num, rfl,
                hv, fun h => by omega, fun h => by omega⟩)
          | stop =>
            have e := M.code_stop hℓ hcode
            cases hs with
            | mul _ hc => rw [e] at hc; cases hc; exact Or.inr (Or.inr rfl)
            | yes _ hc _ => rw [e] at hc; cases hc
            | no _ hc _ => rw [e] at hc; cases hc
        · rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
          · have e := M.code_acc1 hℓ hc
            cases hs with
            | mul _ hc' => rw [e] at hc'; cases hc'
            | yes _ hc' _ => rw [e] at hc'; cases hc'; exact Or.inr (Or.inr rfl)
            | no _ hc' hd =>
              rw [e] at hc'; cases hc'
              have hv : v 1 = 0 := by
                by_contra h; exact hd ((prime_dvd_pack 1 v).2 h)
              exact Or.inr (Or.inl ⟨ℓ, v, 2, hr, hℓ, hc, by norm_num, by norm_num, rfl,
                h0, fun _ => hv, fun h => by omega⟩)
          · have e := M.code_acc2 hℓ hc
            cases hs with
            | mul _ hc' => rw [e] at hc'; cases hc'
            | yes _ hc' _ => rw [e] at hc'; cases hc'; exact Or.inr (Or.inr rfl)
            | no _ hc' hd =>
              rw [e] at hc'; cases hc'
              have hv : v 2 = 0 := by
                by_contra h; exact hd ((prime_dvd_pack 2 v).2 h)
              exact Or.inr (Or.inl ⟨ℓ, v, 3, hr, hℓ, hc, by norm_num, le_rfl, rfl,
                h0, fun _ => h1 (by norm_num), fun _ => hv⟩)
          · have e := M.code_acc3 hℓ hc
            cases hs with
            | mul _ hc' => rw [e] at hc'; cases hc'
            | yes _ hc' _ => rw [e] at hc'; cases hc'
            | no _ hc' _ => rw [e] at hc'; cases hc'
        · rename_i b0 _ _
          obtain ⟨ℓ0, N0⟩ := b0
          simp only at hsink
          subst hsink
          exact Or.inr (Or.inr (M.step_sink hs))
    have hlt : ℓ' < 5 * M.len + 1 := hℓ'
    rcases hinv _ hr with ⟨ℓ, v, _, he⟩ | ⟨ℓ, v, i, hrM, hℓ, hc, hi1, hi3, he, h0, h1, h2⟩ | hsink
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      by_cases hℓ : ℓ < M.len
      · cases hm : M.code ℓ with
        | inc r nx => rw [M.code_inc hℓ hm] at hc'; cases hc'
        | test r z nz => rw [M.code_test hℓ hm] at hc'; cases hc'
        | accept => rw [M.code_accept hℓ hm] at hc'; cases hc'
        | stop => rw [M.code_stop hℓ hm] at hc'; cases hc'
      · have e : 5 * ℓ = M.sink := by unfold sink; omega
        rw [e, M.code_sink] at hc'
        cases hc'
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
      · rw [M.code_acc1 hℓ hc] at hc'; cases hc'
      · rw [M.code_acc2 hℓ hc] at hc'; cases hc'
      · have hv : v = fun _ => 0 := by
          funext j; fin_cases j
          · exact h0
          · exact h1 (by norm_num)
          · exact h2 le_rfl
        exact ⟨ℓ, hℓ, hc, hv ▸ hrM⟩
    · simp only at hsink
      rw [hsink, M.code_sink] at hc'
      cases hc'

end CProgram

end Jones1980
