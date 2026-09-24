import Diophantine.Paper1980.TagRound91
import Diophantine.Paper1980.TagEquiv91

/-!
# A binary tag system `0 → 0`, `1 → u` simulating a tag system with deletion `d`

Layer 3 of the undecidability of the encoded tag family (after the track-and-shift idea of
Neary, *Undecidability in binary tag systems and the Post correspondence problem for five pairs
of words*, STACS 2015, Lemma 9).  Letters are `0, …, k − 1`; the deletion number is
`β = d L` with `L = 2k + 2`, and `u` consists of `s` rows of `β` bits, so that reading a copy of
`u` at phase `φ` reads its *track* `φ` (a column of `s` bits).  The binary queue is a sequence of
*tokens* `0` and `u`, and the reading of a token sequence from a phase is `rT`/`pT`: a `u`
emits its track and keeps the phase, a `0` at phase `0` emits `0` and wraps to `β − 1`, any other
`0` lowers the phase.

A letter `x` is encoded `0^{a} u 0^{L−a}` with `a = 2(x + 1)`, and *garbage* items `u` may be
interleaved.  Reading the letters of a group from the letter-boundary phases
`0, β − L, …, L` reads the first letter's `u` at the phase `β − a`, whose track is the encoding
of the production without its first `0` (restored by the wrap) padded by garbage, and every
other `u` at an even phase outside the letter tracks, whose track is garbage.  The halting
letter's track, and every odd track, is all `0`: after it the parity of every later phase is
flipped, every `u` is read at an odd phase and the queue decays to zeros.  With `s` even,
`s ≡ 1 (mod β − 1)` and the initial length `≡ 1 (mod β − 1)`, the first short queue is the single
word `0`.
-/

namespace Jones1980

open TagSys

namespace GTag

variable {α : Type*} (d : ℕ) (P : α → List α)

/-- A segment of a run through long queues. -/
def LSeg (W : List α) (n : ℕ) (W' : List α) : Prop :=
  (step d P)^[n] W = W' ∧ ∀ m < n, d ≤ ((step d P)^[m] W).length

variable {d P} in
theorem LSeg.trans {W W' W'' : List α} {a b : ℕ} (h1 : LSeg d P W a W') (h2 : LSeg d P W' b W'') :
    LSeg d P W (a + b) W'' := by
  refine ⟨by rw [Nat.add_comm, Function.iterate_add_apply, h1.1, h2.1], fun m hm => ?_⟩
  by_cases hma : m < a
  · exact h1.2 m hma
  · obtain ⟨j, rfl⟩ : ∃ j, m = a + j := ⟨m - a, by omega⟩
    rw [Nat.add_comm, Function.iterate_add_apply, h1.1]
    exact h2.2 j (by omega)

end GTag

/-- A tag system with deletion `d` over the letters `0, …, k − 1`, a halting letter and a bound
on the production lengths. -/
structure DTag where
  d : ℕ
  k : ℕ
  H : ℕ
  R : ℕ
  P : ℕ → List ℕ

/-- The admissibility of a `DTag`. -/
structure DTag.Ok (D : DTag) : Prop where
  two_le_d : 2 ≤ D.d
  H_lt : D.H < D.k
  P_ne : ∀ x, D.P x ≠ []
  P_lt : ∀ x, x < D.k → ∀ y ∈ D.P x, y < D.k
  P_len : ∀ x, (D.P x).length ≤ D.R

namespace DTag

open GTag

variable (D : DTag)

/-- The letter width. -/
def L : ℕ := 2 * D.k + 2

/-- The binary deletion number. -/
def β : ℕ := D.d * D.L

/-- The number of rows of `u`: even, `≡ 1 (mod β − 1)`, at least `β` and every track. -/
def s : ℕ := 1 + (2 * D.R * (D.L + 1) + 1) * (D.β - 1)

/-- The encoding of a letter as tokens. -/
def enc (x : ℕ) : List Bool :=
  List.replicate (2 * (x + 1)) false ++ true :: List.replicate (D.L - 2 * (x + 1)) false

/-- The encoding of a word. -/
def encW (w : List ℕ) : List Bool := w.flatMap D.enc

/-- The track at a phase. -/
def track (φ : ℕ) : List Bool :=
  if φ % 2 = 1 then List.replicate D.s false
  else if D.β - 2 * D.k ≤ φ ∧ φ + 2 ≤ D.β then
    (if (D.β - φ) / 2 - 1 = D.H then List.replicate D.s false
     else (D.encW (D.P ((D.β - φ) / 2 - 1))).tail ++
       List.replicate (D.s - ((D.encW (D.P ((D.β - φ) / 2 - 1))).length - 1)) true)
  else List.replicate D.s true

/-- A row of `u`. -/
def row (i : ℕ) : List Bool := (List.range D.β).map (fun φ => (D.track φ).getD i false)

/-- The appendant. -/
def u : List Bool := (List.range D.s).flatMap D.row

/-- The binary tag system. -/
def TS : TagSys := ⟨D.β, D.u⟩

/-- The productions of the binary system. -/
def prodB (b : Bool) : List Bool := if b then D.u else [false]

/-- The bits of a token sequence. -/
def bits (T : List Bool) : List Bool := T.flatMap D.prodB

/-- Reading a token sequence: the emitted tokens. -/
def rT : ℕ → List Bool → List Bool
  | _, [] => []
  | φ, true :: T => D.track φ ++ rT φ T
  | 0, false :: T => false :: rT (D.β - 1) T
  | φ + 1, false :: T => rT φ T

/-- Reading a token sequence: the carried phase. -/
def pT : ℕ → List Bool → ℕ
  | φ, [] => φ
  | φ, true :: T => pT φ T
  | 0, false :: T => pT (D.β - 1) T
  | φ + 1, false :: T => pT φ T

/-! ### Arithmetic of the parameters -/

theorem L_eq : D.L = 2 * D.k + 2 := rfl

theorem two_L_le_β (hD : D.Ok) : 2 * D.L ≤ D.β := by
  unfold β; exact Nat.mul_le_mul_right _ hD.two_le_d

theorem β_even : D.β % 2 = 0 := by
  unfold β L; rw [Nat.mul_mod]; simp [Nat.add_mod]

theorem two_le_β (hD : D.Ok) : 2 ≤ D.β := by have := D.two_L_le_β hD; unfold L at this; omega

theorem β_le_s : D.β ≤ D.s := by
  unfold s
  have : D.β - 1 ≤ (2 * D.R * (D.L + 1) + 1) * (D.β - 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem s_even (hD : D.Ok) : D.s % 2 = 0 := by
  unfold s
  have hb := D.β_even
  have h2 := D.two_le_β hD
  have hodd : (D.β - 1) % 2 = 1 := by omega
  rw [Nat.add_mod, Nat.mul_mod, hodd]
  simp [Nat.add_mod, Nat.mul_mod]

theorem s_modEq : D.s % (D.β - 1) = 1 % (D.β - 1) := by
  unfold s
  rw [Nat.add_mul_mod_self_right]

theorem enc_length {x : ℕ} (hx : x ≤ D.k) : (D.enc x).length = D.L + 1 := by
  simp only [enc, List.length_append, List.length_replicate, List.length_cons, L]
  omega

theorem encW_length (w : List ℕ) (hw : ∀ x ∈ w, x ≤ D.k) :
    (D.encW w).length = w.length * (D.L + 1) := by
  induction w with
  | nil => simp [encW]
  | cons x w ih =>
    have h1 := D.enc_length (hw x List.mem_cons_self)
    have h2 := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    simp only [encW, List.flatMap_cons, List.length_append, List.length_cons] at h2 ⊢
    rw [h1, h2]
    ring

theorem encW_P_le (hD : D.Ok) {x : ℕ} (hx : x < D.k) : (D.encW (D.P x)).length ≤ D.s := by
  rw [D.encW_length _ (fun y hy => le_of_lt (hD.P_lt x hx y hy))]
  have h1 : (D.P x).length * (D.L + 1) ≤ D.R * (D.L + 1) :=
    Nat.mul_le_mul_right _ (hD.P_len x)
  have h2 : D.R * (D.L + 1) ≤ (2 * D.R * (D.L + 1) + 1) * (D.β - 1) := by
    have hb := D.two_le_β hD
    have e : 2 * D.R * (D.L + 1) = 2 * (D.R * (D.L + 1)) := by ring
    have h3 : D.R * (D.L + 1) ≤ 2 * D.R * (D.L + 1) + 1 := by omega
    exact le_trans h3 (Nat.le_mul_of_pos_right _ (by omega))
  unfold s
  omega

theorem track_length (hD : D.Ok) (φ : ℕ) : (D.track φ).length = D.s := by
  unfold track
  split_ifs with h1 h2 h3
  · simp
  · simp
  · have hx : (D.β - φ) / 2 - 1 < D.k := by omega
    have := D.encW_P_le hD hx
    simp only [List.length_append, List.length_tail, List.length_replicate]
    omega
  · simp

theorem getD_map_range (l : List Bool) :
    (List.range l.length).map (fun i => l.getD i false) = l := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp at h1
    simp [List.getD_eq_getElem?_getD, h1]

theorem row_length (i : ℕ) : (D.row i).length = D.β := by simp [row]

theorem reads_u (hD : D.Ok) {φ : ℕ} (hφ : φ < D.β) :
    reads D.β φ D.u = D.track φ ∧ nph D.β φ D.u = φ := by
  obtain ⟨r1, r2⟩ := reads_flatMap D.β (by have := D.two_le_β hD; omega) D.row
    (fun i => (D.track φ).getD i false) hφ D.row_length (fun i => by simp [row, hφ])
    (List.range D.s)
  refine ⟨?_, r2⟩
  rw [u, r1]
  conv_rhs => rw [← getD_map_range (D.track φ)]
  rw [D.track_length hD]

@[simp] theorem rT_nil (φ : ℕ) : D.rT φ [] = [] := by cases φ <;> rfl
@[simp] theorem pT_nil (φ : ℕ) : D.pT φ [] = φ := by cases φ <;> rfl
@[simp] theorem rT_true (φ : ℕ) (T : List Bool) : D.rT φ (true :: T) = D.track φ ++ D.rT φ T := by
  cases φ <;> rfl
@[simp] theorem pT_true (φ : ℕ) (T : List Bool) : D.pT φ (true :: T) = D.pT φ T := by
  cases φ <;> rfl
@[simp] theorem rT_zero_false (T : List Bool) : D.rT 0 (false :: T) = false :: D.rT (D.β - 1) T :=
  rfl
@[simp] theorem pT_zero_false (T : List Bool) : D.pT 0 (false :: T) = D.pT (D.β - 1) T := rfl
@[simp] theorem rT_succ_false (φ : ℕ) (T : List Bool) : D.rT (φ + 1) (false :: T) = D.rT φ T := rfl
@[simp] theorem pT_succ_false (φ : ℕ) (T : List Bool) : D.pT (φ + 1) (false :: T) = D.pT φ T := rfl

theorem rT_append (T T' : List Bool) :
    ∀ φ, D.rT φ (T ++ T') = D.rT φ T ++ D.rT (D.pT φ T) T' ∧ D.pT φ (T ++ T') = D.pT (D.pT φ T) T' := by
  induction T with
  | nil => intro φ; simp
  | cons b T ih =>
    intro φ
    cases b
    · cases φ with
      | zero => simp [ih]
      | succ φ => simp [ih]
    · simp [ih]

theorem bits_cons (b : Bool) (T : List Bool) : D.bits (b :: T) = D.prodB b ++ D.bits T := by
  simp [bits]

theorem bits_append (T T' : List Bool) : D.bits (T ++ T') = D.bits T ++ D.bits T' := by
  simp [bits]

theorem reads_bits (hD : D.Ok) (T : List Bool) : ∀ φ, φ < D.β →
    reads D.β φ (D.bits T) = D.rT φ T ∧ nph D.β φ (D.bits T) = D.pT φ T := by
  have hβ := D.two_le_β hD
  induction T with
  | nil => intro φ _; simp [bits]
  | cons b T ih =>
    intro φ hφ
    rw [bits_cons, reads_append, nph_append]
    cases b
    · cases φ with
      | zero =>
        have e1 : reads D.β 0 (D.prodB false) = [false] := by simp [prodB]
        have e2 : nph D.β 0 (D.prodB false) = D.β - 1 := by simp [prodB]
        rw [e1, e2, (ih _ (by omega)).1, (ih _ (by omega)).2]
        simp
      | succ φ =>
        have e1 : reads D.β (φ + 1) (D.prodB false) = [] := by simp [prodB]
        have e2 : nph D.β (φ + 1) (D.prodB false) = φ := by simp [prodB]
        rw [e1, e2, (ih _ (by omega)).1, (ih _ (by omega)).2]
        simp
    · obtain ⟨e1, e2⟩ := D.reads_u hD hφ
      simp only [prodB, if_true]
      rw [e1, e2, (ih _ hφ).1, (ih _ hφ).2]
      simp

/-- **Reading a token sequence in the binary system.** -/
theorem bin_chunk (hD : D.Ok) (T Y : List Bool) {φ : ℕ} (hφ : φ < D.β) (hY : D.β ≤ Y.length) :
    LSeg D.β D.prodB ((D.bits T ++ Y).drop φ) (D.rT φ T).length
        ((Y ++ D.bits (D.rT φ T)).drop (D.pT φ T)) ∧
      ∀ i (hi : i < (D.rT φ T).length),
        ((step D.β D.prodB)^[i] ((D.bits T ++ Y).drop φ)).head? = some ((D.rT φ T)[i]) := by
  have h := run_chunk D.β D.prodB (by have := D.two_le_β hD; omega) (D.bits T) φ Y hφ hY
  obtain ⟨e1, e2⟩ := D.reads_bits hD T φ hφ
  rw [e1, e2] at h
  exact ⟨⟨h.1, fun m hm => (h.2 m hm).1⟩, fun i hi => (h.2 i hi).2⟩

/-! ### Tracks, zeros and parities -/

theorem u_length : D.u.length = D.s * D.β := by
  simp [u, List.length_flatMap, row_length]

theorem length_le_bits (hD : D.Ok) (T : List Bool) : T.length ≤ (D.bits T).length := by
  have hu : 1 ≤ D.u.length := by
    rw [u_length]; have := D.two_le_β hD; have := D.β_le_s; nlinarith
  induction T with
  | nil => simp [bits]
  | cons b T ih =>
    rw [bits_cons, List.length_append, List.length_cons]
    cases b <;> simp only [prodB, if_true, Bool.false_eq_true, if_false, List.length_singleton] <;>
      omega

theorem β_le_bits_of_true (hD : D.Ok) {T : List Bool} (h : true ∈ T) : D.β ≤ (D.bits T).length := by
  have := GProg.length_le_flatMap D.prodB h
  simp only [prodB, if_true, u_length] at this
  have := D.β_le_s
  have h2 := D.two_le_β hD
  unfold bits
  nlinarith

theorem track_odd {φ : ℕ} (h : φ % 2 = 1) : D.track φ = List.replicate D.s false := by
  simp [track, h]

theorem track_garb {φ : ℕ} (h : φ % 2 = 0) (h2 : φ + 2 * D.k < D.β) :
    D.track φ = List.replicate D.s true := by
  unfold track
  rw [if_neg (by omega), if_neg (by omega)]

theorem track_letter (hD : D.Ok) {x : ℕ} (hx : x < D.k) :
    D.track (D.β - 2 * (x + 1)) = if x = D.H then List.replicate D.s false
      else (D.encW (D.P x)).tail ++
        List.replicate (D.s - ((D.encW (D.P x)).length - 1)) true := by
  have hL := D.two_L_le_β hD
  have hb := D.β_even
  unfold L at hL
  have e : (D.β - (D.β - 2 * (x + 1))) / 2 - 1 = x := by omega
  unfold track
  rw [if_neg (by omega), if_pos (by omega), e]

theorem zeros_le (m : ℕ) : ∀ φ, m ≤ φ →
    D.rT φ (List.replicate m false) = [] ∧ D.pT φ (List.replicate m false) = φ - m := by
  induction m with
  | zero => intro φ _; simp
  | succ m ih =>
    intro φ h
    obtain ⟨φ, rfl⟩ : ∃ φ', φ = φ' + 1 := ⟨φ - 1, by omega⟩
    rw [List.replicate_succ, rT_succ_false, pT_succ_false]
    obtain ⟨h1, h2⟩ := ih φ (by omega)
    exact ⟨h1, by omega⟩

theorem zeros_wrap (hD : D.Ok) {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ D.β) :
    D.rT 0 (List.replicate m false) = [false] ∧ D.pT 0 (List.replicate m false) = D.β - m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.replicate_succ, rT_zero_false, pT_zero_false]
  obtain ⟨e1, e2⟩ := D.zeros_le m (D.β - 1) (by omega)
  exact ⟨by rw [e1], by omega⟩

/-- All bits are `0`. -/
def AF (l : List Bool) : Prop := ∀ b ∈ l, b = false

theorem AF_append {l l' : List Bool} (h : AF l) (h' : AF l') : AF (l ++ l') := by
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact h b hb
  · exact h' b hb

theorem AF_replicate (n : ℕ) : AF (List.replicate n false) := by
  intro b hb; exact (List.mem_replicate.1 hb).2

theorem pT_lt (hD : D.Ok) (T : List Bool) : ∀ φ, φ < D.β → D.pT φ T < D.β := by
  have := D.two_le_β hD
  induction T with
  | nil => intro φ h; simpa using h
  | cons b T ih =>
    intro φ h
    cases b
    · cases φ with
      | zero => rw [pT_zero_false]; exact ih _ (by omega)
      | succ φ => rw [pT_succ_false]; exact ih _ (by omega)
    · rw [pT_true]; exact ih _ h

theorem zeros_parity (hD : D.Ok) (m : ℕ) : ∀ φ, φ < D.β →
    AF (D.rT φ (List.replicate m false)) ∧
      D.pT φ (List.replicate m false) % 2 = (φ + m) % 2 := by
  have hb := D.β_even
  have h2 := D.two_le_β hD
  induction m with
  | zero => intro φ _; simp [AF]
  | succ m ih =>
    intro φ h
    rw [List.replicate_succ]
    cases φ with
    | zero =>
      rw [rT_zero_false, pT_zero_false]
      obtain ⟨a1, a2⟩ := ih (D.β - 1) (by omega)
      refine ⟨fun b hb' => ?_, by omega⟩
      rcases List.mem_cons.1 hb' with rfl | hb'
      · rfl
      · exact a1 b hb'
    | succ φ =>
      rw [rT_succ_false, pT_succ_false]
      obtain ⟨a1, a2⟩ := ih φ (by omega)
      exact ⟨a1, by omega⟩

/-! ### Items -/

/-- The tokens of an item: a letter or a garbage `u`. -/
def itok : Option ℕ → List Bool
  | none => [true]
  | some x => D.enc x

/-- The tokens of an item sequence. -/
def toks (I : List (Option ℕ)) : List Bool := I.flatMap D.itok

/-- The letters of an item sequence. -/
def letters : List (Option ℕ) → List ℕ
  | [] => []
  | none :: I => letters I
  | some x :: I => x :: letters I

/-- The phase at a letter boundary, after `c` letters. -/
def ph (c : ℕ) : ℕ := if c % D.d = 0 then 0 else D.β - c % D.d * D.L

/-- The emission of the letter `x` read as the `c`-th letter. -/
def letE (c x : ℕ) : List Bool :=
  if c % D.d = 0 then false :: D.track (D.β - 2 * (x + 1)) else List.replicate D.s true

/-- The emission of an item sequence read from the boundary after `c` letters. -/
def emT : ℕ → List (Option ℕ) → List Bool
  | _, [] => []
  | c, none :: I => List.replicate D.s true ++ emT c I
  | c, some x :: I => D.letE c x ++ emT (c + 1) I

theorem succ_mod_eq {c d : ℕ} (hd : 1 ≤ d) :
    (c + 1) % d = if c % d + 1 = d then 0 else c % d + 1 := by
  have h := Nat.mod_add_div c d
  have hl := Nat.mod_lt c (show d > 0 by omega)
  split_ifs with he
  · have : c + 1 = d * (c / d + 1) := by rw [Nat.mul_add, mul_one]; omega
    rw [this, Nat.mul_mod_right]
  · have : c + 1 = (c % d + 1) + d * (c / d) := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem ph_lt (hD : D.Ok) (c : ℕ) : D.ph c < D.β := by
  have := D.two_le_β hD
  have hL2 : 2 ≤ D.L := by unfold L; omega
  unfold ph
  split_ifs with h
  · omega
  · have : 1 * D.L ≤ c % D.d * D.L := Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero h)
    omega

theorem ph_even (hD : D.Ok) (c : ℕ) : D.ph c % 2 = 0 := by
  have hb := D.β_even
  unfold ph
  split_ifs with h
  · rfl
  · have hj : c % D.d * D.L ≤ D.β := by
      unfold β; exact Nat.mul_le_mul_right _ (le_of_lt (Nat.mod_lt _ (by have := hD.two_le_d; omega)))
    have he : (c % D.d * D.L) % 2 = 0 := by unfold L; rw [Nat.mul_mod]; simp [Nat.add_mod]
    omega

theorem ph_garb (hD : D.Ok) (c : ℕ) : D.ph c + 2 * D.k < D.β := by
  have hL := D.two_L_le_β hD
  have hLk : D.L = 2 * D.k + 2 := rfl
  unfold ph
  split_ifs with h
  · omega
  · have hpos : 1 ≤ c % D.d := Nat.pos_of_ne_zero h
    have hj : c % D.d * D.L ≤ D.β := by
      unfold β; exact Nat.mul_le_mul_right _ (le_of_lt (Nat.mod_lt _ (by have := hD.two_le_d; omega)))
    have hj1 : D.L ≤ c % D.d * D.L := Nat.le_mul_of_pos_left _ hpos
    omega

/-- Reading one letter from its boundary phase. -/
theorem read_letter (hD : D.Ok) (c : ℕ) {x : ℕ} (hx : x < D.k) :
    D.rT (D.ph c) (D.enc x) = D.letE c x ∧ D.pT (D.ph c) (D.enc x) = D.ph (c + 1) := by
  have hd := hD.two_le_d
  have hL := D.two_L_le_β hD
  have hb := D.β_even
  have hsm := succ_mod_eq (c := c) (show 1 ≤ D.d by omega)
  have hjl := Nat.mod_lt c (show D.d > 0 by omega)
  have henc : D.enc x = List.replicate (2 * (x + 1)) false ++
      (true :: List.replicate (D.L - 2 * (x + 1)) false) := rfl
  rw [henc]
  obtain ⟨a1, a2⟩ := D.rT_append (List.replicate (2 * (x + 1)) false)
    (true :: List.replicate (D.L - 2 * (x + 1)) false) (D.ph c)
  rw [a1, a2]
  have hLk : D.L = 2 * D.k + 2 := rfl
  by_cases hj : c % D.d = 0
  · have hph : D.ph c = 0 := by simp [ph, hj]
    rw [hph]
    obtain ⟨z1, z2⟩ := D.zeros_wrap hD (m := 2 * (x + 1)) (by omega) (by omega)
    rw [z1, z2, rT_true, pT_true]
    obtain ⟨y1, y2⟩ := D.zeros_le (D.L - 2 * (x + 1)) (D.β - 2 * (x + 1)) (by omega)
    rw [y1, y2]
    refine ⟨by simp [letE, hj], ?_⟩
    have h1 : (c + 1) % D.d = 1 := by rw [hsm, hj]; simp; omega
    simp only [ph, h1]
    simp
    omega
  · set j := c % D.d with hjdef
    have hpos : 1 ≤ j := Nat.pos_of_ne_zero hj
    have hjL : j * D.L + D.L ≤ D.β := by
      have : (j + 1) * D.L ≤ D.d * D.L := Nat.mul_le_mul_right _ (by omega)
      unfold β; nlinarith
    have hj1 : D.L ≤ j * D.L := Nat.le_mul_of_pos_left _ hpos
    have hjeven : (j * D.L) % 2 = 0 := by rw [hLk, Nat.mul_mod]; simp [Nat.add_mod]
    have hph : D.ph c = D.β - j * D.L := by simp [ph, ← hjdef, hj]
    rw [hph]
    obtain ⟨z1, z2⟩ := D.zeros_le (2 * (x + 1)) (D.β - j * D.L) (by omega)
    rw [z1, z2, rT_true, pT_true, D.track_garb (by omega) (by omega)]
    obtain ⟨y1, y2⟩ := D.zeros_le (D.L - 2 * (x + 1)) (D.β - j * D.L - 2 * (x + 1)) (by omega)
    rw [y1, y2]
    refine ⟨by simp [letE, ← hjdef, hj], ?_⟩
    by_cases hlast : j + 1 = D.d
    · have h1 : (c + 1) % D.d = 0 := by rw [hsm, if_pos hlast]
      have : j * D.L + D.L = D.β := by
        unfold β; rw [← hlast]; ring
      simp only [ph, h1, if_true]
      omega
    · have h1 : (c + 1) % D.d = j + 1 := by rw [hsm, if_neg hlast]
      have : (j + 1) * D.L = j * D.L + D.L := by ring
      simp only [ph, h1, if_neg (show j + 1 ≠ 0 by omega), this]
      omega

theorem letters_nil : letters [] = [] := rfl
theorem letters_none (I : List (Option ℕ)) : letters (none :: I) = letters I := rfl
theorem letters_some (x : ℕ) (I : List (Option ℕ)) : letters (some x :: I) = x :: letters I := rfl
theorem letters_append (I J : List (Option ℕ)) : letters (I ++ J) = letters I ++ letters J := by
  induction I with
  | nil => rfl
  | cons i I ih => cases i <;> simp [letters, ih]
theorem toks_append (I J : List (Option ℕ)) : D.toks (I ++ J) = D.toks I ++ D.toks J := by
  simp [toks]
theorem toks_cons (i : Option ℕ) (I : List (Option ℕ)) : D.toks (i :: I) = D.itok i ++ D.toks I := by
  simp [toks]

/-- **Reading an item sequence** from a letter boundary. -/
theorem read_items (hD : D.Ok) (I : List (Option ℕ)) (hI : ∀ x ∈ letters I, x < D.k) :
    ∀ c, D.rT (D.ph c) (D.toks I) = D.emT c I ∧
      D.pT (D.ph c) (D.toks I) = D.ph (c + (letters I).length) := by
  induction I with
  | nil => intro c; simp [toks, emT, letters_nil]
  | cons i I ih =>
    intro c
    rw [toks_cons]
    obtain ⟨a1, a2⟩ := D.rT_append (D.itok i) (D.toks I) (D.ph c)
    rw [a1, a2]
    cases i with
    | none =>
      rw [letters_none] at hI ⊢
      have ht : D.rT (D.ph c) (D.itok none) = List.replicate D.s true := by
        simp [itok, D.track_garb (D.ph_even hD c) (D.ph_garb hD c)]
      have hp : D.pT (D.ph c) (D.itok none) = D.ph c := by simp [itok]
      rw [ht, hp, (ih hI c).1, (ih hI c).2]
      exact ⟨rfl, rfl⟩
    | some x =>
      rw [letters_some] at hI ⊢
      have hx := hI x List.mem_cons_self
      have hI' : ∀ y ∈ letters I, y < D.k := fun y hy => hI y (List.mem_cons_of_mem _ hy)
      obtain ⟨r1, r2⟩ := D.read_letter hD c hx
      simp only [itok] at r1 r2 ⊢
      rw [r1, r2, (ih hI' (c + 1)).1, (ih hI' (c + 1)).2]
      refine ⟨rfl, ?_⟩
      simp only [List.length_cons]
      congr 1
      ring

/-! ### One group of letters -/

theorem emT_append (I J : List (Option ℕ)) : ∀ c,
    D.emT c (I ++ J) = D.emT c I ++ D.emT (c + (letters I).length) J := by
  induction I with
  | nil => intro c; simp [emT, letters_nil]
  | cons i I ih =>
    intro c
    cases i with
    | none => simp [emT, ih, letters_none]
    | some x =>
      simp only [List.cons_append, emT, ih, letters_some, List.length_cons, List.append_assoc]
      congr 3
      ring

theorem emT_garb (B : List (Option ℕ)) : ∀ c, (∀ i < (letters B).length, (c + i) % D.d ≠ 0) →
    D.emT c B = List.replicate (D.s * B.length) true := by
  induction B with
  | nil => intro c _; simp [emT]
  | cons i B ih =>
    intro c h
    cases i with
    | none =>
      rw [letters_none] at h
      simp only [emT, ih c h, List.length_cons]
      rw [← List.replicate_add]; congr 1; ring
    | some x =>
      rw [letters_some] at h
      have h0 := h 0 (by simp)
      simp only [add_zero] at h0
      have h' : ∀ i < (letters B).length, (c + 1 + i) % D.d ≠ 0 := fun i hi => by
        have := h (i + 1) (by simp; omega)
        rwa [show c + (i + 1) = c + 1 + i by ring] at this
      simp only [emT, letE, if_neg h0, ih (c + 1) h', List.length_cons]
      rw [← List.replicate_add]; congr 1; ring

theorem true_mem_toks {I : List (Option ℕ)} (h : letters I ≠ []) : true ∈ D.toks I := by
  induction I with
  | nil => simp [letters_nil] at h
  | cons i I ih =>
    rw [toks_cons]
    cases i with
    | none => exact List.mem_append_left _ (by simp [itok])
    | some x => exact List.mem_append_left _ (by simp [itok, enc])

theorem toks_map_some (w : List ℕ) : D.toks (w.map some) = D.encW w := by
  simp [toks, encW, List.flatMap_map, itok]

theorem toks_replicate_none (n : ℕ) : D.toks (List.replicate n none) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, toks_cons, itok, ih]

theorem letters_map_some (w : List ℕ) : letters (w.map some) = w := by
  induction w with
  | nil => rfl
  | cons x w ih => simp [letters_some, ih]

theorem letters_replicate_none (n : ℕ) : letters (List.replicate n none) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, letters_none, ih]

/-- The padded items of a production. -/
def prodI (x : ℕ) : List (Option ℕ) :=
  (D.P x).map some ++ List.replicate (D.s - ((D.encW (D.P x)).length - 1)) none

theorem letE_prodI (hD : D.Ok) {x : ℕ} (hx : x < D.k) (hH : x ≠ D.H) :
    D.letE 0 x = D.toks (D.prodI x) := by
  have hne := hD.P_ne x
  obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hne
  have hhead : D.encW (D.P x) = false :: (D.encW (D.P x)).tail := by
    rw [hy]; simp [encW, enc, List.replicate_succ, show 2 * (y + 1) = (2 * y + 1) + 1 by ring]
  simp only [letE, Nat.zero_mod, if_true, D.track_letter hD hx, if_neg hH, prodI, toks_append,
    toks_map_some, toks_replicate_none]
  rw [← List.cons_append, ← hhead]

theorem letters_split {I : List (Option ℕ)} : ∀ {u v : List ℕ}, letters I = u ++ v →
    ∃ A B, I = A ++ B ∧ letters A = u ∧ letters B = v := by
  induction I with
  | nil =>
    intro u v h
    simp only [letters_nil, List.nil_eq_append_iff] at h
    exact ⟨[], [], rfl, h.1.symm, h.2.symm⟩
  | cons i I ih =>
    intro u v h
    cases i with
    | none =>
      rw [letters_none] at h
      obtain ⟨A, B, rfl, hA, hB⟩ := ih h
      exact ⟨none :: A, B, rfl, by rw [letters_none, hA], hB⟩
    | some x =>
      rw [letters_some] at h
      cases u with
      | nil =>
        exact ⟨[], some x :: I, rfl, rfl, by rw [letters_some, h]; rfl⟩
      | cons y u =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨A, B, rfl, hA, hB⟩ := ih h
        exact ⟨some x :: A, B, rfl, by rw [letters_some, hA], hB⟩

theorem ph_zero : D.ph 0 = 0 := by simp [ph]

theorem first_letter {I : List (Option ℕ)} {x0 : ℕ} {w : List ℕ} (h : letters I = x0 :: w) :
    ∃ G A, I = G ++ some x0 :: A ∧ letters G = [] ∧ letters A = w := by
  induction I with
  | nil => simp [letters_nil] at h
  | cons i I ih =>
    cases i with
    | none =>
      rw [letters_none] at h
      obtain ⟨G, A, rfl, hG, hA⟩ := ih h
      exact ⟨none :: G, A, rfl, by rw [letters_none, hG], hA⟩
    | some x =>
      rw [letters_some, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨[], I, rfl, rfl, h⟩

theorem letters_length_le (I : List (Option ℕ)) : (letters I).length ≤ I.length := by
  induction I with
  | nil => simp [letters_nil]
  | cons i I ih => cases i <;> simp [letters_none, letters_some] <;> omega

/-- **Reading a group of `d` letters.** -/
theorem read_group (hD : D.Ok) (I : List (Option ℕ)) (hI : ∀ x ∈ letters I, x < D.k)
    {x0 : ℕ} {w : List ℕ} (hw : letters I = x0 :: w) (hlen : D.d ≤ w.length + 1) :
    ∃ n C g b, 1 ≤ b ∧ letters C = w.drop (D.d - 1) ∧
      LSeg D.β D.prodB (D.bits (D.toks I)) n
        (D.bits (D.toks C ++ (List.replicate (D.s * g) true ++ D.letE 0 x0) ++
          List.replicate (D.s * b) true)) ∧
      ∃ i < n, ((step D.β D.prodB)^[i] (D.bits (D.toks I))).head? = some true := by
  have hd := hD.two_le_d
  have hβs := D.β_le_s
  have hβ2 := D.two_le_β hD
  obtain ⟨G, A, rfl, hG, hA⟩ := first_letter hw
  obtain ⟨B, C, rfl, hB, hC⟩ := letters_split (I := A) (u := w.take (D.d - 1))
    (v := w.drop (D.d - 1)) (by rw [hA, List.take_append_drop])
  have hBlen : (letters B).length = D.d - 1 := by
    rw [hB, List.length_take]; omega
  have hlets : letters (G ++ some x0 :: (B ++ C)) = x0 :: (letters B ++ letters C) := by
    rw [letters_append, hG, letters_some, letters_append]; rfl
  have hk1 : ∀ y ∈ letters (G ++ [some x0]), y < D.k := fun y hy => by
    rw [letters_append, hG, letters_some, letters_nil] at hy
    simp at hy
    exact hI y (by rw [hlets, hy]; exact List.mem_cons_self)
  have hkB : ∀ y ∈ letters B, y < D.k := fun y hy => hI y (by rw [hlets]; simp [hy])
  have hl1 : (letters (G ++ [some x0])).length = 1 := by
    rw [letters_append, hG, letters_some, letters_nil]; rfl
  -- chunk 1
  obtain ⟨e1, e2⟩ := D.read_items hD _ hk1 0
  simp only [ph_zero, hl1, zero_add] at e1 e2
  have hE1 : D.emT 0 (G ++ [some x0]) = List.replicate (D.s * G.length) true ++ D.letE 0 x0 := by
    rw [emT_append, hG, List.length_nil, add_zero, D.emT_garb G 0 (by simp [hG])]
    simp [emT]
  rw [hE1] at e1
  have hY1 : D.β ≤ (D.bits (D.toks (B ++ C))).length :=
    D.β_le_bits_of_true hD (D.true_mem_toks (fun h => by
      have := congrArg List.length h
      rw [letters_append, List.length_append, hBlen] at this
      simp at this; omega))
  obtain ⟨s1, -⟩ := D.bin_chunk hD (D.toks (G ++ [some x0])) (D.bits (D.toks (B ++ C))) (φ := 0)
    (by omega) hY1
  rw [e1, e2] at s1
  -- chunk 2
  obtain ⟨f1, f2⟩ := D.read_items hD B hkB 1
  rw [hBlen, show 1 + (D.d - 1) = D.d by omega] at f2
  have hph1 : D.ph D.d = 0 := by simp [ph]
  rw [hph1] at f2
  have hE2 : D.emT 1 B = List.replicate (D.s * B.length) true :=
    D.emT_garb B 1 (fun i hi => by
      rw [hBlen] at hi; rw [Nat.mod_eq_of_lt (by omega)]; omega)
  rw [hE2] at f1
  have hE1len : D.s + 1 ≤ (List.replicate (D.s * G.length) true ++ D.letE 0 x0).length := by
    simp [letE, D.track_length hD]
  have hY2 : D.β ≤ (D.bits (D.toks C) ++
      D.bits (List.replicate (D.s * G.length) true ++ D.letE 0 x0)).length := by
    have := D.length_le_bits hD (List.replicate (D.s * G.length) true ++ D.letE 0 x0)
    rw [List.length_append]; omega
  obtain ⟨s2, h2⟩ := D.bin_chunk hD (D.toks B) (D.bits (D.toks C) ++
      D.bits (List.replicate (D.s * G.length) true ++ D.letE 0 x0)) (φ := D.ph 1) (D.ph_lt hD 1) hY2
  rw [f1, f2] at s2
  rw [f1] at h2
  have hq : (D.bits (D.toks (B ++ C)) ++
      D.bits (List.replicate (D.s * G.length) true ++ D.letE 0 x0)).drop (D.ph 1) =
      (D.bits (D.toks B) ++ (D.bits (D.toks C) ++
        D.bits (List.replicate (D.s * G.length) true ++ D.letE 0 x0))).drop (D.ph 1) := by
    rw [toks_append, bits_append, List.append_assoc]
  rw [hq] at s1
  have hin : D.bits (D.toks (G ++ some x0 :: (B ++ C))) =
      (D.bits (D.toks (G ++ [some x0])) ++ D.bits (D.toks (B ++ C))).drop 0 := by
    rw [List.drop_zero, ← bits_append, ← toks_append]; simp
  have hout : (D.bits (D.toks C) ++ D.bits (List.replicate (D.s * G.length) true ++ D.letE 0 x0) ++
      D.bits (List.replicate (D.s * B.length) true)).drop 0 =
      D.bits (D.toks C ++ (List.replicate (D.s * G.length) true ++ D.letE 0 x0) ++
        List.replicate (D.s * B.length) true) := by
    simp only [List.drop_zero, bits_append, List.append_assoc]
  have hBpos : 1 ≤ B.length := by have := letters_length_le B; omega
  have hspos : 0 < (List.replicate (D.s * B.length) true).length := by
    rw [List.length_replicate]; exact Nat.mul_pos (by omega) (by omega)
  refine ⟨_, C, G.length, B.length, hBpos, hC, by rw [hin, ← hout]; exact s1.trans s2,
    (List.replicate (D.s * G.length) true ++ D.letE 0 x0).length, Nat.lt_add_of_pos_right hspos, ?_⟩
  rw [hin, s1.1]
  have := h2 0 hspos
  simpa using this

/-! ### After the halting letter -/

theorem letE_prodI' (hD : D.Ok) {c x : ℕ} (hc : c % D.d = 0) (hx : x < D.k) (hH : x ≠ D.H) :
    D.letE c x = D.toks (D.prodI x) := by
  rw [← D.letE_prodI hD hx hH]; simp [letE, hc]

theorem emT_items (hD : D.Ok) (I : List (Option ℕ)) (hI : ∀ x ∈ letters I, x < D.k ∧ x ≠ D.H) :
    ∀ c, ∃ J, D.emT c I = D.toks J := by
  induction I with
  | nil => intro c; exact ⟨[], rfl⟩
  | cons i I ih =>
    intro c
    cases i with
    | none =>
      rw [letters_none] at hI
      obtain ⟨J, hJ⟩ := ih hI c
      exact ⟨List.replicate D.s none ++ J, by simp [emT, hJ, toks_append, toks_replicate_none]⟩
    | some x =>
      rw [letters_some] at hI
      obtain ⟨J, hJ⟩ := ih (fun y hy => hI y (List.mem_cons_of_mem _ hy)) (c + 1)
      obtain ⟨hx, hH⟩ := hI x List.mem_cons_self
      by_cases hc : c % D.d = 0
      · exact ⟨D.prodI x ++ J, by simp [emT, hJ, toks_append, D.letE_prodI' hD hc hx hH]⟩
      · exact ⟨List.replicate D.s none ++ J,
          by simp [emT, letE, hc, hJ, toks_append, toks_replicate_none]⟩

theorem emT_length (hD : D.Ok) (I : List (Option ℕ)) (hI : letters I ≠ []) :
    ∀ c, D.s ≤ (D.emT c I).length := by
  induction I with
  | nil => simp [letters_nil] at hI
  | cons i I ih =>
    intro c
    cases i with
    | none => simp [emT]
    | some x =>
      simp only [emT, List.length_append]
      have : D.s ≤ (D.letE c x).length := by
        unfold letE; split_ifs <;> simp [D.track_length hD]
      omega

theorem rT_replicate_true (φ : ℕ) {b : Bool} (h : D.track φ = List.replicate D.s b) (m : ℕ) :
    D.rT φ (List.replicate m true) = List.replicate (D.s * m) b ∧
      D.pT φ (List.replicate m true) = φ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, rT_true, pT_true, ih.1, ih.2, h, ← List.replicate_add]
    exact ⟨by congr 1; ring, rfl⟩

theorem odd_items (hD : D.Ok) (J : List (Option ℕ)) : ∀ φ, φ < D.β → φ % 2 = 1 →
    AF (D.rT φ (D.toks J)) ∧ D.pT φ (D.toks J) < D.β ∧ D.pT φ (D.toks J) % 2 = 1 := by
  have hb := D.β_even
  induction J with
  | nil => intro φ h1 h2; simp [toks, AF, h1, h2]
  | cons i J ih =>
    intro φ h1 h2
    rw [toks_cons]
    obtain ⟨a1, a2⟩ := D.rT_append (D.itok i) (D.toks J) φ
    rw [a1, a2]
    have key : AF (D.rT φ (D.itok i)) ∧ D.pT φ (D.itok i) < D.β ∧ D.pT φ (D.itok i) % 2 = 1 := by
      cases i with
      | none =>
        simp only [itok, rT_true, rT_nil, pT_true, pT_nil, List.append_nil, D.track_odd h2]
        exact ⟨AF_replicate _, h1, h2⟩
      | some x =>
        simp only [itok, enc]
        obtain ⟨b1, b2⟩ := D.rT_append (List.replicate (2 * (x + 1)) false)
          (true :: List.replicate (D.L - 2 * (x + 1)) false) φ
        rw [b1, b2]
        obtain ⟨z1, z2⟩ := D.zeros_parity hD (2 * (x + 1)) φ h1
        have zl := D.pT_lt hD (List.replicate (2 * (x + 1)) false) φ h1
        set φ1 := D.pT φ (List.replicate (2 * (x + 1)) false)
        have hφ1 : φ1 % 2 = 1 := by omega
        rw [rT_true, pT_true, D.track_odd hφ1]
        obtain ⟨y1, y2⟩ := D.zeros_parity hD (D.L - 2 * (x + 1)) φ1 zl
        have yl := D.pT_lt hD (List.replicate (D.L - 2 * (x + 1)) false) φ1 zl
        refine ⟨AF_append z1 (AF_append (AF_replicate _) y1), yl, ?_⟩
        have hL : D.L = 2 * D.k + 2 := rfl
        omega
    obtain ⟨k1, k2, k3⟩ := key
    obtain ⟨j1, j2, j3⟩ := ih _ k2 k3
    exact ⟨AF_append k1 j1, j2, j3⟩

theorem AF_bits {T : List Bool} (h : AF T) : AF (D.bits T) := by
  induction T with
  | nil => simp [bits, AF]
  | cons b T ih =>
    rw [bits_cons]
    have hb : b = false := h b List.mem_cons_self
    subst hb
    exact AF_append (by simp [prodB, AF]) (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem AF_drop {l : List Bool} (h : AF l) (n : ℕ) : AF (l.drop n) :=
  fun b hb => h b (List.mem_of_mem_drop hb)

theorem bin_step (hD : D.Ok) {W : List Bool} (T Y : List Bool) {φ : ℕ} (hW : W = (D.bits T ++ Y).drop φ)
    (hφ : φ < D.β) (hY : D.β ≤ Y.length) :
    LSeg D.β D.prodB W (D.rT φ T).length ((Y ++ D.bits (D.rT φ T)).drop (D.pT φ T)) :=
  hW ▸ (D.bin_chunk hD T Y hφ hY).1

/-- **The collapse after the halting letter**: the queue reaches all zeros. -/
theorem collapse (hD : D.Ok) (C : List (Option ℕ)) (hC : ∀ x ∈ letters C, x < D.k ∧ x ≠ D.H)
    (hCne : letters C ≠ []) (g b : ℕ) (hb : 1 ≤ b) :
    ∃ n W, AF W ∧ LSeg D.β D.prodB (D.bits (D.toks C ++ (List.replicate (D.s * g) true ++
      D.letE 0 D.H) ++ List.replicate (D.s * b) true)) n W := by
  have hβs := D.β_le_s
  have hβ2 := D.two_le_β hD
  have hse := D.s_even hD
  have hbe := D.β_even
  have hH : D.letE 0 D.H = List.replicate (D.s + 1) false := by
    simp [letE, D.track_letter hD hD.H_lt, List.replicate_succ]
  rw [hH]
  set E := List.replicate (D.s * g) true ++ List.replicate (D.s + 1) false ++
    List.replicate (D.s * b) true with hE
  -- chunk 1: the remaining letters
  have hk : ∀ y ∈ letters C, y < D.k := fun y hy => (hC y hy).1
  obtain ⟨r1, r2⟩ := D.read_items hD C hk 0
  rw [ph_zero] at r1 r2
  obtain ⟨J, hJ⟩ := D.emT_items hD C hC 0
  rw [hJ] at r1
  set p := D.ph (0 + (letters C).length)
  have hEl : D.β ≤ (D.bits E).length := by
    have := D.length_le_bits hD E; simp [hE] at this ⊢; omega
  have c1 := D.bin_step hD (D.toks C) (D.bits E) (φ := 0)
    (W := D.bits (D.toks C ++ (List.replicate (D.s * g) true ++ List.replicate (D.s + 1) false) ++
      List.replicate (D.s * b) true))
    (by simp only [List.drop_zero, bits_append, hE, List.append_assoc]) (by omega) hEl
  rw [r1, r2] at c1
  -- chunk 2: the garbage and the halting zeros
  have hJl : D.β ≤ (D.bits (D.toks J)).length := by
    have := D.length_le_bits hD (D.toks J)
    have := D.emT_length hD C hCne 0
    rw [hJ] at this; omega
  have hp : p < D.β := D.ph_lt hD _
  have hpe : p % 2 = 0 := D.ph_even hD _
  obtain ⟨u1, u2⟩ := D.rT_replicate_true p (D.track_garb hpe (D.ph_garb hD _)) (D.s * g)
  obtain ⟨z1, z2⟩ := D.zeros_parity hD (D.s + 1) p hp
  have zl := D.pT_lt hD (List.replicate (D.s + 1) false) p hp
  set Z1 := D.rT p (List.replicate (D.s + 1) false)
  set p' := D.pT p (List.replicate (D.s + 1) false)
  have hp' : p' % 2 = 1 := by omega
  obtain ⟨v1, v2⟩ := D.rT_replicate_true p' (D.track_odd hp') (D.s * b)
  have eE : D.rT p E = List.replicate (D.s * (D.s * g)) true ++ Z1 ++
      List.replicate (D.s * (D.s * b)) false ∧ D.pT p E = p' := by
    rw [hE]
    obtain ⟨a1, a2⟩ := D.rT_append (List.replicate (D.s * g) true ++ List.replicate (D.s + 1) false)
      (List.replicate (D.s * b) true) p
    obtain ⟨b1, b2⟩ := D.rT_append (List.replicate (D.s * g) true) (List.replicate (D.s + 1) false) p
    rw [a1, a2, b1, b2, u1, u2, v1, v2]
    exact ⟨rfl, rfl⟩
  have c2 := D.bin_step hD E (D.bits (D.toks J)) (φ := p) rfl hp hJl
  rw [eE.1, eE.2] at c2
  -- chunk 3: everything else is read at odd phases
  have hRl : D.β ≤ (D.bits (Z1 ++ List.replicate (D.s * (D.s * b)) false)).length := by
    have := D.length_le_bits hD (Z1 ++ List.replicate (D.s * (D.s * b)) false)
    have h1 : D.s ≤ D.s * (D.s * b) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hb)
    rw [List.length_append, List.length_replicate] at this
    omega
  obtain ⟨o1, o2, o3⟩ := D.odd_items hD J p' zl hp'
  obtain ⟨w1, w2⟩ := D.rT_replicate_true (D.pT p' (D.toks J))
    (D.track_odd o3) (D.s * (D.s * g))
  have c3 := D.bin_step hD (D.toks J ++ List.replicate (D.s * (D.s * g)) true)
    (D.bits (Z1 ++ List.replicate (D.s * (D.s * b)) false))
    (W := (D.bits (D.toks J) ++ D.bits (List.replicate (D.s * (D.s * g)) true ++ Z1 ++
      List.replicate (D.s * (D.s * b)) false)).drop p')
    (φ := p') (by simp only [bits_append, List.append_assoc]) zl hRl
  obtain ⟨m1, m2⟩ := D.rT_append (D.toks J) (List.replicate (D.s * (D.s * g)) true) p'
  rw [m1, m2, w1, w2] at c3
  refine ⟨_, _, ?_, (c1.trans c2).trans c3⟩
  refine AF_drop (AF_append (D.AF_bits (AF_append z1 (AF_replicate _)))
    (D.AF_bits (AF_append o1 (AF_replicate _)))) _

/-- A queue of zeros runs short. -/
theorem halts_AF (hD : D.Ok) : ∀ (N : ℕ) (W : List Bool), W.length ≤ N → AF W →
    ∃ n, ((step D.β D.prodB)^[n] W).length < D.β ∧
      ∀ m < n, D.β ≤ ((step D.β D.prodB)^[m] W).length := by
  have hβ2 := D.two_le_β hD
  intro N
  induction N with
  | zero =>
    intro W hW _
    exact ⟨0, by simp only [Function.iterate_zero, id]; omega,
      fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  | succ N ih =>
    intro W hW hAF
    by_cases hs : W.length < D.β
    · exact ⟨0, hs, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
    · obtain ⟨x, W', rfl⟩ := List.exists_cons_of_ne_nil
        (show W ≠ [] from fun h => by rw [h] at hs; simp at hs; omega)
      have hx : x = false := hAF x List.mem_cons_self
      subst hx
      have hst : step D.β D.prodB (false :: W') = (false :: W').drop D.β ++ [false] := by
        rw [step_cons D.β D.prodB (by omega)]; rfl
      have hAF' : AF ((false :: W').drop D.β ++ [false]) :=
        AF_append (AF_drop hAF _) (AF_replicate 1)
      obtain ⟨n, h1, h2⟩ := ih _ (by
        rw [List.length_append, List.length_drop, List.length_cons, List.length_singleton]
        simp only [List.length_cons] at hW hs
        have := hβ2
        omega) hAF'
      refine ⟨n + 1, by rw [Function.iterate_succ_apply, hst]; exact h1, fun m hm => ?_⟩
      cases m with
      | zero => simpa using (show D.β ≤ (false :: W').length by omega)
      | succ m =>
        rw [Function.iterate_succ_apply, hst]
        exact h2 m (by omega)

/-! ### The initial word and the invariants of the binary run -/

/-- The garbage padding making the initial length `≡ 1 (mod β − 1)`. -/
def pad (w : List ℕ) : ℕ := (D.β - 2) * (D.bits (D.toks (w.map some))).length + 1

/-- The initial items of a tag word. -/
def items0 (w : List ℕ) : List (Option ℕ) := w.map some ++ List.replicate (D.pad w) none

/-- The initial binary word of a tag word. -/
def W0 (w : List ℕ) : List Bool := D.bits (D.toks (D.items0 w))

theorem letters_items0 (w : List ℕ) : letters (D.items0 w) = w := by
  simp [items0, letters_append, letters_map_some, letters_replicate_none]

theorem TS_step : D.TS.step = step D.β D.prodB := by
  rw [TagSys.step_eq]; rfl

theorem run_eq (W : List Bool) (m : ℕ) : run D.TS W m = (step D.β D.prodB)^[m] W := by
  unfold run; rw [TS_step]

theorem bits_replicate (n : ℕ) (b : Bool) :
    (D.bits (List.replicate n b)).length = n * (if b then D.s * D.β else 1) := by
  induction n with
  | zero => simp [bits]
  | succ n ih =>
    rw [List.replicate_succ, bits_cons, List.length_append, ih]
    cases b <;> simp [prodB, u_length] <;> ring

theorem bits_replicate_false (n : ℕ) : D.bits (List.replicate n false) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, bits_cons, ih]; rfl

/-- `s β = 1 + (β − 1)(1 + Kβ)`. -/
theorem sβ_eq (hD : D.Ok) :
    D.s * D.β = 1 + (D.β - 1) * (1 + (2 * D.R * (D.L + 1) + 1) * D.β) := by
  have h2 := D.two_le_β hD
  obtain ⟨m, hm⟩ : ∃ m, D.β = m + 1 := ⟨D.β - 1, by omega⟩
  unfold s
  rw [hm, Nat.add_sub_cancel]
  ring

theorem W0_length_mod (hD : D.Ok) (w : List ℕ) :
    (D.W0 w).length % (D.β - 1) = 1 % (D.β - 1) := by
  have h2 := D.two_le_β hD
  unfold W0 items0 pad
  rw [toks_append, bits_append, List.length_append, toks_replicate_none, bits_replicate, if_pos rfl,
    D.sβ_eq hD]
  set M := (D.bits (D.toks (w.map some))).length
  obtain ⟨m, hm⟩ : ∃ m, D.β = m + 2 := ⟨D.β - 2, by omega⟩
  rw [hm, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have : M + (m * M + 1) * (1 + (m + 1) * (1 + (2 * D.R * (D.L + 1) + 1) * (m + 2))) =
      1 + (m + 1) * (M + (m * M + 1) * (1 + (2 * D.R * (D.L + 1) + 1) * (m + 2))) := by ring
  rw [this, Nat.add_mul_mod_self_left]

theorem length_mod_step (hD : D.Ok) (W : List Bool) (h : W.length % (D.β - 1) = 1 % (D.β - 1)) :
    (D.TS.step W).length % (D.β - 1) = 1 % (D.β - 1) := by
  have h2 := D.two_le_β hD
  by_cases hs : D.TS.Short W
  · rw [TagSys.step_of_short _ hs]; exact h
  · obtain ⟨x, W', rfl⟩ := List.exists_cons_of_ne_nil
      (show W ≠ [] from fun h' => by rw [h'] at hs; exact hs (by simp [TagSys.Short, TS]; omega))
    have hl := TagSys.length_step D.TS (s := x) (W' := W') (by simp [TagSys.Short] at hs; exact hs)
    have hu : D.TS.u.length = 1 + (D.β - 1) * (1 + (2 * D.R * (D.L + 1) + 1) * D.β) := by
      show D.u.length = _; rw [u_length, D.sβ_eq hD]
    have hβ : D.TS.β = D.β := rfl
    rw [hβ] at hl
    obtain ⟨m, hm⟩ : ∃ m, D.β = m + 1 := ⟨D.β - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel] at h hu ⊢
    rw [hm] at hl
    cases x
    · simp only [Bool.false_eq_true, if_false] at hl
      have e : (D.TS.step (false :: W')).length + m * 1 = (false :: W').length := by omega
      have e1 := congrArg (· % m) e
      simp only [Nat.add_mul_mod_self_left] at e1
      rw [e1]; exact h
    · simp only [if_true] at hl
      rw [hu] at hl
      have e : (D.TS.step (true :: W')).length + m * 1 =
          (true :: W').length + m * (1 + (2 * D.R * (D.L + 1) + 1) * (m + 1)) := by omega
      have e1 := congrArg (· % m) e
      simp only [Nat.add_mul_mod_self_left] at e1
      rw [e1]; exact h

theorem run_length_mod (hD : D.Ok) (w : List ℕ) :
    ∀ n, (run D.TS (D.W0 w) n).length % (D.β - 1) = 1 % (D.β - 1) := by
  intro n
  induction n with
  | zero => exact D.W0_length_mod hD w
  | succ n ih => rw [run_succ]; exact D.length_mod_step hD _ ih

theorem content_ge_of_get : ∀ (l : List Bool) (i : ℕ), l[i]? = some true → 3 ^ i ≤ content l := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons b l ih =>
    intro i h
    rw [content_cons]
    cases i with
    | zero => simp at h; subst h; simp [bit]
    | succ i =>
      have := ih i (by simpa using h)
      rw [pow_succ]; omega

theorem W0_split (hD : D.Ok) {x : ℕ} {w : List ℕ} :
    ∃ Z, D.W0 (x :: w) = List.replicate (2 * (x + 1)) false ++ (D.u ++ Z) := by
  refine ⟨D.bits (List.replicate (D.L - 2 * (x + 1)) false) ++
    D.bits (D.toks (w.map some ++ List.replicate (D.pad (x :: w)) none)), ?_⟩
  simp only [W0, items0, List.map_cons, List.cons_append, toks_cons, itok, enc, bits_append,
    bits_cons, bits_replicate_false, prodB, if_true, List.append_assoc]

theorem u_get (hD : D.Ok) : D.u[D.L]? = some true := by
  have hL := D.two_L_le_β hD
  have hs := D.β_le_s
  have h1 : 1 ≤ D.s := by have := D.two_le_β hD; omega
  obtain ⟨s', hs'⟩ : ∃ s', D.s = s' + 1 := ⟨D.s - 1, by omega⟩
  have hu : D.u = D.row 0 ++ (List.range s').flatMap (fun i => D.row (i + 1)) := by
    unfold u; rw [hs', List.range_succ_eq_map]; simp [List.flatMap_map]
  rw [hu, List.getElem?_append_left (by rw [row_length]; unfold L at hL ⊢; omega)]
  have hLe : D.L % 2 = 0 := by unfold L; omega
  have hLk : D.L + 2 * D.k < D.β := by unfold L at hL ⊢; omega
  simp [row, show D.L < D.β by omega, D.track_garb hLe hLk]
  rw [hs']; rfl

theorem W0_first (hD : D.Ok) {x : ℕ} {w : List ℕ} : (D.W0 (x :: w)).head? = some false := by
  obtain ⟨Z, hZ⟩ := D.W0_split hD (x := x) (w := w)
  rw [hZ, show 2 * (x + 1) = (2 * x + 1) + 1 by ring, List.replicate_succ]
  rfl

/-! ### The equivalence -/

theorem LSeg_refl (W : List Bool) : LSeg D.β D.prodB W 0 W :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The binary run follows the tag run as long as the halting letter is not read. -/
theorem sim (hD : D.Ok) (w0 : List ℕ) (hw0 : ∀ x ∈ w0, x < D.k)
    (hlong : ∀ n, (∀ m < n, ((step D.d D.P)^[m] w0).head? ≠ some D.H) →
      D.d ≤ ((step D.d D.P)^[n] w0).length) :
    ∀ n, (∀ m < n, ((step D.d D.P)^[m] w0).head? ≠ some D.H) →
      ∃ N I, n ≤ N ∧ letters I = (step D.d D.P)^[n] w0 ∧ (∀ x ∈ letters I, x < D.k) ∧
        LSeg D.β D.prodB (D.W0 w0) N (D.bits (D.toks I)) := by
  have hd := hD.two_le_d
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨0, D.items0 w0, le_rfl, D.letters_items0 w0, by rw [D.letters_items0]; exact hw0,
      D.LSeg_refl _⟩
  | succ n ih =>
    intro hH
    obtain ⟨N, I, hN, hlet, hk, hseg⟩ := ih (fun m hm => hH m (by omega))
    have hl := hlong n (fun m hm => hH m (by omega))
    have hn := hH n (by omega)
    obtain ⟨x0, w, hw⟩ := List.exists_cons_of_ne_nil
      (show (step D.d D.P)^[n] w0 ≠ [] from fun h => by rw [h] at hl; simp at hl; omega)
    rw [hw] at hlet hl hn
    have hx0H : x0 ≠ D.H := fun h => hn (by rw [h]; rfl)
    have hx0k : x0 < D.k := hk x0 (by rw [hlet]; exact List.mem_cons_self)
    simp only [List.length_cons] at hl
    obtain ⟨n1, C, g, b, -, hC, seg1, i, hi, -⟩ := D.read_group hD I hk hlet hl
    obtain ⟨d', hd'⟩ : ∃ d', D.d = d' + 1 := ⟨D.d - 1, by omega⟩
    have hstep : (step D.d D.P)^[n + 1] w0 = w.drop (D.d - 1) ++ D.P x0 := by
      rw [Function.iterate_succ_apply', hw, step_cons D.d D.P (by simp; omega), hd',
        List.drop_succ_cons, Nat.add_sub_cancel]
    refine ⟨N + n1, C ++ (List.replicate (D.s * g) none ++ D.prodI x0) ++
      List.replicate (D.s * b) none, by omega, ?_, ?_, ?_⟩
    · rw [hstep, letters_append, letters_append, letters_append, hC, letters_replicate_none,
        letters_replicate_none, prodI, letters_append, letters_map_some, letters_replicate_none]
      simp
    · intro y hy
      rw [letters_append, letters_append, letters_append, letters_replicate_none,
        letters_replicate_none, prodI, letters_append, letters_map_some, letters_replicate_none,
        hC] at hy
      simp only [List.nil_append, List.append_nil, List.mem_append] at hy
      rcases hy with hy | hy
      · exact hk y (by rw [hlet]; exact List.mem_cons_of_mem _ (List.mem_of_mem_drop hy))
      · exact hD.P_lt x0 hx0k y hy
    · have e : D.toks (C ++ (List.replicate (D.s * g) none ++ D.prodI x0) ++
          List.replicate (D.s * b) none) = D.toks C ++ (List.replicate (D.s * g) true ++
            D.letE 0 x0) ++ List.replicate (D.s * b) true := by
        rw [toks_append, toks_append, toks_append, toks_replicate_none, toks_replicate_none,
          D.letE_prodI hD hx0k hx0H]
      rw [e]
      exact hseg.trans seg1

theorem short_run_eq (hD : D.Ok) (w : List ℕ) {n : ℕ} (hshort : D.TS.Short (run D.TS (D.W0 w) (n + 1)))
    (hlong : ¬ D.TS.Short (run D.TS (D.W0 w) n)) : run D.TS (D.W0 w) (n + 1) = [false] := by
  have hβ2 := D.two_le_β hD
  have hβs := D.β_le_s
  have hL := D.two_L_le_β hD
  have hβ4 : 4 ≤ D.β := by unfold L at hL; omega
  have hmod := D.run_length_mod hD w (n + 1)
  rw [run_succ] at hshort hmod ⊢
  unfold TagSys.Short at hshort hlong
  have hTSβ : D.TS.β = D.β := rfl
  rw [hTSβ] at hshort hlong
  obtain ⟨s0, W', hW⟩ := List.exists_cons_of_ne_nil
    (show run D.TS (D.W0 w) n ≠ [] from fun h => by rw [h] at hlong; simp at hlong; omega)
  rw [hW] at hshort hmod hlong ⊢
  have hls := TagSys.length_step D.TS (s := s0) (W' := W') (by rw [hTSβ]; omega)
  rw [hTSβ] at hls
  have hv : (D.TS.step (s0 :: W')).length = 1 := by
    set v := (D.TS.step (s0 :: W')).length
    have h1 : 1 % (D.β - 1) = 1 := Nat.mod_eq_of_lt (by omega)
    by_cases hv : v < D.β - 1
    · rw [Nat.mod_eq_of_lt hv, h1] at hmod; exact hmod
    · have : v = D.β - 1 := by omega
      rw [this, Nat.mod_self, h1] at hmod; exact absurd hmod (by norm_num)
  cases s0
  · simp only [Bool.false_eq_true, if_false] at hls
    rw [TagSys.step_of_long D.TS (by rw [hTSβ]; omega)]
    have : (false :: W').length = D.β := by omega
    rw [hTSβ, List.drop_eq_nil_of_le (by omega)]
    rfl
  · simp only [if_true] at hls
    have hu : D.TS.u.length = D.s * D.β := u_length D
    rw [hu] at hls
    have : D.β ≤ D.s * D.β := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith

/-- **The binary track system halts exactly when the tag system reads its halting letter**,
with the promises of the tag certificate. -/
theorem bin_iff (hD : D.Ok) (w0 : List ℕ) (hw0 : ∀ x ∈ w0, x < D.k)
    (hlong : ∀ n, (∀ m < n, ((step D.d D.P)^[m] w0).head? ≠ some D.H) →
      D.d ≤ ((step D.d D.P)^[n] w0).length)
    (hshape : ∀ n, ((step D.d D.P)^[n] w0).head? = some D.H →
      (∀ m < n, ((step D.d D.P)^[m] w0).head? ≠ some D.H) →
      2 * D.d ≤ ((step D.d D.P)^[n] w0).length ∧ ∀ y ∈ ((step D.d D.P)^[n] w0).drop D.d, y ≠ D.H) :
    (D.TS.Halts (D.W0 w0) ↔ ∃ n, ((step D.d D.P)^[n] w0).head? = some D.H) ∧
      TagPromise D.TS (D.W0 w0) ∧ D.TS.β ≤ (D.W0 w0).length ∧ 2 ≤ D.TS.β ∧
      2 ≤ D.TS.u.length := by
  classical
  have hβ2 := D.two_le_β hD
  have hβs := D.β_le_s
  have hd := hD.two_le_d
  have hL := D.two_L_le_β hD
  have hl0 := hlong 0 (fun m hm => absurd hm (Nat.not_lt_zero _))
  obtain ⟨x, w, rfl⟩ := List.exists_cons_of_ne_nil
    (show w0 ≠ [] from fun h => by rw [h] at hl0; simp at hl0; omega)
  have hxk : x < D.k := hw0 x List.mem_cons_self
  have hW0len : D.β ≤ (D.W0 (x :: w)).length :=
    D.β_le_bits_of_true hD (D.true_mem_toks (by rw [letters_items0]; simp))
  have hulen : 2 ≤ D.TS.u.length := by
    show 2 ≤ D.u.length; rw [u_length]; nlinarith
  -- after the halting letter the binary run halts, having read a `1`
  have key : (∃ n, ((step D.d D.P)^[n] (x :: w)).head? = some D.H) →
      ∃ T i, i < T ∧ (run D.TS (D.W0 (x :: w)) T).length < D.β ∧
        (∀ m < T, D.β ≤ (run D.TS (D.W0 (x :: w)) m).length) ∧
        (run D.TS (D.W0 (x :: w)) i).head? = some true := by
    intro hA
    have hmin : ∀ m < Nat.find hA, ((step D.d D.P)^[m] (x :: w)).head? ≠ some D.H :=
      fun m hm => Nat.find_min hA hm
    obtain ⟨N, I, -, hlet, hk, seg0⟩ := D.sim hD (x :: w) hw0 hlong _ hmin
    obtain ⟨h2d, hdrop⟩ := hshape _ (Nat.find_spec hA) hmin
    have hspec : ((step D.d D.P)^[Nat.find hA] (x :: w)).head? = some D.H := Nat.find_spec hA
    obtain ⟨y, v, hyv⟩ := List.exists_cons_of_ne_nil
      (show (step D.d D.P)^[Nat.find hA] (x :: w) ≠ [] from fun h => by
        rw [h] at hspec; simp at hspec)
    rw [hyv] at hspec hlet h2d hdrop
    have hy : y = D.H := by simpa using hspec
    subst hy
    simp only [List.length_cons] at h2d
    obtain ⟨n1, C, g, b, hb, hC, seg1, i, hi, hhead⟩ := D.read_group hD I hk hlet (by omega)
    obtain ⟨d', hd'⟩ : ∃ d', D.d = d' + 1 := ⟨D.d - 1, by omega⟩
    have hCk : ∀ z ∈ letters C, z < D.k ∧ z ≠ D.H := fun z hz => by
      rw [hC] at hz
      refine ⟨hk z (by rw [hlet]; exact List.mem_cons_of_mem _ (List.mem_of_mem_drop hz)),
        hdrop z ?_⟩
      rw [hd', List.drop_succ_cons]
      rwa [hd', Nat.add_sub_cancel] at hz
    have hCne : letters C ≠ [] := by
      rw [hC]; intro h; have := congrArg List.length h; simp at this; omega
    obtain ⟨n2, W, hAF, seg2⟩ := D.collapse hD C hCk hCne g b hb
    obtain ⟨n3, hshort, hl3⟩ := D.halts_AF hD W.length W le_rfl hAF
    have seg := (seg0.trans seg1).trans seg2
    refine ⟨N + n1 + n2 + n3, N + i, by omega, ?_, ?_, ?_⟩
    · rw [run_eq, show N + n1 + n2 + n3 = n3 + (N + n1 + n2) by ring, Function.iterate_add_apply,
        seg.1]
      exact hshort
    · intro m hm
      rw [run_eq]
      by_cases hm' : m < N + n1 + n2
      · exact seg.2 m hm'
      · obtain ⟨j, rfl⟩ : ∃ j, m = N + n1 + n2 + j := ⟨m - (N + n1 + n2), by omega⟩
        rw [show N + n1 + n2 + j = j + (N + n1 + n2) by ring, Function.iterate_add_apply, seg.1]
        exact hl3 j (by omega)
    · rw [run_eq, show N + i = i + N by ring, Function.iterate_add_apply, seg0.1]
      exact hhead
  have nokey : (¬ ∃ n, ((step D.d D.P)^[n] (x :: w)).head? = some D.H) →
      ∀ T, D.β ≤ (run D.TS (D.W0 (x :: w)) T).length := by
    intro hA T
    push_neg at hA
    obtain ⟨N, I, hN, -, -, seg⟩ := D.sim hD (x :: w) hw0 hlong (T + 1) (fun m _ => hA m)
    rw [run_eq]
    exact seg.2 T (by omega)
  refine ⟨⟨fun hh => ?_, fun hA => ?_⟩, ⟨?_, ?_, ?_⟩, hW0len, hβ2, hulen⟩
  · by_contra hA
    obtain ⟨T, hT⟩ := hh
    have := nokey hA T
    exact absurd hT (by unfold TagSys.Short; show ¬ (run D.TS (D.W0 (x :: w)) T).length < D.β; omega)
  · obtain ⟨T, i, -, hT, -, -⟩ := key hA
    exact ⟨T, hT⟩
  · -- the first symbol is `0`
    have h := D.W0_first hD (x := x) (w := w)
    obtain ⟨Z, hZ⟩ : ∃ Z, D.W0 (x :: w) = false :: Z := by
      cases hc : D.W0 (x :: w) with
      | nil => rw [hc] at h; simp at h
      | cons c Z => rw [hc] at h; simp at h; exact ⟨Z, by rw [h]⟩
    show content (run D.TS (D.W0 (x :: w)) 0) % 3 = 0
    rw [run_zero, hZ, content_cons]
    simp [bit]
  · -- a `1` in the initial deleted prefix beyond the head
    show 1 ≤ content (run D.TS (D.W0 (x :: w)) 0) % 3 ^ D.β / 3
    rw [run_zero]
    set W := D.W0 (x :: w)
    have hsplit : content W = content (W.take D.β) + 3 ^ D.β * content (W.drop D.β) := by
      conv_lhs => rw [← List.take_append_drop D.β W]
      rw [content_append, List.length_take, min_eq_left hW0len]
    have hlt : content (W.take D.β) < 3 ^ D.β := by
      have := content_lt (W.take D.β)
      rwa [List.length_take, min_eq_left hW0len] at this
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hLk : D.L = 2 * D.k + 2 := rfl
    have hidx : 2 * (x + 1) + D.L < D.β := by omega
    have hget : (W.take D.β)[2 * (x + 1) + D.L]? = some true := by
      rw [List.getElem?_take_of_lt hidx]
      obtain ⟨Z, hZ⟩ := D.W0_split hD (x := x) (w := w)
      rw [show W = List.replicate (2 * (x + 1)) false ++ (D.u ++ Z) from hZ,
        List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
        List.getElem?_append_left (by rw [u_length]; nlinarith), D.u_get hD]
    have := content_ge_of_get _ _ hget
    have h3 : 3 ≤ 3 ^ (2 * (x + 1) + D.L) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ 2 * (x + 1) + D.L by omega))
    omega
  · -- the terminal promise
    intro n hshort hmin
    by_cases hA : ∃ n, ((step D.d D.P)^[n] (x :: w)).head? = some D.H
    · obtain ⟨T, i, hiT, hT, hlT, hhead⟩ := key hA
      have hin : i < n := by
        by_contra hni
        have := hlT n (by omega)
        unfold TagSys.Short at hshort
        exact absurd hshort (by show ¬ (run D.TS (D.W0 (x :: w)) n).length < D.β; omega)
      refine ⟨?_, i, hin, ?_⟩
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact D.short_run_eq hD (x :: w) hshort (hmin n' (by omega))
      · show content (run D.TS (D.W0 (x :: w)) i) % 3 = 1
        obtain ⟨c, Z, hc⟩ := List.exists_cons_of_ne_nil (show run D.TS (D.W0 (x :: w)) i ≠ [] from
          fun h => by rw [h] at hhead; simp at hhead)
        rw [hc] at hhead ⊢
        simp at hhead
        rw [hhead]
        exact (content_mod_three_eq_one_iff true Z).2 rfl
    · exact absurd hshort (by
        have := nokey hA n
        unfold TagSys.Short; show ¬ (run D.TS (D.W0 (x :: w)) n).length < D.β; omega)

end DTag

end Jones1980
