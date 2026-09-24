import Diophantine.Paper1980.TagGoedel91
import Diophantine.Paper1980.TagRead91

/-!
# A 30-tag system simulating a single-register machine

Layer 2 of the undecidability of the encoded tag family.  A single-register machine (`GProg`)
with multiplications by `1, …, 5` and divisibility tests by `2, 3, 5` is simulated by a tag
system with deletion number `30` over natural-number letters.  A letter `lt kd ℓ t` carries a
kind `kd < 10`, a location `ℓ` and an index `t < 64`; a *block* `blk kd ℓ` is the thirty letters
of one kind and location with the indices `0, …, 29`.

A machine configuration `(ℓ, N)` is the queue `cfg ℓ I`: a sequence of `B`-blocks (one per
unit of `N`) and junk blocks, followed by the marker block `M ℓ`; junk blocks are read at
every phase into junk blocks, so they never disturb the alignment.

* `mul k nx`: each `B` block becomes `k` blocks `B nx`, the marker becomes `M nx`.
* `div k y n` (with `dl = 30/k`): each `B` block becomes the `30 + dl` letters `E ℓ`; reading
  these shifts the phase by `dl` per block, emitting `Q C` at the blocks counted `≡ 0 (mod k)`
  and `C` otherwise, and leaves the marker `M1` at the phase `c = dl·(−N mod k)`.  `M1` pads
  `c` junk letters and a block `M2` choosing the branch; the `Q`/`C` blocks are read at phase
  `c` into `B y` (from `Q`, when `c = 0`) or `B n` (from `C`, when `c ≠ 0`).
* `acc`: the marker emits the halting letter `H = 1` at a block start.

`reachesAcc_iff` is the equivalence: from `cfg 0 (junk :: B^N)` the tag system reads `H` exactly
when the machine reaches its accepting halt from `N`, and it never runs short before reading
`H`.  Locations outside the program are folded into a looping location `len`.
-/

namespace Jones1980

namespace GTag

variable {α : Type*} (d : ℕ) (P : α → List α)

/-- A segment of a run: `n` steps from `W` to `W'` through long queues whose heads avoid `H`. -/
def Seg (H : α) (W : List α) (n : ℕ) (W' : List α) : Prop :=
  (step d P)^[n] W = W' ∧
    ∀ m < n, d ≤ ((step d P)^[m] W).length ∧ ((step d P)^[m] W).head? ≠ some H

theorem Seg.refl (H : α) (W : List α) : Seg d P H W 0 W :=
  ⟨rfl, fun m h => absurd h (Nat.not_lt_zero _)⟩

variable {d P} in
theorem Seg.trans {H : α} {W W' W'' : List α} {a b : ℕ} (h1 : Seg d P H W a W')
    (h2 : Seg d P H W' b W'') : Seg d P H W (a + b) W'' := by
  refine ⟨by rw [Nat.add_comm, Function.iterate_add_apply, h1.1, h2.1], fun m hm => ?_⟩
  by_cases hma : m < a
  · exact h1.2 m hma
  · obtain ⟨j, rfl⟩ : ∃ j, m = a + j := ⟨m - a, by omega⟩
    rw [Nat.add_comm, Function.iterate_add_apply, h1.1]
    exact h2.2 j (by omega)

variable {d P} in
theorem Seg.congr {H : α} {W W' V V' : List α} {n : ℕ} (h : Seg d P H W n W') (hV : W = V)
    (hV' : W' = V') : Seg d P H V n V' := hV ▸ hV' ▸ h

theorem mem_of_mem_reads {X : List α} : ∀ {φ : ℕ} {y : α}, y ∈ reads d φ X → y ∈ X := by
  induction X with
  | nil => intro φ y h; simp at h
  | cons x X ih =>
    intro φ y h
    cases φ with
    | zero =>
      rw [reads_zero_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    | succ φ =>
      rw [reads_succ_cons] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A chunk without the letter `H` is a segment. -/
theorem seg_chunk {H : α} (hd : 1 ≤ d) (X Y : List α) {φ : ℕ} (hφ : φ < d) (hY : d ≤ Y.length)
    (hX : H ∉ X) :
    Seg d P H ((X ++ Y).drop φ) (reads d φ X).length
      ((Y ++ (reads d φ X).flatMap P).drop (nph d φ X)) := by
  obtain ⟨h1, h2⟩ := run_chunk d P hd X φ Y hφ hY
  refine ⟨h1, fun m hm => ⟨(h2 m hm).1, ?_⟩⟩
  rw [(h2 m hm).2]
  intro he
  simp only [Option.some.injEq] at he
  exact hX (mem_of_mem_reads d (he ▸ List.getElem_mem hm))

/-- The reads of a concatenation of rows of length `d`. -/
theorem reads_flatMap {β : Type*} (hd : 1 ≤ d) (f : β → List α) (g : β → α) {φ : ℕ}
    (hφ : φ < d) (hf : ∀ b, (f b).length = d) (hg : ∀ b, (f b)[φ]? = some (g b)) (I : List β) :
    reads d φ (I.flatMap f) = I.map g ∧ nph d φ (I.flatMap f) = φ := by
  induction I with
  | nil => simp
  | cons b I ih =>
    rw [List.flatMap_cons, reads_append, nph_append]
    obtain ⟨r1, r2⟩ := reads_row d hd (f b) (hf b) φ hφ
    rw [r1, r2, ih.1, ih.2]
    have := hg b
    rw [List.getElem?_eq_getElem (by rw [hf b]; exact hφ), Option.some.injEq] at this
    simp [this]

end GTag

namespace GProg

open GTag

variable (G : GProg)

/-- The letter of kind `kd`, location `ℓ` and index `t`. -/
def lt (kd ℓ t : ℕ) : ℕ := kd + 10 * t + 640 * ℓ

theorem lt_kind {kd ℓ t : ℕ} (hk : kd < 10) (ht : t < 64) : lt kd ℓ t % 10 = kd := by
  unfold lt; omega
theorem lt_idx {kd ℓ t : ℕ} (hk : kd < 10) (ht : t < 64) : lt kd ℓ t / 10 % 64 = t := by
  unfold lt; omega
theorem lt_loc {kd ℓ t : ℕ} (hk : kd < 10) (ht : t < 64) : lt kd ℓ t / 640 = ℓ := by
  unfold lt; omega

/-- A block of thirty letters. -/
def blk (kd ℓ : ℕ) : List ℕ := (List.range 30).map (lt kd ℓ)

/-- The junk block. -/
def junk : List ℕ := blk 0 0

/-- The halting block: the letter `H = 1` followed by junk letters. -/
def hblk : List ℕ := 1 :: List.replicate 29 0

/-- The division sequence `E ℓ` of `30 + 30/k` letters. -/
def eseq (k ℓ : ℕ) : List ℕ := (List.range (30 + 30 / k)).map (lt 3 ℓ)

/-- The instruction at a location, the locations from `len` on looping. -/
def ins (ℓ : ℕ) : GInstr := if ℓ < G.len then G.code ℓ else .mul 1 G.len

/-- A jump target folded into `0, …, len`. -/
def cl (n : ℕ) : ℕ := min n G.len

/-- The productions. -/
def tagP (x : ℕ) : List ℕ :=
  if x % 10 = 2 then
    if x / 10 % 64 = 0 then
      match G.ins (x / 640) with
      | .mul k nx => (List.replicate k (blk 2 (G.cl nx))).flatten
      | .div k _ _ => eseq k (x / 640)
      | .acc => junk
    else junk
  else if x % 10 = 3 then (if x / 10 % 64 = 0 then blk 4 (x / 640) else blk 5 (x / 640))
  else if x % 10 = 4 then
    (if x / 10 % 64 = 0 then
      (match G.ins (x / 640) with | .div _ y _ => blk 2 (G.cl y) | _ => junk) else junk)
  else if x % 10 = 5 then
    (if x / 10 % 64 = 0 then junk else
      (match G.ins (x / 640) with | .div _ _ n => blk 2 (G.cl n) | _ => junk))
  else if x % 10 = 6 then
    match G.ins (x / 640) with
    | .mul _ nx => blk 6 (G.cl nx)
    | .div _ _ _ => blk 7 (x / 640)
    | .acc => hblk
  else if x % 10 = 7 then
    List.replicate (x / 10 % 64) 0 ++ blk (if x / 10 % 64 = 0 then 8 else 9) (x / 640)
  else if x % 10 = 8 then (match G.ins (x / 640) with | .div _ y _ => blk 6 (G.cl y) | _ => junk)
  else if x % 10 = 9 then (match G.ins (x / 640) with | .div _ _ n => blk 6 (G.cl n) | _ => junk)
  else junk

/-! ### Evaluating the productions -/

section eval

variable {G}
variable {ℓ t : ℕ} (ht : t < 64)
include ht

theorem P_junk : G.tagP (lt 0 ℓ t) = junk := by
  simp [tagP, lt_kind (show 0 < 10 by norm_num) ht]

theorem P_H : G.tagP (lt 1 ℓ t) = junk := by
  simp [tagP, lt_kind (show 1 < 10 by norm_num) ht]

theorem P_B_mul {k nx : ℕ} (h : G.ins ℓ = .mul k nx) (h0 : t = 0) :
    G.tagP (lt 2 ℓ t) = (List.replicate k (blk 2 (G.cl nx))).flatten := by
  subst h0
  simp [tagP, lt_kind (show 2 < 10 by norm_num) ht, lt_idx (show 2 < 10 by norm_num) ht,
    lt_loc (show 2 < 10 by norm_num) ht, h]

theorem P_B_div {k y n : ℕ} (h : G.ins ℓ = .div k y n) (h0 : t = 0) :
    G.tagP (lt 2 ℓ t) = eseq k ℓ := by
  subst h0
  simp [tagP, lt_kind (show 2 < 10 by norm_num) ht, lt_idx (show 2 < 10 by norm_num) ht,
    lt_loc (show 2 < 10 by norm_num) ht, h]

theorem P_B_acc (h : G.ins ℓ = .acc) : G.tagP (lt 2 ℓ t) = junk := by
  obtain rfl | h0 := eq_or_ne t 0 <;>
  simp [tagP, lt_kind (show 2 < 10 by norm_num) ht, lt_idx (show 2 < 10 by norm_num) ht,
    lt_loc (show 2 < 10 by norm_num) ht, h, *]

theorem P_E : G.tagP (lt 3 ℓ t) = if t = 0 then blk 4 ℓ else blk 5 ℓ := by
  simp [tagP, lt_kind (show 3 < 10 by norm_num) ht, lt_idx (show 3 < 10 by norm_num) ht,
    lt_loc (show 3 < 10 by norm_num) ht]

theorem P_Q {k y n : ℕ} (h : G.ins ℓ = .div k y n) :
    G.tagP (lt 4 ℓ t) = if t = 0 then blk 2 (G.cl y) else junk := by
  obtain rfl | h0 := eq_or_ne t 0 <;>
  simp [tagP, lt_kind (show 4 < 10 by norm_num) ht, lt_idx (show 4 < 10 by norm_num) ht,
    lt_loc (show 4 < 10 by norm_num) ht, h]

theorem P_C {k y n : ℕ} (h : G.ins ℓ = .div k y n) :
    G.tagP (lt 5 ℓ t) = if t = 0 then junk else blk 2 (G.cl n) := by
  obtain rfl | h0 := eq_or_ne t 0 <;>
  simp [tagP, lt_kind (show 5 < 10 by norm_num) ht, lt_idx (show 5 < 10 by norm_num) ht,
    lt_loc (show 5 < 10 by norm_num) ht, h]

theorem P_M_mul {k nx : ℕ} (h : G.ins ℓ = .mul k nx) : G.tagP (lt 6 ℓ t) = blk 6 (G.cl nx) := by
  simp [tagP, lt_kind (show 6 < 10 by norm_num) ht, lt_loc (show 6 < 10 by norm_num) ht, h]

theorem P_M_div {k y n : ℕ} (h : G.ins ℓ = .div k y n) : G.tagP (lt 6 ℓ t) = blk 7 ℓ := by
  simp [tagP, lt_kind (show 6 < 10 by norm_num) ht, lt_loc (show 6 < 10 by norm_num) ht, h]

theorem P_M_acc (h : G.ins ℓ = .acc) : G.tagP (lt 6 ℓ t) = hblk := by
  simp [tagP, lt_kind (show 6 < 10 by norm_num) ht, lt_loc (show 6 < 10 by norm_num) ht, h]

theorem P_M1 : G.tagP (lt 7 ℓ t) = List.replicate t 0 ++ blk (if t = 0 then 8 else 9) ℓ := by
  simp [tagP, lt_kind (show 7 < 10 by norm_num) ht, lt_idx (show 7 < 10 by norm_num) ht,
    lt_loc (show 7 < 10 by norm_num) ht]

theorem P_M8 {k y n : ℕ} (h : G.ins ℓ = .div k y n) : G.tagP (lt 8 ℓ t) = blk 6 (G.cl y) := by
  simp [tagP, lt_kind (show 8 < 10 by norm_num) ht, lt_loc (show 8 < 10 by norm_num) ht, h]

theorem P_M9 {k y n : ℕ} (h : G.ins ℓ = .div k y n) : G.tagP (lt 9 ℓ t) = blk 6 (G.cl n) := by
  simp [tagP, lt_kind (show 9 < 10 by norm_num) ht, lt_loc (show 9 < 10 by norm_num) ht, h]

end eval

theorem P_zero : G.tagP 0 = junk := by simpa [lt] using G.P_junk (ℓ := 0) (t := 0) (by norm_num)

/-! ### Blocks and segments -/

theorem blk_length (kd ℓ : ℕ) : (blk kd ℓ).length = 30 := by simp [blk]

theorem blk_get {kd ℓ φ : ℕ} (h : φ < 30) : (blk kd ℓ)[φ]? = some (lt kd ℓ φ) := by
  simp [blk, h]

theorem not_mem_blk {kd ℓ : ℕ} (hk : kd < 10) (h1 : kd ≠ 1) : 1 ∉ blk kd ℓ := by
  simp only [blk, List.mem_map, List.mem_range, not_exists, not_and]
  intro t ht he
  have := lt_kind (ℓ := ℓ) hk (show t < 64 by omega)
  rw [he] at this
  omega

theorem length_le_flatMap {β γ : Type*} (f : β → List γ) {b : β} :
    ∀ {I : List β}, b ∈ I → (f b).length ≤ (I.flatMap f).length := by
  intro I
  induction I with
  | nil => intro h; simp at h
  | cons c I ih =>
    intro h
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem not_mem_flatMap {β : Type*} (f : β → List ℕ) (h : ∀ b, 1 ∉ f b) (I : List β) :
    1 ∉ I.flatMap f := by
  simp only [List.mem_flatMap, not_exists, not_and]
  exact fun b _ => h b

/-- Reading a sequence of blocks at a common phase. -/
theorem seg_rows {β : Type*} (f : β → List ℕ) (g : β → ℕ) {φ : ℕ} (hφ : φ < 30)
    (hf : ∀ b, (f b).length = 30) (hg : ∀ b, (f b)[φ]? = some (g b)) (hno : ∀ b, 1 ∉ f b)
    (I : List β) (Y : List ℕ) (hY : 30 ≤ Y.length) :
    Seg 30 G.tagP 1 ((I.flatMap f ++ Y).drop φ) I.length
      ((Y ++ I.flatMap (fun b => G.tagP (g b))).drop φ) := by
  obtain ⟨r1, r2⟩ := reads_flatMap 30 (by norm_num) f g hφ hf hg I
  have := seg_chunk 30 G.tagP (by norm_num) (I.flatMap f) Y hφ hY (not_mem_flatMap f hno I)
  rw [r1, r2, List.length_map, List.flatMap_map] at this
  exact this

/-- Reading one block. -/
theorem seg_block (B : List ℕ) (x : ℕ) {φ : ℕ} (hφ : φ < 30) (hB : B.length = 30)
    (hx : B[φ]? = some x) (hno : 1 ∉ B) (Y : List ℕ) (hY : 30 ≤ Y.length) :
    Seg 30 G.tagP 1 ((B ++ Y).drop φ) 1 ((Y ++ G.tagP x).drop φ) := by
  have := G.seg_rows (fun _ : Unit => B) (fun _ => x) hφ (fun _ => hB) (fun _ => hx)
    (fun _ => hno) [()] Y hY
  simpa using this

/-! ### Configurations -/

/-- A `B` block or a junk block. -/
def bj (ℓ : ℕ) (b : Bool) : List ℕ := if b then blk 2 ℓ else junk

/-- The queue of a machine configuration. -/
def cfg (ℓ : ℕ) (I : List Bool) : List ℕ := I.flatMap (bj ℓ) ++ blk 6 ℓ

theorem bj_length (ℓ : ℕ) (b : Bool) : (bj ℓ b).length = 30 := by
  cases b <;> simp [bj, junk, blk_length]

theorem bj_get (ℓ : ℕ) {φ : ℕ} (hφ : φ < 30) (b : Bool) :
    (bj ℓ b)[φ]? = some (if b then lt 2 ℓ φ else lt 0 0 φ) := by
  cases b <;> simp [bj, junk, blk_get hφ]

theorem bj_no (ℓ : ℕ) (b : Bool) : 1 ∉ bj ℓ b := by
  cases b
  · exact not_mem_blk (by norm_num) (by norm_num)
  · exact not_mem_blk (by norm_num) (by norm_num)

theorem length_flatMap_bj {ℓ : ℕ} {I : List Bool} (hI : false ∈ I) :
    30 ≤ (I.flatMap (bj ℓ)).length := by
  have := length_le_flatMap (bj ℓ) hI
  rwa [bj_length] at this

theorem replicate_flatMap_bj (ℓ k : ℕ) :
    (List.replicate k true).flatMap (bj ℓ) = (List.replicate k (blk 2 ℓ)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, bj, ih]

theorem emit_mul {ℓ k nx : ℕ} (h : G.ins ℓ = .mul k nx) (I : List Bool) :
    I.flatMap (fun b => G.tagP (if b then lt 2 ℓ 0 else lt 0 0 0)) =
      (I.flatMap (fun b => if b then List.replicate k true else [false])).flatMap
        (bj (G.cl nx)) := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_append, ih]
    cases b
    · simp only [Bool.false_eq_true, if_false, P_junk (show 0 < 64 by norm_num)]
      rfl
    · simp only [if_true, P_B_mul (show 0 < 64 by norm_num) h rfl, replicate_flatMap_bj]

/-- **The multiplication round.** -/
theorem round_mul {ℓ k nx : ℕ} (h : G.ins ℓ = .mul k nx) {I : List Bool} (hI : false ∈ I) :
    Seg 30 G.tagP 1 (cfg ℓ I) (I.length + 1)
      (cfg (G.cl nx) (I.flatMap (fun b => if b then List.replicate k true else [false]))) := by
  have s1 := G.seg_rows (bj ℓ) (fun b => if b then lt 2 ℓ 0 else lt 0 0 0) (φ := 0)
    (by norm_num) (bj_length ℓ) (bj_get ℓ (by norm_num)) (bj_no ℓ) I (blk 6 ℓ)
    (by rw [blk_length])
  rw [G.emit_mul h] at s1
  have hlen : 30 ≤ ((I.flatMap (fun b => if b then List.replicate k true else [false])).flatMap
      (bj (G.cl nx))).length := by
    refine length_flatMap_bj (List.mem_flatMap.2 ⟨false, hI, by simp⟩)
  have s2 := G.seg_block (blk 6 ℓ) (lt 6 ℓ 0) (φ := 0) (by norm_num) (blk_length 6 ℓ)
    (blk_get (by norm_num)) (not_mem_blk (by norm_num) (by norm_num)) _ hlen
  rw [P_M_mul (show 0 < 64 by norm_num) h] at s2
  simpa [cfg] using s1.trans s2

theorem count_mul (k : ℕ) (I : List Bool) :
    (I.flatMap (fun b => if b then List.replicate k true else [false])).count true =
      k * I.count true := by
  induction I with
  | nil => simp
  | cons b I ih =>
    cases b <;> simp [List.count_cons, ih] <;> ring

theorem false_mem_mul (k : ℕ) {I : List Bool} (hI : false ∈ I) :
    false ∈ I.flatMap (fun b => if b then List.replicate k true else [false]) :=
  List.mem_flatMap.2 ⟨false, hI, by simp⟩

/-! ### The accepting round -/

theorem emit_acc {ℓ : ℕ} (h : G.ins ℓ = .acc) (I : List Bool) :
    I.flatMap (fun b => G.tagP (if b then lt 2 ℓ 0 else lt 0 0 0)) = I.flatMap (fun _ => junk) := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ih]
    cases b
    · simp only [Bool.false_eq_true, if_false, P_junk (show 0 < 64 by norm_num)]
    · simp only [if_true, P_B_acc (show 0 < 64 by norm_num) h]

theorem emit_junk (I : List Bool) :
    I.flatMap (fun _ => G.tagP (lt 0 0 0)) = I.flatMap (fun _ => junk) := by
  simp only [P_junk (show 0 < 64 by norm_num)]

/-- **The accepting round** ends at a queue headed by `H`. -/
theorem round_acc {ℓ : ℕ} (h : G.ins ℓ = .acc) {I : List Bool} (hI : false ∈ I) :
    Seg 30 G.tagP 1 (cfg ℓ I) (I.length + 1 + I.length) (hblk ++ I.flatMap (fun _ => junk)) := by
  have s1 := G.seg_rows (bj ℓ) (fun b => if b then lt 2 ℓ 0 else lt 0 0 0) (φ := 0)
    (by norm_num) (bj_length ℓ) (bj_get ℓ (by norm_num)) (bj_no ℓ) I (blk 6 ℓ)
    (by rw [blk_length])
  rw [G.emit_acc h] at s1
  have hlen : 30 ≤ (I.flatMap (fun _ => junk)).length := by
    have := length_le_flatMap (fun _ : Bool => junk) hI
    simpa [junk, blk_length] using this
  have s2 := G.seg_block (blk 6 ℓ) (lt 6 ℓ 0) (φ := 0) (by norm_num) (blk_length 6 ℓ)
    (blk_get (by norm_num)) (not_mem_blk (by norm_num) (by norm_num)) _ hlen
  rw [P_M_acc (show 0 < 64 by norm_num) h] at s2
  have s3 := G.seg_rows (fun _ : Bool => junk) (fun _ => lt 0 0 0) (φ := 0) (by norm_num)
    (fun _ => blk_length 0 0) (fun _ => blk_get (by norm_num))
    (fun _ => not_mem_blk (by norm_num) (by norm_num)) I hblk (by simp [hblk])
  rw [G.emit_junk] at s3
  simpa [cfg] using (s1.trans s2).trans s3

/-! ### The division round -/

/-- The phase after `j` division sequences. -/
def ph (k j : ℕ) : ℕ := (30 - 30 / k * (j % k)) % 30

theorem ph_lt (k j : ℕ) : ph k j < 30 := Nat.mod_lt _ (by norm_num)

theorem not_mem_eseq (k ℓ : ℕ) (hk : 1 ≤ k) : 1 ∉ eseq k ℓ := by
  simp only [eseq, List.mem_map, List.mem_range, not_exists, not_and]
  intro t ht he
  have h30 : 30 / k ≤ 30 := Nat.div_le_self _ _
  have := lt_kind (kd := 3) (ℓ := ℓ) (by norm_num) (show t < 64 by omega)
  rw [he] at this
  omega

theorem reads_eseq {k ℓ j : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 5) :
    reads 30 (ph k j) (eseq k ℓ) =
        (if j % k = 0 then [lt 3 ℓ 0, lt 3 ℓ 30] else [lt 3 ℓ (ph k j)]) ∧
      nph 30 (ph k j) (eseq k ℓ) = ph k (j + 1) := by
  have hsplit : eseq k ℓ = blk 3 ℓ ++ (List.range (30 / k)).map (fun i => lt 3 ℓ (30 + i)) := by
    simp [eseq, blk, List.range_add, Function.comp_def]
  have hφ := ph_lt k j
  obtain ⟨r1, r2⟩ := reads_row 30 (by norm_num) (blk 3 ℓ) (blk_length 3 ℓ) (ph k j) hφ
  rw [hsplit, reads_append, nph_append, r1, r2]
  have hget : (blk 3 ℓ)[ph k j]'(by rw [blk_length]; exact hφ) = lt 3 ℓ (ph k j) := by
    simp [blk]
  rw [hget]
  set T := (List.range (30 / k)).map (fun i => lt 3 ℓ (30 + i)) with hT
  have hTl : T.length = 30 / k := by simp [hT]
  by_cases hj : j % k = 0
  · have h0 : ph k j = 0 := by unfold ph; rw [hj]; simp
    rw [if_pos hj, h0]
    have hlt : 0 < T.length := by rw [hTl]; rcases hk with rfl | rfl | rfl <;> norm_num
    obtain ⟨t1, t2⟩ := reads_of_lt 30 T 0 hlt
    obtain ⟨t3, t4⟩ := reads_of_le 30 (T.drop (0 + 1)) (30 - 1)
      (by simp [hTl]; rcases hk with rfl | rfl | rfl <;> norm_num)
    rw [t1, t2, t3, t4]
    refine ⟨by simp [hT], ?_⟩
    simp only [List.length_drop, hTl]
    unfold ph
    rcases hk with rfl | rfl | rfl <;> omega
  · rw [if_neg hj]
    obtain ⟨t3, t4⟩ := reads_of_le 30 T (ph k j)
      (by rw [hTl]; unfold ph; rcases hk with rfl | rfl | rfl <;> omega)
    rw [t3, t4, hTl]
    refine ⟨rfl, ?_⟩
    unfold ph
    rcases hk with rfl | rfl | rfl <;> omega

/-- A division sequence or a junk block. -/
def be (k ℓ : ℕ) (b : Bool) : List ℕ := if b then eseq k ℓ else junk

/-- The `Q`/`C`/junk items emitted by reading the division sequences. -/
def st2 (k : ℕ) : ℕ → List Bool → List ℕ
  | _, [] => []
  | j, false :: I => 0 :: st2 k j I
  | j, true :: I => (if j % k = 0 then [1, 2] else [2]) ++ st2 k (j + 1) I

/-- The block of an item: junk, `Q` or `C`. -/
def qc (ℓ m : ℕ) : List ℕ := if m = 0 then junk else if m = 1 then blk 4 ℓ else blk 5 ℓ

theorem reads_be {k ℓ : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 5) (I : List Bool) : ∀ j,
    (reads 30 (ph k j) (I.flatMap (be k ℓ))).flatMap G.tagP = (st2 k j I).flatMap (qc ℓ) ∧
      nph 30 (ph k j) (I.flatMap (be k ℓ)) = ph k (j + I.count true) := by
  induction I with
  | nil => intro j; simp [st2]
  | cons b I ih =>
    intro j
    rw [List.flatMap_cons, reads_append, nph_append, List.flatMap_append]
    cases b
    · obtain ⟨r1, r2⟩ := reads_row 30 (by norm_num) (be k ℓ false) (by simp [be, junk, blk_length])
        (ph k j) (ph_lt k j)
      rw [r1, r2, (ih j).1, (ih j).2]
      have hg : (be k ℓ false)[ph k j]'(by simp [be, junk, blk_length, ph_lt]) = lt 0 0 (ph k j) := by
        simp [be, junk, blk]
      refine ⟨?_, by simp⟩
      simp only [hg, List.flatMap_cons, List.flatMap_nil, List.append_nil, st2,
        P_junk (show ph k j < 64 by have := ph_lt k j; omega)]
      simp [qc]
    · obtain ⟨r1, r2⟩ := reads_eseq (ℓ := ℓ) (j := j) hk
      simp only [be, if_true] at r1 r2 ⊢
      rw [r1, r2, (ih (j + 1)).1, (ih (j + 1)).2]
      refine ⟨?_, by simp [List.count_cons]; ring_nf⟩
      simp only [st2]
      by_cases hj : j % k = 0
      · simp only [if_pos hj, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          P_E (show 0 < 64 by norm_num), P_E (show 30 < 64 by norm_num), List.cons_append,
          List.nil_append, List.append_assoc]
        simp [qc]
      · have hph : ph k j ≠ 0 := by unfold ph; rcases hk with rfl | rfl | rfl <;> omega
        simp only [if_neg hj, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          P_E (show ph k j < 64 by have := ph_lt k j; omega), if_neg hph, List.cons_append,
          List.nil_append]
        simp [qc]

theorem zero_mem_st2 (k : ℕ) {I : List Bool} (hI : false ∈ I) : ∀ j, 0 ∈ st2 k j I := by
  induction I with
  | nil => simp at hI
  | cons b I ih =>
    intro j
    cases b
    · simp [st2]
    · have h : false ∈ I := by simpa using hI
      simp only [st2]
      exact List.mem_append_right _ (ih h (j + 1))

/-- The selector of the second pass. -/
def sel (c m : ℕ) : Bool := decide (m ≠ 0 ∧ ((c = 0 ∧ m = 1) ∨ (c ≠ 0 ∧ m ≠ 1)))

theorem count_sel {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 5) (c : ℕ) (I : List Bool) : ∀ j,
    ((st2 k j I).map (sel c)).count true + (if c = 0 then (j + k - 1) / k else 0) =
      (if c = 0 then (j + I.count true + k - 1) / k else I.count true) := by
  induction I with
  | nil => intro j; by_cases hc : c = 0 <;> simp [st2, hc]
  | cons b I ih =>
    intro j
    have := ih (j + 1)
    have h0 := ih j
    cases b
    · by_cases hc : c = 0 <;> simp_all [st2, sel, List.count_cons]
    · by_cases hc : c = 0
      · simp only [hc, if_true] at this ⊢
        simp only [st2, List.map_append, List.count_append]
        by_cases hj : j % k = 0
        · simp only [if_pos hj]
          simp [sel, List.count_cons, List.count_nil] at this ⊢
          rcases hk with rfl | rfl | rfl <;> omega
        · simp only [if_neg hj]
          simp [sel, List.count_cons, List.count_nil] at this ⊢
          rcases hk with rfl | rfl | rfl <;> omega
      · simp only [hc, if_false, add_zero] at this ⊢
        simp only [st2, List.map_append, List.count_append]
        by_cases hj : j % k = 0
        · simp only [if_pos hj]
          simp [sel, hc, List.count_cons, List.count_nil] at this ⊢
          omega
        · simp only [if_neg hj]
          simp [sel, hc, List.count_cons, List.count_nil] at this ⊢
          omega

/-- The letter of an item block at a phase. -/
def qcl (ℓ m φ : ℕ) : ℕ := if m = 0 then lt 0 0 φ else if m = 1 then lt 4 ℓ φ else lt 5 ℓ φ

theorem emit_sel {ℓ k y n c : ℕ} (h : G.ins ℓ = .div k y n) (hc : c < 30) (I2 : List ℕ) :
    I2.flatMap (fun m => G.tagP (qcl ℓ m c)) =
      (I2.map (sel c)).flatMap (bj (if c = 0 then G.cl y else G.cl n)) := by
  induction I2 with
  | nil => rfl
  | cons m I2 ih =>
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, ih]
    congr 1
    have hc' : c < 64 := by omega
    by_cases hm0 : m = 0
    · simp [qcl, hm0, sel, bj, P_junk hc']
    · by_cases hm1 : m = 1
      · by_cases hc0 : c = 0
        · subst hc0; simp [qcl, hm1, sel, bj, P_Q (show (0 : ℕ) < 64 by norm_num) h]
        · simp [qcl, hm1, sel, bj, P_Q hc' h, hc0]
      · by_cases hc0 : c = 0
        · subst hc0; simp [qcl, hm0, hm1, sel, bj, P_C (show (0 : ℕ) < 64 by norm_num) h]
        · simp [qcl, hm0, hm1, sel, bj, P_C hc' h, hc0]

theorem ph_eq_zero {k N : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 5) : ph k N = 0 ↔ k ∣ N := by
  rw [Nat.dvd_iff_mod_eq_zero]
  unfold ph
  rcases hk with rfl | rfl | rfl <;> omega

/-- **The division round.** -/
theorem round_div {ℓ k y n : ℕ} (h : G.ins ℓ = .div k y n) (hk : k = 2 ∨ k = 3 ∨ k = 5)
    {I : List Bool} (hI : false ∈ I) :
    ∃ m I', 1 ≤ m ∧ false ∈ I' ∧
      I'.count true = (if k ∣ I.count true then I.count true / k else I.count true) ∧
      Seg 30 G.tagP 1 (cfg ℓ I) m (cfg (if k ∣ I.count true then G.cl y else G.cl n) I') := by
  have hk1 : 1 ≤ k := by rcases hk with rfl | rfl | rfl <;> norm_num
  -- the division sequences
  have s1 := G.seg_rows (bj ℓ) (fun b => if b then lt 2 ℓ 0 else lt 0 0 0) (φ := 0)
    (by norm_num) (bj_length ℓ) (bj_get ℓ (by norm_num)) (bj_no ℓ) I (blk 6 ℓ)
    (by rw [blk_length])
  have hE : I.flatMap (fun b => G.tagP (if b then lt 2 ℓ 0 else lt 0 0 0)) = I.flatMap (be k ℓ) := by
    congr 1
    funext b
    cases b
    · simp [be, P_junk (show 0 < 64 by norm_num)]
    · simp [be, P_B_div (show 0 < 64 by norm_num) h rfl]
  rw [hE] at s1
  have hlen1 : 30 ≤ (I.flatMap (be k ℓ)).length := by
    have := length_le_flatMap (be k ℓ) hI
    simpa [be, junk, blk_length] using this
  have s2 := G.seg_block (blk 6 ℓ) (lt 6 ℓ 0) (φ := 0) (by norm_num) (blk_length 6 ℓ)
    (blk_get (by norm_num)) (not_mem_blk (by norm_num) (by norm_num)) _ hlen1
  rw [P_M_div (show 0 < 64 by norm_num) h] at s2
  -- reading the division sequences
  have hno : 1 ∉ I.flatMap (be k ℓ) := not_mem_flatMap _ (fun b => by
    cases b
    · exact not_mem_blk (by norm_num) (by norm_num)
    · exact not_mem_eseq k ℓ hk1) I
  have s3 := seg_chunk 30 G.tagP (by norm_num) (I.flatMap (be k ℓ)) (blk 7 ℓ) (φ := 0)
    (by norm_num) (by rw [blk_length]) hno
  obtain ⟨e1, e2⟩ := G.reads_be hk (ℓ := ℓ) I 0
  have hph0 : ph k 0 = 0 := by simp [ph]
  simp only [hph0, zero_add] at e1 e2
  rw [e1, e2] at s3
  set c := ph k (I.count true) with hc_def
  have hc : c < 30 := ph_lt _ _
  set I2 := st2 k 0 I with hI2
  have h0I2 : 0 ∈ I2 := zero_mem_st2 k hI 0
  have hlen2 : 30 ≤ (I2.flatMap (qc ℓ)).length := by
    have := length_le_flatMap (qc ℓ) h0I2
    simpa [qc, junk, blk_length] using this
  -- the branch marker
  have s4 := G.seg_block (blk 7 ℓ) (lt 7 ℓ c) hc (blk_length 7 ℓ) (blk_get hc)
    (not_mem_blk (by norm_num) (by norm_num)) _ hlen2
  rw [P_M1 (show c < 64 by omega)] at s4
  -- the second pass
  have s5 := G.seg_rows (qc ℓ) (fun m => qcl ℓ m c) hc
    (fun m => by by_cases h0 : m = 0 <;> by_cases h1 : m = 1 <;> simp [qc, junk, blk_length, h0, h1])
    (fun m => by by_cases h0 : m = 0 <;> by_cases h1 : m = 1 <;> simp [qc, qcl, junk, blk_get hc, h0, h1])
    (fun m => by
      by_cases h0 : m = 0 <;> by_cases h1 : m = 1 <;> simp only [qc, junk, h0, h1, if_true, if_false] <;>
        exact not_mem_blk (by norm_num) (by norm_num))
    I2 (List.replicate c 0 ++ blk (if c = 0 then 8 else 9) ℓ) (by simp [blk_length])
  rw [G.emit_sel h hc] at s5
  have e5 : (List.replicate c 0 ++ blk (if c = 0 then 8 else 9) ℓ ++
      (I2.map (sel c)).flatMap (bj (if c = 0 then G.cl y else G.cl n))).drop c =
      blk (if c = 0 then 8 else 9) ℓ ++
        (I2.map (sel c)).flatMap (bj (if c = 0 then G.cl y else G.cl n)) := by
    rw [List.append_assoc, List.drop_left' (by simp)]
  rw [e5] at s5
  set I3 := I2.map (sel c) with hI3
  have hf3 : false ∈ I3 := List.mem_map.2 ⟨0, h0I2, by simp [sel]⟩
  have s6 := G.seg_block (blk (if c = 0 then 8 else 9) ℓ) (lt (if c = 0 then 8 else 9) ℓ 0)
    (φ := 0) (by norm_num) (blk_length _ ℓ) (blk_get (by norm_num))
    (not_mem_blk (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)) _
    (length_flatMap_bj (ℓ := if c = 0 then G.cl y else G.cl n) hf3)
  have hM2 : G.tagP (lt (if c = 0 then 8 else 9) ℓ 0) = blk 6 (if c = 0 then G.cl y else G.cl n) := by
    by_cases hc0 : c = 0
    · simp only [hc0, if_true]; exact P_M8 (show 0 < 64 by norm_num) h
    · simp only [hc0, if_false]; exact P_M9 (show 0 < 64 by norm_num) h
  rw [hM2] at s6
  have hz : (0 + k - 1) / k = 0 := by rcases hk with rfl | rfl | rfl <;> norm_num
  have hiff := ph_eq_zero (N := I.count true) hk
  refine ⟨I.length + 1 + (reads 30 0 (I.flatMap (be k ℓ))).length + 1 + I2.length + 1, I3,
    by omega, hf3, ?_, ?_⟩
  · show (List.map (sel c) (st2 k 0 I)).count true = _
    have hs := count_sel hk c I 0
    by_cases hd : k ∣ I.count true
    · have hc0 : c = 0 := hiff.2 hd
      rw [if_pos hc0, if_pos hc0, hz, add_zero, zero_add] at hs
      rw [if_pos hd, hs]
      obtain ⟨q, hq⟩ := hd
      rw [hq]
      rcases hk with rfl | rfl | rfl <;> omega
    · have hc0 : c ≠ 0 := fun h => hd (hiff.1 h)
      rw [if_neg hc0, if_neg hc0, add_zero] at hs
      rw [if_neg hd, hs]
  · have hbr : (if c = 0 then G.cl y else G.cl n) =
        (if k ∣ I.count true then G.cl y else G.cl n) := by
      by_cases hd : k ∣ I.count true
      · rw [if_pos (hiff.2 hd), if_pos hd]
      · rw [if_neg (fun h => hd (hiff.1 h)), if_neg hd]
    rw [← hbr]
    have := (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6)
    simpa [cfg] using this

/-! ### The whole run -/

/-- The machine is admissible for the tag simulation: multipliers `1, …, 5` and divisors
`2, 3, 5`. -/
structure WF (G : GProg) : Prop where
  mul_le : ∀ ℓ k nx, G.code ℓ = .mul k nx → 1 ≤ k ∧ k ≤ 5
  div_k : ∀ ℓ k y n, G.code ℓ = .div k y n → k = 2 ∨ k = 3 ∨ k = 5

/-- The deterministic successor configuration (the accepting halt and the loop are fixed). -/
def gnext (c : ℕ × ℕ) : ℕ × ℕ :=
  match G.ins c.1 with
  | .mul k nx => (G.cl nx, k * c.2)
  | .div k y n => if k ∣ c.2 then (G.cl y, c.2 / k) else (G.cl n, c.2)
  | .acc => c

/-- The initial queue for the register value `N`. -/
def tagWord (N : ℕ) : List ℕ := cfg 0 (false :: List.replicate N true)

theorem ins_of_lt {ℓ : ℕ} (h : ℓ < G.len) : G.ins ℓ = G.code ℓ := if_pos h
theorem ins_of_ge {ℓ : ℕ} (h : ¬ ℓ < G.len) : G.ins ℓ = .mul 1 G.len := if_neg h

theorem sim (hwf : G.WF) (N0 : ℕ) : ∀ i, (∀ j < i, G.ins (G.gnext^[j] (0, N0)).1 ≠ .acc) →
    ∃ T I, i ≤ T ∧ false ∈ I ∧ I.count true = (G.gnext^[i] (0, N0)).2 ∧
      Seg 30 G.tagP 1 (tagWord N0) T (cfg (G.gnext^[i] (0, N0)).1 I) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨0, false :: List.replicate N0 true, le_rfl, List.mem_cons_self, ?_, Seg.refl _ _ _ _⟩
    simp [List.count_replicate]
  | succ i ih =>
    intro hacc
    obtain ⟨T, I, hT, hI, hcnt, hseg⟩ := ih (fun j hj => hacc j (by omega))
    have hna := hacc i (by omega)
    rw [Function.iterate_succ_apply']
    set c := G.gnext^[i] (0, N0) with hc
    cases hins : G.ins c.1 with
    | mul k nx =>
      have hs := G.round_mul hins hI
      refine ⟨T + (I.length + 1), _, by omega, false_mem_mul k hI, ?_, hseg.trans ?_⟩
      · rw [count_mul, hcnt]; simp [gnext, hins]
      · simpa [gnext, hins] using hs
    | div k y n =>
      have hk : k = 2 ∨ k = 3 ∨ k = 5 := by
        by_cases hl : c.1 < G.len
        · rw [G.ins_of_lt hl] at hins; exact hwf.div_k _ _ _ _ hins
        · rw [G.ins_of_ge hl] at hins; cases hins
      obtain ⟨m, I', hm, hI', hcnt', hs⟩ := G.round_div hins hk hI
      refine ⟨T + m, I', by omega, hI', ?_, hseg.trans ?_⟩
      · rw [hcnt', hcnt]
        by_cases hd : k ∣ c.2 <;> simp [gnext, hins, hd]
      · rw [hcnt] at hs
        by_cases hd : k ∣ c.2 <;> simpa [gnext, hins, hd] using hs
    | acc => exact absurd hins hna

theorem le_len_gnext (N0 : ℕ) : ∀ i, (G.gnext^[i] (0, N0)).1 ≤ G.len := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    set c := G.gnext^[i] (0, N0)
    unfold gnext
    split
    · simp [cl]
    · split_ifs <;> simp [cl]
    · exact ih

theorem reaches_of_gnext (N0 : ℕ) : ∀ i, (G.gnext^[i] (0, N0)).1 < G.len →
    Relation.ReflTransGen G.Step (0, N0) (G.gnext^[i] (0, N0)) := by
  intro i
  induction i with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ i ih =>
    intro hlt
    have hle := G.le_len_gnext N0 i
    set c := G.gnext^[i] (0, N0) with hc
    rw [Function.iterate_succ_apply'] at hlt ⊢
    rw [← hc] at hlt ⊢
    by_cases hl : c.1 < G.len
    · have hr := ih hl
      have hins := G.ins_of_lt hl
      cases hcode : G.code c.1 with
      | mul k nx =>
        have hg : G.gnext c = (G.cl nx, k * c.2) := by simp [gnext, hins, hcode]
        rw [hg] at hlt ⊢
        have e : G.cl nx = nx := by simp [cl] at hlt ⊢; omega
        rw [e] at hlt ⊢
        exact hr.tail (by rw [show c = (c.1, c.2) from rfl]; exact GProg.Step.mul hl hcode)
      | div k y n =>
        by_cases hd : k ∣ c.2
        · have hg : G.gnext c = (G.cl y, c.2 / k) := by simp [gnext, hins, hcode, hd]
          rw [hg] at hlt ⊢
          have e : G.cl y = y := by simp [cl] at hlt ⊢; omega
          rw [e] at hlt ⊢
          exact hr.tail (by rw [show c = (c.1, c.2) from rfl]; exact GProg.Step.yes hl hcode hd)
        · have hg : G.gnext c = (G.cl n, c.2) := by simp [gnext, hins, hcode, hd]
          rw [hg] at hlt ⊢
          have e : G.cl n = n := by simp [cl] at hlt ⊢; omega
          rw [e] at hlt ⊢
          exact hr.tail (by rw [show c = (c.1, c.2) from rfl]; exact GProg.Step.no hl hcode hd)
      | acc =>
        have hg : G.gnext c = c := by simp [gnext, hins, hcode]
        rw [hg]
        exact hr
    · exfalso
      unfold gnext at hlt
      rw [G.ins_of_ge hl] at hlt
      simp [cl] at hlt

theorem gnext_of_reaches (N0 : ℕ) : ∀ c, Relation.ReflTransGen G.Step (0, N0) c →
    ∃ i, G.gnext^[i] (0, N0) = (G.cl c.1, c.2) := by
  intro c h
  induction h with
  | refl => exact ⟨0, by simp [cl]⟩
  | tail _ hs ih =>
    obtain ⟨i, hi⟩ := ih
    refine ⟨i + 1, ?_⟩
    rw [Function.iterate_succ_apply', hi]
    cases hs with
    | mul hl hc =>
      simp [gnext, G.ins_of_lt hl, hc, cl, min_eq_left (le_of_lt hl)]
    | yes hl hc hd =>
      simp [gnext, G.ins_of_lt hl, hc, cl, min_eq_left (le_of_lt hl), hd]
    | no hl hc hd =>
      simp [gnext, G.ins_of_lt hl, hc, cl, min_eq_left (le_of_lt hl), hd]

theorem reachesAcc_iff_gnext (N0 : ℕ) :
    G.ReachesAcc N0 ↔ ∃ i, G.ins (G.gnext^[i] (0, N0)).1 = .acc := by
  constructor
  · rintro ⟨ℓ, N, hℓ, hc, hr⟩
    obtain ⟨i, hi⟩ := G.gnext_of_reaches N0 _ hr
    refine ⟨i, ?_⟩
    rw [hi]
    have e : G.cl ℓ = ℓ := min_eq_left (le_of_lt hℓ)
    simp only [e]
    rw [G.ins_of_lt hℓ, hc]
  · rintro ⟨i, hi⟩
    have hl : (G.gnext^[i] (0, N0)).1 < G.len := by
      by_contra hl
      rw [G.ins_of_ge hl] at hi
      cases hi
    refine ⟨_, _, hl, ?_, G.reaches_of_gnext N0 i hl⟩
    rw [← G.ins_of_lt hl, hi]

/-- **The 30-tag system reads `H` exactly when the machine accepts**, and never runs short
before reading `H`. -/
theorem tag_iff (hwf : G.WF) (N0 : ℕ) :
    (∀ n, (∀ m < n, ((step 30 G.tagP)^[m] (tagWord N0)).head? ≠ some 1) →
        30 ≤ ((step 30 G.tagP)^[n] (tagWord N0)).length) ∧
      ((∃ n, ((step 30 G.tagP)^[n] (tagWord N0)).head? = some 1) ↔ G.ReachesAcc N0) := by
  classical
  rw [G.reachesAcc_iff_gnext]
  by_cases hA : ∃ i, G.ins (G.gnext^[i] (0, N0)).1 = .acc
  · -- the halting letter is read after the first accepting configuration
    have hmin : ∀ j < Nat.find hA, G.ins (G.gnext^[j] (0, N0)).1 ≠ .acc :=
      fun j hj => Nat.find_min hA hj
    obtain ⟨T, I, -, hI, -, hseg⟩ := G.sim hwf N0 _ hmin
    have hs := hseg.trans (G.round_acc (Nat.find_spec hA) hI)
    set nH := T + (I.length + 1 + I.length)
    have hHead : ((step 30 G.tagP)^[nH] (tagWord N0)).head? = some 1 := by
      rw [hs.1]; simp [hblk]
    have hHlen : 30 ≤ ((step 30 G.tagP)^[nH] (tagWord N0)).length := by
      rw [hs.1]; simp [hblk]
    refine ⟨fun n hn => ?_, ⟨fun _ => hA, fun _ => ⟨nH, hHead⟩⟩⟩
    rcases lt_trichotomy n nH with h | h | h
    · exact (hs.2 n h).1
    · rw [h]; exact hHlen
    · exact absurd hHead (hn nH h)
  · push_neg at hA
    have hsim : ∀ n, n < (Classical.choose (G.sim hwf N0 (n + 1) (fun j _ => hA j))) := fun n => by
      have := Classical.choose_spec (G.sim hwf N0 (n + 1) (fun j _ => hA j))
      obtain ⟨I, h, -⟩ := this
      omega
    have hseg : ∀ n, 30 ≤ ((step 30 G.tagP)^[n] (tagWord N0)).length ∧
        ((step 30 G.tagP)^[n] (tagWord N0)).head? ≠ some 1 := fun n => by
      have := Classical.choose_spec (G.sim hwf N0 (n + 1) (fun j _ => hA j))
      obtain ⟨I, -, -, -, hs⟩ := this
      exact hs.2 n (hsim n)
    refine ⟨fun n _ => (hseg n).1, ⟨fun ⟨n, hn⟩ => absurd hn (hseg n).2, fun ⟨i, hi⟩ => absurd hi (hA i)⟩⟩

end GProg

end Jones1980
