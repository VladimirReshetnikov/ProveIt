import Diophantine.Paper1980.TagBinary91
import Diophantine.Paper1980.Universal100

/-!
# The 91-operation tag certificate is universal

The layers assemble (`EXPLORATION_PRODUCT_COORDINATE_TAG.md` cites Neary, STACS 2015, for the
universality of binary tag systems with the productions `0 → 0`, `1 → u`; here it is proved):

* a recursively enumerable set is accepted by a three-counter program (`TMUniv.re_tm0`,
  `TMCounter.accepts_iff`);
* the program compiles to a single-register machine (`CProgram.accepts_iff_reachesAcc`), which
  is admissible (`compile_wf`);
* the 30-tag system of that machine reads its halting letter exactly on acceptance
  (`GProg.tag_iff`), with the shape needed at that moment (`tag_shape`), and its productions are
  nonempty, bounded and closed under the letter bound (`tagP_ok`, `dtag_ok`);
* the binary track system halts exactly when the 30-tag system reads its halting letter, under
  the certificate's promises (`DTag.bin_iff`);
* the constants of a binary system with `C = 3^γ` above the admitted bound satisfy the
  fixed-constant contract (`tagConst_ok`), and `tag_iff91` turns halting into solvability.

`tag91_re`: for every recursively enumerable `S` there is one binary tag system whose constants
`k, Ut, ε, B, cc` are fixed, such that `x ∈ S` exactly when the 18 equations are solvable at the
encoded input `(content W_x, 3^|W_x|)` with `C = 3^γ_x`.
-/

namespace Jones1980

open TagSys Ternary

namespace CProgram

variable (M : CProgram)
theorem prime3_cases (r : Fin 3) : prime3 r = 2 ∨ prime3 r = 3 ∨ prime3 r = 5 := by
  unfold prime3; split_ifs <;> simp

theorem prime3_bounds (r : Fin 3) : 1 ≤ prime3 r ∧ prime3 r ≤ 5 := by
  rcases prime3_cases r with h | h | h <;> omega

theorem compile_wf : (M.compile).WF := by
  constructor
  · intro ℓ k nx h
    unfold compile at h
    dsimp only at h
    split_ifs at h <;> (repeat' split at h) <;> simp only [GInstr.mul.injEq, reduceCtorEq] at h <;>
      (try obtain ⟨rfl, -⟩ := h) <;> first | omega | exact prime3_bounds _
  · intro ℓ k y n h
    unfold compile at h
    dsimp only at h
    split_ifs at h <;> (repeat' split at h) <;> simp only [GInstr.div.injEq, reduceCtorEq] at h <;>
      (try obtain ⟨rfl, -⟩ := h) <;> first | omega | exact prime3_cases _

end CProgram

namespace GProg

variable (G : GProg)

theorem mem_blk_lt {kd ℓ y : ℕ} (hk : kd < 10) (h : y ∈ blk kd ℓ) : y < 640 * (ℓ + 1) := by
  simp only [blk, List.mem_map, List.mem_range] at h
  obtain ⟨t, ht, rfl⟩ := h
  unfold lt; omega

theorem ins_mul {ℓ k nx : ℕ} (hwf : G.WF) (h : G.ins ℓ = .mul k nx) : 1 ≤ k ∧ k ≤ 5 := by
  unfold ins at h
  split_ifs at h with hl
  · exact hwf.mul_le _ _ _ h
  · cases h; omega

theorem cl_le (n : ℕ) : G.cl n ≤ G.len := min_le_right _ _

set_option maxHeartbeats 2000000 in
/-- The productions are nonempty, of length at most `150`, and stay below the location bound. -/
theorem tagP_ok (hwf : G.WF) (x : ℕ) :
    1 ≤ (G.tagP x).length ∧ (G.tagP x).length ≤ 150 ∧
      ∀ y ∈ G.tagP x, y < 640 * (max (x / 640) G.len + 1) := by
  have hb : ∀ kd ℓ, kd < 10 → ℓ ≤ max (x / 640) G.len →
      1 ≤ (blk kd ℓ).length ∧ (blk kd ℓ).length ≤ 150 ∧
        ∀ y ∈ blk kd ℓ, y < 640 * (max (x / 640) G.len + 1) := fun kd ℓ hk hl =>
    ⟨by simp [blk_length], by simp [blk_length], fun y hy => by
      have := mem_blk_lt hk hy
      have : 640 * (ℓ + 1) ≤ 640 * (max (x / 640) G.len + 1) := by omega
      omega⟩
  have hcl : ∀ n, G.cl n ≤ max (x / 640) G.len := fun n => le_trans (G.cl_le n) (le_max_right _ _)
  have hx : x / 640 ≤ max (x / 640) G.len := le_max_left _ _
  have hj : 1 ≤ junk.length ∧ junk.length ≤ 150 ∧ ∀ y ∈ junk, y < 640 * (max (x / 640) G.len + 1) :=
    hb 0 0 (by norm_num) (Nat.zero_le _)
  have hH : 1 ≤ hblk.length ∧ hblk.length ≤ 150 ∧ ∀ y ∈ hblk, y < 640 * (max (x / 640) G.len + 1) := by
    refine ⟨by simp [hblk], by simp [hblk], fun y hy => ?_⟩
    simp only [hblk, List.mem_cons, List.mem_replicate] at hy
    have : 640 ≤ 640 * (max (x / 640) G.len + 1) := by omega
    omega
  have hpos : 0 < 640 * (max (x / 640) G.len + 1) := by positivity
  have hM1 : ∀ m, m < 10 → 1 ≤ (List.replicate (x / 10 % 64) 0 ++ blk m (x / 640)).length ∧
      (List.replicate (x / 10 % 64) 0 ++ blk m (x / 640)).length ≤ 150 ∧
      ∀ y ∈ List.replicate (x / 10 % 64) 0 ++ blk m (x / 640),
        y < 640 * (max (x / 640) G.len + 1) := fun m hm => by
    obtain ⟨b1, b2, b3⟩ := hb m (x / 640) hm hx
    refine ⟨by simp [blk_length], by simp [blk_length]; omega, fun y hy => ?_⟩
    rcases List.mem_append.1 hy with hy | hy
    · rw [(List.mem_replicate.1 hy).2]; exact hpos
    · exact b3 y hy
  have hE : ∀ k, 1 ≤ (eseq k (x / 640)).length ∧ (eseq k (x / 640)).length ≤ 150 ∧
      ∀ y ∈ eseq k (x / 640), y < 640 * (max (x / 640) G.len + 1) := fun k => by
    have h30 : 30 / k ≤ 30 := Nat.div_le_self _ _
    refine ⟨by rw [eseq, List.length_map, List.length_range]; generalize 30 / k = q at h30 ⊢; omega,
      by rw [eseq, List.length_map, List.length_range]; generalize 30 / k = q at h30 ⊢; omega,
      fun y hy => ?_⟩
    simp only [eseq, List.mem_map, List.mem_range] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    have : 640 * (x / 640 + 1) ≤ 640 * (max (x / 640) G.len + 1) := by omega
    unfold lt; omega
  have hF : ∀ k nx, 1 ≤ k → k ≤ 5 →
      1 ≤ (List.replicate k (blk 2 (G.cl nx))).flatten.length ∧
      (List.replicate k (blk 2 (G.cl nx))).flatten.length ≤ 150 ∧
      ∀ y ∈ (List.replicate k (blk 2 (G.cl nx))).flatten, y < 640 * (max (x / 640) G.len + 1) :=
    fun k nx h1 h5 => by
      obtain ⟨b1, b2, b3⟩ := hb 2 (G.cl nx) (by norm_num) (hcl nx)
      have hlen : (List.replicate k (blk 2 (G.cl nx))).flatten.length = k * 30 := by
        simp [List.length_flatten, blk_length]
      refine ⟨by rw [hlen]; omega, by rw [hlen]; omega, fun y hy => ?_⟩
      obtain ⟨B, hB, hyB⟩ := List.mem_flatten.1 hy
      rw [(List.mem_replicate.1 hB).2] at hyB
      exact b3 y hyB
  unfold tagP
  generalize hI : G.ins (x / 640) = I
  have hIm : ∀ k nx, I = .mul k nx → 1 ≤ k ∧ k ≤ 5 := fun k nx h => G.ins_mul hwf (hI.trans h)
  cases I with
  | mul k nx =>
    obtain ⟨hk1, hk5⟩ := hIm k nx rfl
    split_ifs <;> first
      | with_reducible exact hj | with_reducible exact hH
      | with_reducible exact hb _ _ (by norm_num) (hcl _)
      | with_reducible exact hb _ _ (by norm_num) hx
      | with_reducible exact hM1 _ (by norm_num) | with_reducible exact hE _
      | with_reducible exact hF _ _ hk1 hk5
      | skip
  | div k y n =>
    split_ifs <;> first
      | with_reducible exact hj | with_reducible exact hH
      | with_reducible exact hb _ _ (by norm_num) (hcl _)
      | with_reducible exact hb _ _ (by norm_num) hx
      | with_reducible exact hM1 _ (by norm_num) | with_reducible exact hE _
      | with_reducible exact hF _ _ hk1 hk5
      | skip
  | acc =>
    split_ifs <;> first
      | with_reducible exact hj | with_reducible exact hH
      | with_reducible exact hb _ _ (by norm_num) (hcl _)
      | with_reducible exact hb _ _ (by norm_num) hx
      | with_reducible exact hM1 _ (by norm_num) | with_reducible exact hE _
      | with_reducible exact hF _ _ hk1 hk5
      | skip

theorem mem_junk {y : ℕ} (h : y ∈ junk) : y % 10 = 0 := by
  simp only [junk, blk, List.mem_map, List.mem_range] at h
  obtain ⟨t, ht, rfl⟩ := h
  unfold lt; omega

theorem tagWord_lt (N : ℕ) : ∀ y ∈ tagWord N, y < 640 := by
  intro y hy
  simp only [tagWord, cfg, List.mem_append, List.mem_flatMap] at hy
  rcases hy with ⟨b, -, hb⟩ | hy
  · cases b
    · simpa using mem_blk_lt (kd := 0) (ℓ := 0) (by norm_num) hb
    · simpa using mem_blk_lt (kd := 2) (ℓ := 0) (by norm_num) hb
  · simpa using mem_blk_lt (kd := 6) (ℓ := 0) (by norm_num) hy

/-- The queue at the first reading of `H`: at least two blocks, with no `H` beyond the first. -/
theorem tag_shape (hwf : G.WF) (N0 : ℕ) : ∀ n,
    ((GTag.step 30 G.tagP)^[n] (tagWord N0)).head? = some 1 →
    (∀ m < n, ((GTag.step 30 G.tagP)^[m] (tagWord N0)).head? ≠ some 1) →
    2 * 30 ≤ ((GTag.step 30 G.tagP)^[n] (tagWord N0)).length ∧
      ∀ y ∈ ((GTag.step 30 G.tagP)^[n] (tagWord N0)).drop 30, y ≠ 1 := by
  classical
  intro n hn hmin
  have hA : ∃ i, G.ins (G.gnext^[i] (0, N0)).1 = .acc := by
    by_contra hA
    push_neg at hA
    obtain ⟨T, I, hT, -, -, hs⟩ := G.sim hwf N0 (n + 1) (fun j _ => hA j)
    exact (hs.2 n (by omega)).2 hn
  obtain ⟨T, I, -, hI, -, hseg⟩ := G.sim hwf N0 _ (fun j hj => Nat.find_min hA hj)
  have hs := hseg.trans (G.round_acc (Nat.find_spec hA) hI)
  have hHead : ((GTag.step 30 G.tagP)^[T + (I.length + 1 + I.length)] (tagWord N0)).head? =
      some 1 := by
    rw [hs.1]; simp [hblk]
  have heq : n = T + (I.length + 1 + I.length) := by
    rcases lt_trichotomy n (T + (I.length + 1 + I.length)) with h | h | h
    · exact absurd hn (hs.2 n h).2
    · exact h
    · exact absurd hHead (hmin _ h)
  rw [heq, hs.1]
  have hIl : 1 ≤ I.length := List.length_pos_of_mem hI
  refine ⟨?_, ?_⟩
  · have : (I.flatMap (fun _ => junk)).length = I.length * 30 := by
      simp [List.length_flatMap, junk, blk_length]
    simp only [List.length_append, this, hblk, List.length_cons, List.length_replicate]
    omega
  · rw [List.drop_left' (by simp [hblk])]
    intro y hy h1
    obtain ⟨b, -, hb⟩ := List.mem_flatMap.1 hy
    have := mem_junk hb
    omega

/-- The 30-tag system as a `DTag`. -/
def dtag : DTag := ⟨30, 640 * (G.len + 1), 1, 150, G.tagP⟩

theorem dtag_ok (hwf : G.WF) : G.dtag.Ok where
  two_le_d := by norm_num [dtag]
  H_lt := by show 1 < 640 * (G.len + 1); omega
  P_ne := fun x h => by
    have := (G.tagP_ok hwf x).1
    rw [show G.dtag.P = G.tagP from rfl] at h
    rw [h] at this; simp at this
  P_lt := fun x hx y hy => by
    have hx' : x / 640 ≤ G.len := by
      have : x < 640 * (G.len + 1) := hx
      omega
    have := (G.tagP_ok hwf x).2.2 y hy
    rw [max_eq_right hx'] at this
    exact this
  P_len := fun x => (G.tagP_ok hwf x).2.1

end GProg

/-! ### The constants of the certificate -/

/-- The certificate constants of a binary tag system, with `C = 3^γ`. -/
def tagConst (TS : TagSys) (γ : ℕ) : Tag91 where
  Khalf := 3 ^ (TS.β - 1)
  Uthird := content TS.u / 3
  ε := content TS.u % 3
  B := 3 ^ (TS.u.length - 1)
  C := 3 ^ γ
  jg := (3 ^ γ - 3 ^ (γ - TS.β)) / 2
  cc := (3 ^ (TS.β - 1) - 1) / 2

theorem three_mul_pow_pred {n : ℕ} (h : 1 ≤ n) : 3 * 3 ^ (n - 1) = 3 ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel h]

theorem tagConst_ok (TS : TagSys) {γ : ℕ} (hβ : 2 ≤ TS.β) (ha : 2 ≤ TS.u.length)
    (hγ : 3 * TS.β + TS.u.length + 2 ≤ γ) : (tagConst TS γ).Ok ∧ Matches (tagConst TS γ) TS := by
  have hK : 3 * 3 ^ (TS.β - 1) = 3 ^ TS.β := three_mul_pow_pred (by omega)
  have hB : 3 * 3 ^ (TS.u.length - 1) = 3 ^ TS.u.length := three_mul_pow_pred (by omega)
  have hU : content TS.u < 3 ^ TS.u.length := content_lt _
  have hmono : ∀ a b, a < b → 3 ^ a < 3 ^ b := fun a b h => Nat.pow_lt_pow_right (by norm_num) h
  refine ⟨⟨⟨TS.β, hβ, rfl⟩, ⟨TS.u.length, ha, rfl⟩, ⟨γ, rfl⟩,
    by have := content_mod_three_le_one TS.u; show content TS.u % 3 < 2; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨hK, (Nat.div_add_mod _ _).symm, hB⟩⟩
  · show 2 * ((3 ^ (TS.β - 1) - 1) / 2) + 1 = 3 ^ (TS.β - 1)
    have := pow_three_mod_two (TS.β - 1)
    have : 1 ≤ 3 ^ (TS.β - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  · show 2 * ((3 ^ γ - 3 ^ (γ - TS.β)) / 2) + 3 ^ γ / (3 * 3 ^ (TS.β - 1)) = 3 ^ γ
    rw [hK, Nat.pow_div (by omega) (by norm_num)]
    have h1 := pow_three_mod_two γ
    have h2 := pow_three_mod_two (γ - TS.β)
    have h3 : 3 ^ (γ - TS.β) ≤ 3 ^ γ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · show 3 * 3 ^ (TS.β - 1) ∣ 3 ^ γ
    rw [hK]; exact Nat.pow_dvd_pow _ (by omega)
  · show (3 * 3 ^ (TS.β - 1)) ^ 3 < 3 ^ γ
    rw [hK, ← pow_mul]; exact hmono _ _ (by omega)
  · show 3 * (3 * 3 ^ (TS.β - 1)) * (3 * 3 ^ (TS.u.length - 1)) < 3 ^ γ
    rw [hK, hB, ← pow_succ', ← pow_add]; exact hmono _ _ (by omega)
  · show 2 * (3 * 3 ^ (TS.β - 1)) * (3 * (content TS.u / 3) + content TS.u % 3) + 3 < 3 ^ γ
    rw [hK, Nat.div_add_mod]
    have h1 : 3 ^ (TS.β + TS.u.length + 1) ≤ 3 ^ γ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ (TS.β + TS.u.length + 1) = 3 * (3 ^ TS.β * 3 ^ TS.u.length) := by ring
    have h9 : 9 ≤ 3 ^ TS.β := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ TS.β := Nat.pow_le_pow_right (by norm_num) hβ
    have h4 : 3 ^ TS.β * (content TS.u + 1) ≤ 3 ^ TS.β * 3 ^ TS.u.length :=
      Nat.mul_le_mul_left _ hU
    nlinarith

/-! ### Universality -/

namespace CProgram

variable (M : CProgram)

/-- The binary tag system of a three-counter program. -/
def binTS : TagSys := (M.compile).dtag.TS

/-- The encoded binary word of an input. -/
def binWord (x : ℕ) : List Bool := (M.compile).dtag.W0 (GProg.tagWord (2 ^ x))

/-- The exponent of `C` for an input. -/
def binγ (x : ℕ) : ℕ := (M.binWord x).length + 3 * M.binTS.β + M.binTS.u.length + 2

theorem accepts_iff_halts (x : ℕ) :
    (M.Accepts x ↔ M.binTS.Halts (M.binWord x)) ∧ TagPromise M.binTS (M.binWord x) ∧
      M.binTS.β ≤ (M.binWord x).length ∧ 2 ≤ M.binTS.β ∧ 2 ≤ M.binTS.u.length := by
  have hwf := M.compile_wf
  have hD := (M.compile).dtag_ok hwf
  have hL := (M.compile).tag_iff hwf (2 ^ x)
  obtain ⟨h1, h2, h3, h4, h5⟩ := (M.compile).dtag.bin_iff hD (GProg.tagWord (2 ^ x))
    (fun y hy => by
      have := GProg.tagWord_lt (2 ^ x) y hy
      show y < 640 * ((M.compile).len + 1); omega)
    hL.1 ((M.compile).tag_shape hwf (2 ^ x))
  refine ⟨?_, h2, h3, h4, h5⟩
  rw [M.accepts_iff_reachesAcc, ← hL.2]
  exact h1.symm

/-- **The 91-operation tag certificate is universal**: for every recursively enumerable set `S`
there are a fixed binary tag system, with fixed constants `k`, `Ut`, `ε`, `B`, `cc`, and an
encoding of inputs by the words `W_x` and the powers `C_x = 3^γ_x` above the admitted bound,
such that `x ∈ S` exactly when the 18 equations are solvable at `(content W_x, 3^|W_x|)`. -/
theorem _root_.Jones1980.tag91_re {S : Set ℕ} (hS : REPred S) :
    ∃ M : CProgram, ∀ x, (tagConst M.binTS (M.binγ x)).Ok ∧
      Matches (tagConst M.binTS (M.binγ x)) M.binTS ∧
      (x ∈ S ↔ Solvable91 (tagConst M.binTS (M.binγ x)) (content (M.binWord x))
        (3 ^ (M.binWord x).length)) := by
  obtain ⟨Γ, Λ, iΓ, fΓ, iΛ, fΛ, TM, enc, pre, hM⟩ := TMUniv.re_tm0 hS
  let P := TMCounter.prog TM enc pre
  refine ⟨P, fun x => ?_⟩
  obtain ⟨hiff, hP, hβW, hβ, ha⟩ := P.accepts_iff_halts x
  obtain ⟨hOk, hMatch⟩ := tagConst_ok P.binTS (γ := P.binγ x) hβ ha (by unfold binγ; omega)
  refine ⟨hOk, hMatch, ?_⟩
  rw [hM x, ← TMCounter.accepts_iff TM enc pre x, hiff]
  exact (tag_iff91 hOk hMatch rfl hβ ha hβW (by unfold binγ; omega) hP).symm

end CProgram

end Jones1980
