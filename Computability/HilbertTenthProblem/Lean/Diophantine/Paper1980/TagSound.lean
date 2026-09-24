import Diophantine.Paper1980.TagSystem
import Diophantine.Paper1980.TagPath
import Diophantine.Paper1980.TagContent

/-!
# Soundness of the decoded tag history: actual eventual halting

`EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md`, §§4–5, and `EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md`,
§4.  Given the decoded row data of a solution (`Ctx`): the Boolean marker words `M₀, M₁`,
the head selectors `S₁`, the prefix word `E`, the guarded content `GN`, the projector rows
of `M₁`, the length equation and the content transport — the actual tag computation from
the initial word `W₀` halts.

The proof identifies the rows with the actual computation inductively (`Inv`): row `i`
carries the single marker at the offset `|Wᵢ|`, and the content transport reads
`Einv … (content Wᵢ) i t`.  At each row the guard chunk gives a Boolean discrepancy `s`,
the prefix identity `dᵢ = pᵢ + s` shows that the encoded selector dominates the actual
first symbol, so the encoded successor length dominates the actual one; a short encoded
successor (or the endpoint) therefore halts the actual machine, and otherwise the next
guard forces `s = 0`, identifying the row exactly and moving the invariant on.
-/

namespace Jones1980

open Ternary TagSys

/-! ### Facts about contents -/

theorem content_bool3 : ∀ W : List Bool, Bool3 (content W)
  | [] => by rw [content_nil]; exact bool3_zero
  | b :: W => by
    intro p
    rw [content_cons]
    have ih := content_bool3 W
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0
      rw [dg_zero_pos, Nat.add_mul_mod_self_left]
      have := bit_le_one b
      rw [Nat.mod_eq_of_lt (by omega)]; exact this
    · obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      have e : dg (bit b + 3 * content W) (p + 1) = dg (content W) p := by
        unfold dg
        rw [pow_succ, mul_comm (3 ^ p) 3, ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ (by norm_num),
          Nat.div_eq_of_lt (show bit b < 3 by have := bit_le_one b; omega), zero_add]
      rw [e]; exact ih p

theorem content_cons_mod (b : Bool) (W : List Bool) : content (b :: W) % 3 = bit b := by
  rw [content_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by have := bit_le_one b; omega)]

/-- `3E + s` with `E` Boolean and `s ≤ 1` is Boolean. -/
theorem bool3_three_mul_add {E s : ℕ} (hE : Bool3 E) (hs : s ≤ 1) : Bool3 (3 * E + s) := by
  intro p
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    rw [dg_zero_pos, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]; exact hs
  · obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have e : dg (3 * E + s) (p + 1) = dg E p := by
      unfold dg
      rw [pow_succ, mul_comm (3 ^ p) 3, ← Nat.div_div_eq_div_mul, add_comm,
        Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (show s < 3 by omega), zero_add]
    rw [e]; exact hE p

theorem three_mul_add_mod (E s : ℕ) (hs : s ≤ 1) : (3 * E + s) % 3 = s := by
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-! ### The decoded context -/

/-- The decoded row data of a solution of the tag certificate, for a tag system `TS`. -/
structure Ctx (TS : TagSys) (W₀ : List Bool) (m t M0 M1 S1 E GN : ℕ) : Prop where
  hm : 1 ≤ m
  ht : 1 ≤ t
  hβ : 2 ≤ TS.β
  ha : 2 ≤ TS.u.length
  hβm : 3 * TS.β < m
  hℓ₀ : TS.β ≤ W₀.length
  hℓ₀m : W₀.length + 2 * TS.β < m
  hM0 : Bool3 M0
  hM1 : Bool3 M1
  hM0lt : M0 < 3 ^ (m * t)
  hM1lt : M1 < 3 ^ (m * t)
  hS1 : Bool3 S1
  hS1lt : S1 < 3 ^ (m * t)
  hS1H : ∀ p, dg S1 p = 1 → p % m = 0 ∧ p < m * t
  hE : Bool3 E
  hElt : E < 3 ^ (m * t)
  hEsupp : ∀ p, dg E p = 1 → p % m < TS.β - 1 ∧ p < m * t
  hGN : Bool3 GN
  hGNlt : GN < 3 ^ (m * t)
  /-- The projector rows of `M₁`. -/
  hM1row : ∀ i, i < t → ∃ ℓ, row M1 m i = if dg S1 (m * i) = 1 then 3 ^ ℓ else 0
  /-- The `M₁`-markers are at most `A`, and `a + β < γ`. -/
  hM1α : ∀ p, dg M1 p = 1 → p % m + TS.u.length + TS.β < m
  /-- The length equation in row form. -/
  heq : M0 + M1 + 3 ^ (m * t + 1) =
    3 ^ W₀.length + 3 ^ (m - (TS.β - 1)) * M0 + 3 ^ (m - (TS.β - 1) + (TS.u.length - 1)) * M1
  /-- The content transport `R (N − (3E + S₁) + U M₁) = K (N − Ninit)`, with the signed content
  `N = GN − rep β · 3^(m−β) · H`. -/
  htrans : ((3 ^ m : ℕ) : ℤ) * (((GN : ℤ) - rep TS.β * 3 ^ (m - TS.β) * heads m t) -
      (3 * E + S1) + content TS.u * M1) =
    (3 ^ TS.β : ℕ) * (((GN : ℤ) - rep TS.β * 3 ^ (m - TS.β) * heads m t) - content W₀)

/-- The signed content row `nᵢ = gᵢ − hK·b`. -/
def nrow (β m GN i : ℕ) : ℤ := (row GN m i : ℤ) - rep β * 3 ^ (m - β)

/-- The transport row `xᵢ = nᵢ − dᵢ + U·M₁ᵢ`. -/
def xrow (β m E S1 M1 GN U i : ℕ) : ℤ :=
  nrow β m GN i - (3 * (row E m i : ℤ) + dg S1 (m * i)) + U * row M1 m i

/-- The actual run of the tag system. -/
def run (TS : TagSys) (W₀ : List Bool) (i : ℕ) : List Bool := TS.step^[i] W₀

theorem run_zero (TS : TagSys) (W₀ : List Bool) : run TS W₀ 0 = W₀ := rfl

theorem run_succ (TS : TagSys) (W₀ : List Bool) (i : ℕ) :
    run TS W₀ (i + 1) = TS.step (run TS W₀ i) := Function.iterate_succ_apply' _ _ _

theorem row_S1_eq {S1 m t i : ℕ} (hS1 : Bool3 S1) (hS1H : ∀ p, dg S1 p = 1 → p % m = 0 ∧ p < m * t)
    (hm : 1 ≤ m) : row S1 m i = dg S1 (m * i) := by
  apply row_eq_of_dg
  · have := hS1 (m * i)
    calc dg S1 (m * i) ≤ 1 := this
      _ < 3 ^ m := by
        calc 1 < 3 ^ 1 := by norm_num
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [add_zero, dg_zero_pos, Nat.mod_eq_of_lt (by have := hS1 (m * i); omega)]
    · have : dg S1 (m * i + k) = 0 := dg_S_eq_zero_of_offset hS1 hS1H h0 hk
      rw [this, dg_eq_zero_of_lt]
      calc dg S1 (m * i) ≤ 1 := hS1 (m * i)
        _ < 3 ^ k := by
          calc 1 < 3 ^ 1 := by norm_num
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h0

section Sound

variable {TS : TagSys} {W₀ : List Bool} {m t M0 M1 S1 E GN : ℕ}
  (C : Ctx TS W₀ m t M0 M1 S1 E GN)

include C

/-- The content transport in the row form of `Einv_zero`. -/
theorem transport_rows :
    ((3 ^ m : ℕ) : ℤ) *
        ∑ i ∈ Finset.range t, xrow TS.β m E S1 M1 GN (content TS.u) i * ((3 ^ m : ℕ) : ℤ) ^ i =
      (3 ^ TS.β : ℕ) * ∑ i ∈ Finset.range t, nrow TS.β m GN i * ((3 ^ m : ℕ) : ℤ) ^ i -
        (3 ^ TS.β : ℕ) * content W₀ := by
  have hGN := sum_rows t C.hGNlt
  have hE := sum_rows t C.hElt
  have hS1 := sum_rows t C.hS1lt
  have hM1 := sum_rows t C.hM1lt
  have hH : heads m t = ∑ i ∈ Finset.range t, 3 ^ (m * i) := rfl
  have hN : ((GN : ℤ) - rep TS.β * 3 ^ (m - TS.β) * heads m t) =
      ∑ i ∈ Finset.range t, nrow TS.β m GN i * ((3 ^ m : ℕ) : ℤ) ^ i := by
    unfold nrow
    conv_lhs => rw [hGN, hH]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd : ((3 * E + S1 : ℕ) : ℤ) = ∑ i ∈ Finset.range t,
      (3 * (row E m i : ℤ) + dg S1 (m * i)) * ((3 ^ m : ℕ) : ℤ) ^ i := by
    conv_lhs => rw [hE, hS1]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [row_S1_eq C.hS1 C.hS1H C.hm]
    ring
  have hM1' : ((M1 : ℕ) : ℤ) = ∑ i ∈ Finset.range t, (row M1 m i : ℤ) * ((3 ^ m : ℕ) : ℤ) ^ i := by
    conv_lhs => rw [hM1]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htrans := C.htrans
  rw [hN] at htrans
  have hx : ∑ i ∈ Finset.range t, xrow TS.β m E S1 M1 GN (content TS.u) i * ((3 ^ m : ℕ) : ℤ) ^ i =
      ∑ i ∈ Finset.range t, nrow TS.β m GN i * ((3 ^ m : ℕ) : ℤ) ^ i - (3 * E + S1 : ℕ) +
        content TS.u * M1 := by
    rw [hd, hM1', Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold xrow
    ring
  rw [hx]
  push_cast at htrans ⊢
  linear_combination htrans

omit C in
/-- `rep (b + 1) = 3 rep b + 1`. -/
theorem rep_succ_three (b : ℕ) : rep (b + 1) = 3 * rep b + 1 := by
  have h1 := two_mul_rep_add_one (b + 1)
  have h2 := two_mul_rep_add_one b
  rw [pow_succ] at h1
  omega

omit C in
/-- A Boolean row supported below the offset `b` is below `3^b`. -/
theorem row_lt_of_support {X m i b : ℕ} (hX : Bool3 X) (hb : b ≤ m)
    (h : ∀ k, b ≤ k → k < m → dg X (m * i + k) = 0) : row X m i < 3 ^ b := by
  have hrb : Bool3 (row X m i) := hX.row m i
  have hz : ∀ k, b ≤ k → dg (row X m i) k = 0 := by
    intro k hk
    rcases Nat.lt_or_ge k m with hkm | hkm
    · rw [dg_row _ _ hkm]; exact h k hk hkm
    · exact dg_row_of_ge _ _ hkm
  have hlt : row X m i < 3 ^ m := row_lt _ _ _
  rw [← val_dg hlt]
  have : val (dg (row X m i)) m = val (dg (row X m i)) b := by
    unfold val
    rw [← Finset.sum_range_add_sum_Ico _ hb]
    rw [Finset.sum_eq_zero (s := Finset.Ico b m) (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hz k hk.1]; ring)]
    ring
  rw [this]
  exact val_lt (fun p => by have := hrb p; omega) _

/-- The invariant at row `i`: the actual queue has the length of the row marker, and the
content transport has been identified below `i`. -/
structure Inv (TS : TagSys) (W₀ : List Bool) (m t M0 M1 S1 E GN i ℓ : ℕ) : Prop where
  hit : i < t
  hlen : (run TS W₀ i).length = ℓ
  hℓ : TS.β ≤ ℓ
  hℓm : ℓ + 2 * TS.β < m
  hrow : ∀ k, k < m → coef M0 M1 (m * i + k) = if k = ℓ then 1 else 0
  hE : Einv (nrow TS.β m GN) (xrow TS.β m E S1 M1 GN (content TS.u)) (3 ^ TS.β : ℕ) (3 ^ m : ℕ)
    (content (run TS W₀ i)) i t

theorem inv_zero : Inv TS W₀ m t M0 M1 S1 E GN 0 W₀.length :=
  { hit := C.ht
    hlen := rfl
    hℓ := C.hℓ₀
    hℓm := C.hℓ₀m
    hrow := fun k hk => by
      have := row_zero_marker C.hm C.ht C.hβ C.ha C.hβm C.hM0 C.hM1 C.hM0lt C.hM1lt C.hℓ₀ C.hℓ₀m
        C.hM1α C.heq k hk
      rwa [mul_zero, zero_add]
    hE := Einv_zero (transport_rows C) }

/-- The row digits of `M₁`, from the projector. -/
theorem dg_M1_row {i : ℕ} (hi : i < t) :
    ∃ ℓ'', ℓ'' < m ∧ ∀ k, k < m →
      dg M1 (m * i + k) = if dg S1 (m * i) = 1 ∧ k = ℓ'' then 1 else 0 := by
  obtain ⟨ℓ'', hr⟩ := C.hM1row i hi
  by_cases hs : dg S1 (m * i) = 1
  · rw [if_pos hs] at hr
    have hlt : 3 ^ ℓ'' < 3 ^ m := by rw [← hr]; exact row_lt M1 m i
    refine ⟨ℓ'', (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt, fun k hk => ?_⟩
    rw [← dg_row _ _ hk, hr, dg_pow]
    by_cases hkℓ : k = ℓ'' <;> simp [hs, hkℓ]
  · rw [if_neg hs] at hr
    refine ⟨0, C.hm, fun k hk => ?_⟩
    rw [← dg_row _ _ hk, hr, dg_zero, if_neg (fun h => hs h.1)]

/-- The soundness induction: from the invariant at any row, the actual machine halts. -/
theorem inv_halts : ∀ j i ℓ, i + j = t → Inv TS W₀ m t M0 M1 S1 E GN i ℓ → TS.Halts W₀ := by
  intro j
  induction j with
  | zero =>
    intro i ℓ hij hI
    exfalso
    have := hI.hit
    omega
  | succ j ih =>
    intro i ℓ hij hI
    obtain ⟨hit, hlen, hℓ, hℓm, hrow, hE⟩ := hI
    have hβ2 := C.hβ; have ha2 := C.ha; have hm := C.hm; have hβm := C.hβm
    set W := run TS W₀ i with hWdef
    -- the queue is not short: it is `w :: W'`
    obtain ⟨w, W', hW⟩ : ∃ w W', W = w :: W' := by
      cases hW' : W with
      | nil => rw [hW'] at hlen; simp at hlen; omega
      | cons w W' => exact ⟨w, W', rfl⟩
    have hlen' : (w :: W').length = ℓ := by rw [← hW]; exact hlen
    have hWlong : TS.β ≤ (w :: W').length := by rw [hlen']; exact hℓ
    have hstep_len := length_step TS hWlong
    have hstep_content := content_step TS hWlong
    have hv_lt : content W < 3 ^ ℓ := by rw [← hlen]; exact content_lt W
    have hv_bool : Bool3 (content W) := content_bool3 W
    have hσ : content W % 3 = bit w := by rw [hW]; exact content_cons_mod w W'
    -- row `i` of `M₁`
    obtain ⟨ℓ'', hℓ''m, hM1dg⟩ := dg_M1_row C hit
    set s := dg S1 (m * i) with hsdef
    have hs1 : s ≤ 1 := C.hS1 _
    have hsℓ : s = 1 → ℓ'' = ℓ := by
      intro h1
      have h2 := hrow ℓ'' hℓ''m
      unfold coef at h2
      rw [hM1dg ℓ'' hℓ''m, if_pos ⟨h1, rfl⟩] at h2
      by_contra hne
      rw [if_neg hne] at h2; omega
    have hsM1 : dg M1 (m * i + ℓ) = s := by
      rw [hM1dg ℓ (by omega)]
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · rw [if_neg (fun h => by omega)]; exact h0.symm
      · have h1 : s = 1 := by omega
        rw [if_pos ⟨h1, (hsℓ h1).symm⟩]; exact h1.symm
    have hM1row : row M1 m i = if s = 1 then 3 ^ ℓ else 0 := by
      apply row_eq_of_dg
      · split_ifs
        · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        · positivity
      · intro k hk
        rw [hM1dg k hk]
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · rw [if_neg (fun h => by omega), if_neg (by omega), dg_zero]
        · have h1 : s = 1 := by omega
          rw [if_pos h1, dg_pow, hsℓ h1]
          by_cases hkℓ : k = ℓ <;> simp [h1, hkℓ]
    -- the successor via the length path
    set ℓ' := ℓ - TS.β + (if s = 1 then TS.u.length else 1) with hℓ'def
    obtain ⟨hℓ'm, -, hnext, hend⟩ := row_step C.hm C.ht C.hβ C.ha C.hβm C.hM0 C.hM1 C.hM0lt
      C.hM1lt C.hℓ₀ C.hℓ₀m C.hM1α C.heq (by omega) hℓ hℓm hrow hsM1.symm rfl
    -- the guard chunk
    have hR0 : ((3 ^ m : ℕ) : ℤ) ≠ 0 := by positivity
    have hRKb : ((3 ^ m : ℕ) : ℤ) = (3 ^ TS.β : ℕ) * (3 ^ (m - TS.β) : ℕ) := by
      push_cast; rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    have hK0 : ((3 ^ TS.β : ℕ) : ℤ) ≠ 0 := by positivity
    have hdvdR := Einv_dvd hit hE hR0
    have hdvdb : ((3 ^ (m - TS.β) : ℕ) : ℤ) ∣ nrow TS.β m GN i - content W := by
      rw [hRKb] at hdvdR
      exact (mul_dvd_mul_iff_left hK0).1 hdvdR
    have hvz : content W < 3 ^ (m - 2 * TS.β) :=
      lt_of_lt_of_le hv_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨s', hs'K, hs'b, hn⟩ := guard_chunk (by omega : 1 ≤ TS.β) (by omega : 2 * TS.β < m)
      (C.hGN.row m i) (row_lt GN m i) hvz hdvdb
    have hn' : nrow TS.β m GN i = content W - s' * 3 ^ (m - TS.β) := hn
    have hc : ((3 ^ TS.β : ℕ) : ℤ) * (nrow TS.β m GN i - content W) =
        ((3 ^ m : ℕ) : ℤ) * (-(s' : ℤ)) := by
      rw [hn', hRKb]
      push_cast
      ring
    -- `K ∣ xᵢ + s'`
    have hKR : ((3 ^ TS.β : ℕ) : ℤ) ∣ ((3 ^ m : ℕ) : ℤ) := by rw [hRKb]; exact dvd_mul_right _ _
    have hxs : ((3 ^ TS.β : ℕ) : ℤ) ∣ xrow TS.β m E S1 M1 GN (content TS.u) i + s' := by
      rcases Nat.lt_or_ge (i + 1) t with hit' | hit'
      · have h := Einv_next hit' hE hR0 hc
        have h1 := dvd_trans hKR h
        have h2 : ((3 ^ TS.β : ℕ) : ℤ) ∣ (3 ^ TS.β : ℕ) * nrow TS.β m GN (i + 1) := dvd_mul_right _ _
        have h3 := dvd_sub h2 h1
        have e : (3 ^ TS.β : ℕ) * nrow TS.β m GN (i + 1) -
            ((3 ^ TS.β : ℕ) * nrow TS.β m GN (i + 1) - (xrow TS.β m E S1 M1 GN (content TS.u) i - -(s' : ℤ))) =
            xrow TS.β m E S1 M1 GN (content TS.u) i + s' := by ring
        rw [e] at h3; exact h3
      · have hit'' : i + 1 = t := by omega
        have h := Einv_last hit'' hE hR0 hc
        rw [show xrow TS.β m E S1 M1 GN (content TS.u) i + s' = 0 by linarith]
        exact dvd_zero _
    -- the prefix identity `dᵢ = pᵢ + s'`
    obtain ⟨d, hddef⟩ : ∃ d, d = 3 * row E m i + s := ⟨_, rfl⟩
    obtain ⟨p, hpdef⟩ : ∃ p, p = content W % 3 ^ TS.β := ⟨_, rfl⟩
    have hple : p ≤ content W := by rw [hpdef]; exact Nat.mod_le _ _
    have hEi : row E m i < 3 ^ (TS.β - 1) := by
      refine row_lt_of_support C.hE (by omega) ?_
      intro k hk hkm
      by_contra h
      have h1 : dg E (m * i + k) = 1 := by have := C.hE (m * i + k); omega
      have := (C.hEsupp _ h1).1
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hkm] at this
      omega
    have hd_le : d ≤ rep TS.β := by
      have h1 : row E m i ≤ rep (TS.β - 1) := (C.hE.row m i).le_rep hEi
      have h2 : rep TS.β = 3 * rep (TS.β - 1) + 1 := by
        have := rep_succ_three (TS.β - 1)
        rwa [Nat.sub_add_cancel (by omega)] at this
      rw [hddef]; omega
    have hp_le : p ≤ rep TS.β := by
      rw [hpdef]; exact (hv_bool.mod_pow TS.β).le_rep (Nat.mod_lt _ (by positivity))
    have hM1K : 3 ^ TS.β ∣ row M1 m i := by
      rw [hM1row]
      split_ifs
      · exact Nat.pow_dvd_pow 3 hℓ
      · exact dvd_zero _
    have hvp : 3 ^ TS.β ∣ content W - p := by rw [hpdef]; exact Nat.dvd_sub_mod _
    have hbK : ((3 ^ TS.β : ℕ) : ℤ) ∣ ((3 ^ (m - TS.β) : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_dvd_pow 3 (by omega : TS.β ≤ m - TS.β)
    have hdps : d = p + s' := by
      apply prefix_eq (by omega : 1 ≤ TS.β) hd_le hp_le hs'K
      have e : (d : ℤ) - (p + s') = ((content W - p : ℕ) : ℤ) - s' * (3 ^ (m - TS.β) : ℕ) +
          content TS.u * row M1 m i - (xrow TS.β m E S1 M1 GN (content TS.u) i + s') := by
        unfold xrow
        rw [hn', ← hsdef, hddef, Nat.cast_sub hple]
        push_cast
        ring
      rw [e]
      have h1 : ((3 ^ TS.β : ℕ) : ℤ) ∣ ((content W - p : ℕ) : ℤ) := by exact_mod_cast hvp
      have h2 : ((3 ^ TS.β : ℕ) : ℤ) ∣ (s' : ℤ) * (3 ^ (m - TS.β) : ℕ) := Dvd.dvd.mul_left hbK _
      have h3 : ((3 ^ TS.β : ℕ) : ℤ) ∣ (content TS.u : ℤ) * row M1 m i := by
        have : ((3 ^ TS.β : ℕ) : ℤ) ∣ ((row M1 m i : ℕ) : ℤ) := by exact_mod_cast hM1K
        exact Dvd.dvd.mul_left this _
      exact dvd_sub (dvd_add (dvd_sub h1 h2) h3) hxs
    -- the encoded selector dominates the actual first symbol
    have hd0 : d % 3 = s := by rw [hddef]; exact three_mul_add_mod _ _ hs1
    have hp0 : p % 3 = bit w := by
      rw [hpdef, Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega)), hσ]
    have hσs : bit w ≤ s := by
      have hdb : Bool3 d := by rw [hddef]; exact bool3_three_mul_add (C.hE.row m i) hs1
      have hpb : Bool3 p := by rw [hpdef]; exact hv_bool.mod_pow TS.β
      have hdb' : Bool3 (p + s') := by rw [← hdps]; exact hdb
      have hdisj := bool3_add_disjoint hpb hs'b hdb'
      have hdg : dg (p + s') 0 = dg p 0 + dg s' 0 :=
        dg_add_of_le_two (fun q => by have := hdisj q; omega) 0
      have h1 : dg d 0 = s := by rw [dg_zero_pos]; exact hd0
      have h2 : dg p 0 = bit w := by rw [dg_zero_pos]; exact hp0
      rw [← hdps, h1, h2] at hdg
      omega
    -- the actual successor length is dominated by the encoded one
    have hlam : (TS.step (w :: W')).length = ℓ - TS.β + (if w then TS.u.length else 1) := by
      rw [hlen'] at hstep_len; omega
    have hlamle : (TS.step (w :: W')).length ≤ ℓ' := by
      rw [hlam, hℓ'def]
      cases w
      · simp only [Bool.false_eq_true, if_false]
        split_ifs <;> omega
      · have hs1' : s = 1 := by simp [bit] at hσs; omega
        simp [hs1']
    have hhalt_of_short : ℓ' < TS.β → TS.Halts W₀ := fun hsh => ⟨i + 1, by
      show (run TS W₀ (i + 1)).length < TS.β
      rw [run_succ, ← hWdef, hW]; omega⟩
    rcases Nat.lt_or_ge (i + 1) t with hit' | hit'
    swap
    · exact hhalt_of_short (by have := hend (by omega); omega)
    by_cases hshortℓ : ℓ' < TS.β
    · exact hhalt_of_short hshortℓ
    push Not at hshortℓ
    -- no discrepancy: `s' = 0`
    have hs'0 : s' = 0 := by
      by_contra hne
      have hs'1 : 1 ≤ s' := by omega
      have hKdvd : 3 ^ TS.β ∣ content W - p + content TS.u * row M1 m i :=
        dvd_add hvp (Dvd.dvd.mul_left hM1K _)
      obtain ⟨vstar, hvstar⟩ := hKdvd
      have hxeq : xrow TS.β m E S1 M1 GN (content TS.u) i + s' =
          ((3 ^ TS.β : ℕ) : ℤ) * vstar - (s' : ℤ) * ((3 ^ (m - TS.β) : ℕ) : ℤ) := by
        unfold xrow
        rw [hn', ← hsdef]
        have hdZ : (3 * (row E m i : ℤ) + (s : ℤ)) = (p : ℤ) + s' := by
          have : ((3 * row E m i + s : ℕ) : ℤ) = ((p + s' : ℕ) : ℤ) := by rw [← hddef, hdps]
          push_cast at this; exact this
        have hv : ((content W - p + content TS.u * row M1 m i : ℕ) : ℤ) =
            ((3 ^ TS.β : ℕ) : ℤ) * vstar := by
          exact_mod_cast hvstar
        push_cast [Nat.cast_sub hple] at hv ⊢
        linear_combination hv - hdZ
      have hnext' := Einv_next hit' hE hR0 hc
      have hnext'' : ((3 ^ m : ℕ) : ℤ) ∣ (3 ^ TS.β : ℕ) * nrow TS.β m GN (i + 1) -
          ((3 ^ TS.β : ℕ) * vstar - s' * (3 ^ (m - TS.β) : ℕ)) := by
        rw [← hxeq]
        have e : (3 ^ TS.β : ℕ) * nrow TS.β m GN (i + 1) - (xrow TS.β m E S1 M1 GN (content TS.u) i + s') =
            (3 ^ TS.β : ℕ) * nrow TS.β m GN (i + 1) - (xrow TS.β m E S1 M1 GN (content TS.u) i - -(s' : ℤ)) := by ring
        rw [e]; exact hnext'
      have hb2 := mod_of_transport (by omega : 1 ≤ TS.β) (by omega : 2 * TS.β < m) hnext''
      have hvz' : vstar < 3 ^ (m - 2 * TS.β) := by
        have hUlt : content TS.u < 3 ^ TS.u.length := content_lt TS.u
        have h1 : 3 ^ TS.β * vstar < 3 ^ TS.β * 3 ^ (m - 2 * TS.β) := by
          rw [← hvstar]
          rcases Nat.eq_zero_or_pos s with h0 | h0
          · rw [hM1row, if_neg (by omega), mul_zero, add_zero]
            calc content W - p ≤ content W := Nat.sub_le _ _
              _ < 3 ^ (m - 2 * TS.β) := hvz
              _ ≤ 3 ^ TS.β * 3 ^ (m - 2 * TS.β) := Nat.le_mul_of_pos_left _ (by positivity)
          · have h1 : s = 1 := by omega
            rw [hM1row, if_pos h1]
            have hα := C.hM1α (m * i + ℓ) (by rw [hsM1]; exact h1)
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)] at hα
            have h2 : content W - p + content TS.u * 3 ^ ℓ < 3 ^ (ℓ + TS.u.length) := by
              have h3 : content TS.u * 3 ^ ℓ ≤ (3 ^ TS.u.length - 1) * 3 ^ ℓ := Nat.mul_le_mul_right _ (by omega)
              have h4 : (3 ^ TS.u.length - 1) * 3 ^ ℓ + 3 ^ ℓ = 3 ^ (ℓ + TS.u.length) := by
                have h5 : 1 ≤ 3 ^ TS.u.length := Nat.one_le_pow _ _ (by norm_num)
                rw [pow_add, Nat.sub_mul, one_mul]
                have h6 : 3 ^ ℓ ≤ 3 ^ TS.u.length * 3 ^ ℓ := Nat.le_mul_of_pos_left _ (by positivity)
                rw [mul_comm (3 ^ TS.u.length) (3 ^ ℓ)]
                have h7 : 3 ^ ℓ ≤ 3 ^ ℓ * 3 ^ TS.u.length := Nat.le_mul_of_pos_right _ (by positivity)
                omega
              have h8 : content W - p ≤ content W := Nat.sub_le _ _
              omega
            calc content W - p + content TS.u * 3 ^ ℓ < 3 ^ (ℓ + TS.u.length) := h2
              _ ≤ 3 ^ (m - TS.β) := Nat.pow_le_pow_right (by norm_num) (by omega)
              _ = 3 ^ TS.β * 3 ^ (m - 2 * TS.β) := by rw [← pow_add]; congr 1; omega
        exact Nat.lt_of_mul_lt_mul_left h1
      unfold nrow at hb2
      exact next_guard_contra (by omega : 1 ≤ TS.β) (by omega : 2 * TS.β < m) (C.hGN.row m (i + 1))
        (row_lt GN m (i + 1)) hvz' hs'1 hs'K hb2
    -- identification of row `i`
    subst hs'0
    simp only [Nat.cast_zero, zero_mul, sub_zero, add_zero] at hn' hdps
    have hs_eq : s = bit w := by rw [← hd0, hdps, hp0]
    have hℓ'eq : (TS.step (w :: W')).length = ℓ' := by
      rw [hlam, hℓ'def, hs_eq]
      cases w <;> simp [bit]
    have hx_eq : xrow TS.β m E S1 M1 GN (content TS.u) i = (3 ^ TS.β : ℕ) * content (TS.step (w :: W')) := by
      unfold xrow
      rw [hn', ← hsdef, hM1row, hs_eq]
      have hcast : ((3 ^ TS.β * content (TS.step (w :: W')) : ℕ) : ℤ) =
          ((content (w :: W') - content (w :: W') % 3 ^ TS.β +
            3 ^ (w :: W').length * (if w then content TS.u else 0) : ℕ) : ℤ) := by
        rw [hstep_content]
      rw [hlen'] at hcast
      have hdZ : (3 * (row E m i : ℤ) + (bit w : ℤ)) = (p : ℤ) := by
        have : ((3 * row E m i + bit w : ℕ) : ℤ) = (p : ℤ) := by
          rw [← hs_eq, ← hddef]; exact_mod_cast hdps
        push_cast at this; exact this
      have hple' : content (w :: W') % 3 ^ TS.β ≤ content (w :: W') := Nat.mod_le _ _
      push_cast [Nat.cast_sub hple'] at hcast ⊢
      rw [hdZ, hpdef, hW]
      cases w
      · simp [bit] at hcast ⊢
        linarith
      · simp [bit] at hcast ⊢
        linarith
    have hE' := Einv_step hit hE hn' hx_eq
    have hI' : Inv TS W₀ m t M0 M1 S1 E GN (i + 1) ℓ' :=
      ⟨hit', by rw [run_succ, ← hWdef, hW]; exact hℓ'eq, hshortℓ, hℓ'm, hnext hit' hshortℓ,
        by rw [run_succ, ← hWdef, hW]; exact hE'⟩
    exact ih (i + 1) ℓ' (by omega) hI'

/-- **Soundness**: the decoded history halts the actual tag machine. -/
theorem halts_of_ctx : TS.Halts W₀ := inv_halts C t 0 W₀.length (by omega) (inv_zero C)

end Sound

end Jones1980
