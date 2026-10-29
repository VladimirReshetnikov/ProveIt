import DiophantineConsistency.ArithmeticControllerData
import BusyBeaver.ZFC.ArithmeticCantor

/-! **K5c — the dummy-bit controller choice** (construction spec §7 K3, with
simplification S7), in every model of IΣ1.

At level `P = p^m` (`p = 120199`, `N = p^(m+1)`, `M = d·N`, `C0 = d·p`,
`d = 94517`, `B = 2^d`) a dummy set is chosen as the positions
`pos e = 2 + 120198·e` (`e < P`) whose discrete-log coordinate `zc P e`
lies in `Z = {o, …, o+k-2} ∪ {last}`. Since `B^(pos e) = B²·g^e` and
`g^e ≡ 1 + C0·zc(e) (mod M)`, the block sum is `B²(k + C0·ΣZ) (mod M)`.
The count `k ∈ [1, C0]` is forced modulo `C0`; the progression and the last
coordinate are arranged so that `ΣZ` hits the required residue modulo `P`,
and the offset `o ∈ {0,1}` keeps `last` outside the progression (this needs
only `2·C0 < P`, no inverse modulo `p^m`). The block sum is computed by
internal induction on the progression, adding one dummy bit at a time
(`ArithmeticControllerData.bsum_add_pt`); no reindexing of finite sums is
used.

Exports: `controller_choice` (any target residue `θ`) and
`rank_calibration` (target `Γ·P(S) + d·s ≡ R0`, for a unit `Γ` modulo `M`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticControllerChoice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift ArithmeticControllerData ArithmeticPackingBlocks
  SetTheory.BusyBeaver.ZFC.ArithmeticCantor
attribute [local instance] Classical.propDecidable

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem le_add_self'' (x y : V) : x ≤ x + y := le_add_of_nonneg_right (Arithmetic.zero_le y)

/-! ## Progression sums -/

/-- `Σ_{t<i} (o+t)`. -/
def sig (o i : V) : V := i * o + (triangle i - i)

instance sig_definable (o : V) : 𝚺₁-Function₁ (sig o) := by
  unfold sig triangle; definability

theorem sig_succ (o i : V) : sig o (i + 1) = sig o i + (o + i) := by
  unfold sig
  have h := le_triangle i
  rw [triangle_succ, show triangle i + i + 1 - (i + 1) = triangle i by
    rw [add_assoc, add_tsub_cancel_right]]
  conv_lhs => rw [← tsub_add_cancel_of_le h]
  ring

/-! ## Dummy maps -/

/-- `j` is a dummy position `2 + 120198·e` with `e < P`. -/
def IsPos (P j : V) : Prop := 2 ≤ j ∧ (j - 2) % 120198 = 0 ∧ (j - 2) / 120198 < P

/-- The selected coordinates: the progression `[o, o+i)` and, if `ε = 1`, `last`. -/
def Sel (o ε last i z : V) : Prop := (o ≤ z ∧ z < o + i) ∨ (ε = 1 ∧ z = last)

/-- The dummy bit at block `j`. -/
def dmap (P o ε last i j : V) : V :=
  if IsPos P j ∧ Sel o ε last i (zc P ((j - 2) / 120198)) then 1 else 0

attribute [local irreducible] zc

theorem fun2_of_rel {f : V → V → V} {R : V → V → V → Prop}
    (hR : 𝚺₁.Definable (fun v : Fin 3 → V => R (v 0) (v 1) (v 2)))
    (h : ∀ y a b, R y a b ↔ y = f a b) : 𝚺₁-Function₂ f :=
  hR.of_iff fun v => (h (v 0) (v 1) (v 2)).symm

/-- The graph of `dmap`. -/
def DRel (P o ε last y i j : V) : Prop :=
  ((IsPos P j ∧ Sel o ε last i (zc P ((j - 2) / 120198))) ∧ y = 1) ∨
    (¬(IsPos P j ∧ Sel o ε last i (zc P ((j - 2) / 120198))) ∧ y = 0)

instance dmap_definable (P o ε last : V) : 𝚺₁-Function₂ (dmap P o ε last) :=
  fun2_of_rel (R := DRel P o ε last) (by unfold DRel IsPos Sel; definability)
    (fun y i j => by
      by_cases h : IsPos P j ∧ Sel o ε last i (zc P ((j - 2) / 120198)) <;> simp [DRel, dmap, h])

attribute [local irreducible] dmap

instance dmap_definable₁ (P o ε last i : V) : 𝚺₁-Function₁ (dmap P o ε last i) := by
  definability

theorem dmap_le (P o ε last i j : V) : dmap P o ε last i j ≤ 1 := by
  unfold dmap; split <;> simp

private theorem dmap_added_zero {P o ε ε' last i i' j : V}
    (h : dmap P o ε' last i' j = dmap P o ε last i j + pt j j) :
    dmap P o ε last i j = 0 := by
  have hle := dmap_le P o ε' last i' j
  rw [h] at hle
  have hle' : dmap P o ε last i j + 1 ≤ 0 + 1 := by simpa [pt] using hle
  exact le_antisymm (le_of_add_le_add_right hle') (Arithmetic.zero_le _)

theorem pos_lt (e : V) : 2 ≤ pos e := by unfold pos; exact le_add_self'' 2 _

theorem isPos_pos {P e : V} (he : e < P) : IsPos P (pos e) ∧ (pos e - 2) / 120198 = e := by
  have h1 : pos e - 2 = 120198 * e := by unfold pos; rw [add_tsub_cancel_left]
  have h2 : (120198 * e) / 120198 = e := div_mul_right _ (by norm_num)
  refine ⟨⟨pos_lt e, by rw [h1]; simp, by rw [h1, h2]; exact he⟩, by rw [h1, h2]⟩

theorem pos_decode {P j : V} (hj : IsPos P j) : j = pos ((j - 2) / 120198) := by
  obtain ⟨h2, hm, _⟩ := hj
  have hd := div_add_mod (j - 2) 120198
  rw [hm, add_zero] at hd
  unfold pos
  rw [hd, add_tsub_cancel_of_le h2]

theorem pos_inj {e e' : V} (h : pos e = pos e') : e = e' := by
  unfold pos at h
  exact mul_cancel_left (by norm_num) (add_left_cancel h)

/-- Changing the selection by one coordinate adds one dummy bit. -/
theorem dmap_add {P o ε ε' last i i' e : V} (he : e < P)
    (hiff : ∀ z, Sel o ε' last i' z ↔ Sel o ε last i z ∨ z = zc P e)
    (hdisj : ¬ Sel o ε last i (zc P e))
    (hinj : ∀ e' < P, zc P e' = zc P e → e' = e) (j : V) :
    dmap P o ε' last i' j = dmap P o ε last i j + pt (pos e) j := by
  by_cases hj : IsPos P j
  · have hdecode : zc P ((j - 2) / 120198) = zc P e ↔ j = pos e := by
      constructor
      · intro h
        rw [pos_decode hj, hinj _ hj.2.2 h]
      · intro h
        rw [h, (isPos_pos he).2]
    by_cases h : j = pos e
    · subst j
      simp [dmap, pt, (isPos_pos he).1, (isPos_pos he).2, hiff, hdisj]
    · simp [dmap, pt, hj, hiff, hdecode, h]
  · have hne : j ≠ pos e := fun h => hj (h ▸ (isPos_pos he).1)
    simp [dmap, pt, hj, hne]

/-! ## The progression sum, by induction -/

theorem bsum_zero_fn {w : V} {f : V → V} [𝚺₁-Function₁ f] {n : V} (hw : 0 < w)
    (h0 : ∀ j < n, f j = 0) : bsum w f n = 0 :=
  bsum_unique (fun j hj => by rw [h0 j hj]; exact exp_pos w)
    ⟨exp_pos _, fun j hj => by rw [h0 j hj]; simp [ArithmeticWindowDigits.dig]⟩

theorem pos_lt_N {P e : V} (he : e < P) : pos e + P < 120199 * P := by
  have h1 : e + 1 ≤ P := lt_iff_succ_le.mp he
  unfold pos
  calc 2 + 120198 * e + P < 120198 + 120198 * e + P :=
        add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le (by norm_num) le_rfl) le_rfl
    _ = 120198 * (e + 1) + P := by ring
    _ ≤ 120198 * P + P := add_le_add (mul_le_mul_of_nonneg_left h1 (by simp)) le_rfl
    _ = 120199 * P := by ring

theorem cong_add {M a a' b b' : V} (hM : 0 < M) (ha : a % M = a' % M) (hb : b % M = b' % M) :
    (a + b) % M = (a' + b') % M := by
  rw [mod_add hM, ha, hb, ← mod_add hM]

theorem cong_mul (c : V) {M a a' : V} (hM : 0 < M) (ha : a % M = a' % M) :
    (c * a) % M = (c * a') % M := by
  rw [← mod_mul_mod_right c a hM, ha, mod_mul_mod_right c a' hM]

/-- One dummy at coordinate `e` contributes `B²(1 + C0·zc e)` modulo `C0·P`. -/
theorem exp_pos_mod {P e : V} (hP : 0 < P) :
    Exp.exp (94517 * pos e) % (94517 * 120199 * P) =
      (Exp.exp (94517 * 2) * (1 + 94517 * 120199 * zc P e)) % (94517 * 120199 * P) := by
  have hM : (0 : V) < 94517 * 120199 * P := mul_pos C0_pos hP
  rw [exp_pos_eq, ← mod_mul_mod_right _ _ hM, (zc_spec hP e).1]

theorem prog_sum (m o last : V) :
    ∀ i, o + i ≤ power 120199 m → ∃ Y,
      Blocks 94517 (dmap (power 120199 m) o 0 last i) (120199 * power 120199 m) Y ∧
      Y % (94517 * 120199 * power 120199 m) =
        (Exp.exp (94517 * 2) * (i + 94517 * 120199 * sig o i)) %
          (94517 * 120199 * power 120199 m) := by
  have hP : (0 : V) < power 120199 m := power_pos _ m p_pos
  have hM : (0 : V) < 94517 * 120199 * power 120199 m := mul_pos C0_pos hP
  have hw : (0 : V) < 94517 := by norm_num
  have hb : ∀ i j, dmap (power 120199 m) o 0 last i j < Exp.exp 94517 :=
    fun i j => lt_of_le_of_lt (dmap_le _ _ _ _ _ _) (one_lt_exp hw)
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · unfold Blocks; definability
  case zero =>
    intro _
    have h0 : ∀ j < 120199 * power (120199 : V) m, dmap (power 120199 m) o 0 last 0 j = 0 := by
      intro j _
      unfold dmap
      rw [if_neg]
      rintro ⟨_, h | h⟩
      · exact absurd (lt_of_le_of_lt h.1 h.2) (by simp)
      · exact absurd h.1 (by simp)
    refine ⟨_, bsum_blocks (fun j _ => hb 0 j), ?_⟩
    rw [bsum_zero_fn hw h0]
    simp [sig, triangle]
  case succ i ih =>
    intro hi
    have hi' : o + i < power 120199 m := lt_of_lt_of_le (by rw [← add_assoc]; exact lt_add_one _) hi
    obtain ⟨Y, hY, hYm⟩ := ih hi'.le
    obtain ⟨e, he, hze⟩ := zc_surj m (o + i) hi'
    have hadd := dmap_add (P := power 120199 m) (o := o) (ε := 0) (ε' := 0) (last := last)
      (i := i) (i' := i + 1) he
      (fun z => by
        unfold Sel
        rw [hze]
        constructor
        · rintro (⟨h1, h2⟩ | h)
          · rcases lt_or_eq_of_le (le_iff_lt_succ.mpr (by rwa [← add_assoc] at h2)) with h3 | h3
            · exact Or.inl (Or.inl ⟨h1, h3⟩)
            · exact Or.inr h3
          · exact Or.inl (Or.inr h)
        · rintro ((⟨h1, h2⟩ | h) | h)
          · exact Or.inl ⟨h1, lt_trans h2 (by rw [← add_assoc]; exact lt_add_one _)⟩
          · exact Or.inr h
          · exact Or.inl ⟨by rw [h]; exact le_add_self'' o i, by
              rw [h, ← add_assoc]; exact lt_add_one _⟩)
      (by unfold Sel; rw [hze]; rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact absurd h (_root_.lt_irrefl _)
          · exact absurd h (by simp))
      (fun e' he' h => zc_inj m e' e he' he h)
    have hq : pos e < 120199 * power 120199 m :=
      lt_of_le_of_lt (le_add_self'' _ _) (pos_lt_N he)
    have hfq := dmap_added_zero (hadd (pos e))
    have hsum := bsum_add_pt hw (f := dmap (power 120199 m) o 0 last i)
      (f' := dmap (power 120199 m) o 0 last (i + 1)) hq
      (fun j _ => dmap_le _ _ _ _ _ _) hfq (fun j _ => hadd j)
    refine ⟨_, bsum_blocks (fun j _ => hb (i + 1) j), ?_⟩
    rw [hsum, bsum_unique (fun j _ => hb i j) hY]
    rw [cong_add hM hYm (exp_pos_mod hP), hze, sig_succ]
    congr 1
    ring

/-- The whole dummy set: the progression of `k-1` coordinates and `last`. -/
theorem full_sum (m o last k : V) (hk : 1 ≤ k) (hok : o + (k - 1) ≤ power 120199 m)
    (hlast : last < power 120199 m) (hnc : ¬(o ≤ last ∧ last < o + (k - 1))) :
    bsum 94517 (dmap (power 120199 m) o 1 last (k - 1)) (120199 * power 120199 m) %
        (94517 * 120199 * power 120199 m) =
      (Exp.exp (94517 * 2) * (k + 94517 * 120199 * (sig o (k - 1) + last))) %
        (94517 * 120199 * power 120199 m) := by
  have hP : (0 : V) < power 120199 m := power_pos _ m p_pos
  have hM : (0 : V) < 94517 * 120199 * power 120199 m := mul_pos C0_pos hP
  have hw : (0 : V) < 94517 := by norm_num
  have hb : ∀ ε j, dmap (power 120199 m) o ε last (k - 1) j < Exp.exp 94517 :=
    fun ε j => lt_of_le_of_lt (dmap_le _ _ _ _ _ _) (one_lt_exp hw)
  obtain ⟨Y, hY, hYm⟩ := prog_sum m o last (k - 1) hok
  obtain ⟨e, he, hze⟩ := zc_surj m last hlast
  have hadd := dmap_add (P := power 120199 m) (o := o) (ε := 0) (ε' := 1) (last := last)
    (i := k - 1) (i' := k - 1) he
    (fun z => by
      unfold Sel
      rw [hze]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | ⟨h0, _⟩) | h)
        · exact Or.inl h
        · exact absurd h0 (by simp)
        · exact Or.inr ⟨rfl, h⟩)
    (by unfold Sel; rw [hze]; rintro (h | ⟨h0, _⟩)
        · exact hnc h
        · exact absurd h0 (by simp))
    (fun e' he' h => zc_inj m e' e he' he h)
  have hq : pos e < 120199 * power 120199 m :=
    lt_of_le_of_lt (le_add_self'' _ _) (pos_lt_N he)
  have hfq := dmap_added_zero (hadd (pos e))
  have hsum := bsum_add_pt hw (f := dmap (power 120199 m) o 0 last (k - 1))
    (f' := dmap (power 120199 m) o 1 last (k - 1)) hq
    (fun j _ => dmap_le _ _ _ _ _ _) hfq (fun j _ => hadd j)
  rw [hsum, bsum_unique (fun j _ => hb 0 j) hY, cong_add hM hYm (exp_pos_mod hP), hze]
  congr 1
  have hk' : k - 1 + 1 = k := tsub_add_cancel_of_le hk
  calc Exp.exp (94517 * 2) * (k - 1 + 94517 * 120199 * sig o (k - 1)) +
        Exp.exp (94517 * 2) * (1 + 94517 * 120199 * last)
      = Exp.exp (94517 * 2) * ((k - 1 + 1) + 94517 * 120199 * (sig o (k - 1) + last)) := by ring
    _ = _ := by rw [hk']

theorem odd_mod (x y : V) (h : x = 2 * y + 1) : x % 2 = 1 := by
  rw [h, mod_mul_add' _ _ (by norm_num : (0 : V) < 2)]
  exact mod_eq_self_of_lt (by norm_num)

theorem power_p_odd (m : V) : power (120199 : V) m % 2 = 1 := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [power_zero]; exact odd_mod 1 0 (by simp)
  case succ m ih =>
    have h1 : (1 : V) % 2 = 1 := odd_mod 1 0 (by simp)
    rw [power_succ, mod_mul (by norm_num : (0 : V) < 2), ih, odd_mod 120199 60099 p_odd,
      one_mul, h1]

/-- **The controller choice.** For every target residue `θ` there is a Σ1
Boolean dummy map, supported on safe blocks, whose block sum is `θ` modulo
`d·N`, `N = p^(m+1)`. -/
theorem controller_choice (m s θ : V) (hP2 : 2 * (94517 * 120199) < power 120199 m)
    (hs : s ≤ power 120199 m) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 120199 (m + 1) ∧ j + s < power 120199 (m + 1)) ∧
      bsum 94517 δ (power 120199 (m + 1)) % (94517 * power 120199 (m + 1)) =
        θ % (94517 * power 120199 (m + 1)) := by
  rw [power_succ 120199 m,
    show (94517 : V) * (120199 * power 120199 m) = 94517 * 120199 * power 120199 m by ring]
  have hP : (0 : V) < power 120199 m := power_pos _ m p_pos
  have hM : (0 : V) < 94517 * 120199 * power 120199 m := mul_pos C0_pos hP
  have hC0P : (94517 : V) * 120199 ≤ power 120199 m :=
    le_trans (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)) hP2.le
  have hMge : (94517 : V) * 120199 ≤ 94517 * 120199 * power 120199 m :=
    le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hP)
  -- (1) a preimage of θ under multiplication by B² (M is odd)
  have hModd : (94517 * 120199 * power (120199 : V) m) % 2 = 1 := by
    have h1 : (1 : V) % 2 = 1 := odd_mod 1 0 (by simp)
    rw [mod_mul (by norm_num : (0 : V) < 2), mod_mul (by norm_num : (0 : V) < 2) (a := 94517),
      odd_mod 94517 47258 (by norm_num), odd_mod 120199 60099 p_odd, power_p_odd,
      one_mul, h1, one_mul, h1]
  set M := (94517 : V) * 120199 * power 120199 m with hMdef
  have h2eq : 2 * (M / 2 + 1) = 1 + M := by
    have hd := div_add_mod M 2
    rw [hModd] at hd
    calc 2 * (M / 2 + 1) = (2 * (M / 2) + 1) + 1 := by ring
      _ = 1 + M := by rw [hd, add_comm]
  set θ' := θ * power (M / 2 + 1) (94517 * 2) with hθ'
  have hB : (Exp.exp (94517 * 2) * θ') % M = θ % M := by
    obtain ⟨t, ht⟩ := power_one_add_mul M (94517 * 2)
    rw [hθ', ← power_two,
      show power 2 (94517 * 2) * (θ * power (M / 2 + 1) (94517 * 2)) =
        θ * (power 2 (94517 * 2) * power (M / 2 + 1) (94517 * 2)) by ring,
      ← power_mul_base, h2eq, ht, show θ * (1 + M * t) = θ + M * (θ * t) by ring,
      mod_add_mul' _ _ hM]
  -- (2) the count k ∈ [1, C0], k ≡ θ' (mod C0)
  have hC0 : (0 : V) < 94517 * 120199 := C0_pos
  set k := (θ' + 94517 * 120199 - 1) % (94517 * 120199) + 1 with hkdef
  have hk1 : 1 ≤ k := le_add_of_nonneg_left (Arithmetic.zero_le _)
  have hkC : k ≤ 94517 * 120199 := lt_iff_succ_le.mp (mod_lt _ hC0)
  have hkmod : k % (94517 * 120199) = θ' % (94517 * 120199) := by
    rw [hkdef, mod_add_mod_left _ _ hC0, tsub_add_cancel_of_le (le_trans (pos_iff_one_le.mp hC0)
      (le_add_of_nonneg_left (Arithmetic.zero_le _))),
      show θ' + 94517 * 120199 = θ' + 94517 * 120199 * 1 by ring, mod_add_mul' _ _ hC0]
  -- (3) the coordinate sum with C0·(x/C0) = x = θ' mod M + M - k
  have hkM : k ≤ M := le_trans hkC hMge
  set x := θ' % M + M - k with hxdef
  have hx : x + k = θ' % M + M :=
    tsub_add_cancel_of_le (le_trans hkM (le_add_of_nonneg_left (Arithmetic.zero_le _)))
  have hxC : x % (94517 * 120199) = 0 := by
    have h1 : (k + x) % (94517 * 120199) = (k + 0) % (94517 * 120199) := by
      rw [add_comm k x, hx, add_zero, hkmod, hMdef,
        show θ' % (94517 * 120199 * power 120199 m) + 94517 * 120199 * power 120199 m =
          θ' % (94517 * 120199 * power 120199 m) + 94517 * 120199 * power 120199 m by rfl,
        mod_add_mul' _ _ hC0, mod_of_mul_mod _ hC0]
    simpa using add_cancel_mod hC0 h1
  have hxeq : 94517 * 120199 * (x / (94517 * 120199)) = x := by
    have := div_add_mod x (94517 * 120199); rwa [hxC, add_zero] at this
  -- (4)–(6) assemble for an admissible offset o and last coordinate
  have key : ∀ o last, o ≤ 1 → last < power 120199 m →
      (last + sig o (k - 1)) % power 120199 m = (x / (94517 * 120199)) % power 120199 m →
      ¬(o ≤ last ∧ last < o + (k - 1)) →
      ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
        (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < 120199 * power 120199 m ∧
          j + s < 120199 * power 120199 m) ∧
        bsum 94517 δ (120199 * power 120199 m) % M = θ % M := by
    intro o last ho hlast hsum hnc
    have hok : o + (k - 1) ≤ power 120199 m := by
      calc o + (k - 1) ≤ 1 + (k - 1) := add_le_add ho le_rfl
        _ = k := add_tsub_cancel_of_le hk1
        _ ≤ power 120199 m := le_trans hkC hC0P
    refine ⟨dmap (power 120199 m) o 1 last (k - 1), inferInstance,
      fun j => dmap_le _ _ _ _ _ _, ?_, ?_⟩
    · intro j hj
      have hc : IsPos (power 120199 m) j := by
        by_contra hn
        exact hj (by unfold dmap; rw [if_neg (fun h => hn h.1)])
      have hje := pos_decode hc
      have hb := pos_lt_N hc.2.2
      rw [← hje] at hb
      refine ⟨lt_of_lt_of_le (by norm_num) hc.1, ?_, ?_⟩
      · exact lt_of_le_of_lt (add_le_add le_rfl (pos_iff_one_le.mp hP)) hb
      · exact lt_of_le_of_lt (add_le_add le_rfl hs) hb
    · have hfs := full_sum m o last k hk1 hok hlast hnc
      rw [← hMdef] at hfs
      rw [hfs]
      have hA : (94517 * 120199 * (sig o (k - 1) + last)) % M = x % M := by
        rw [hMdef, mul_mod_mul hC0 hP, add_comm, hsum, ← mul_mod_mul hC0 hP, hxeq]
      have hB2 : (k + 94517 * 120199 * (sig o (k - 1) + last)) % M = θ' % M := by
        rw [cong_add hM rfl hA, add_comm, hx, show θ' % M + M = θ' % M + M * 1 by ring,
          mod_add_mul' _ _ hM, mod_mod' _ hM]
      rw [cong_mul _ hM hB2, hB]
  -- the offset
  set υ := (x / (94517 * 120199)) % power 120199 m
  have lastOK : ∀ o, ((υ + (power 120199 m - 1) * sig o (k - 1)) % power 120199 m +
      sig o (k - 1)) % power 120199 m = (x / (94517 * 120199)) % power 120199 m := by
    intro o
    rw [mod_add_mod_left _ _ hP, add_assoc,
      show (power 120199 m - 1) * sig o (k - 1) + sig o (k - 1) =
        power (120199 : V) m * sig o (k - 1) by
        rw [show (power 120199 m - 1) * sig o (k - 1) + sig o (k - 1) =
          (power 120199 m - 1 + 1) * sig o (k - 1) by ring,
          tsub_add_cancel_of_le (pos_iff_one_le.mp hP)],
      mod_add_mul' _ _ hP, mod_mod' _ hP]
  set last0 := (υ + (power 120199 m - 1) * sig 0 (k - 1)) % power 120199 m
  by_cases hc : k - 1 ≤ last0
  · exact key 0 last0 (Arithmetic.zero_le _) (mod_lt _ hP) (lastOK 0)
      (fun h => absurd (by simpa using h.2) (not_lt.mpr hc))
  · have hlt : last0 < k - 1 := lt_of_not_ge hc
    have hk1P : k - 1 ≤ power 120199 m := le_trans tsub_le_self (le_trans hkC hC0P)
    have hlastP : last0 + (power 120199 m - (k - 1)) < power 120199 m := by
      calc last0 + (power 120199 m - (k - 1)) < (k - 1) + (power 120199 m - (k - 1)) :=
            add_lt_add_of_lt_of_le hlt le_rfl
        _ = power 120199 m := add_tsub_cancel_of_le hk1P
    have hsig : sig 1 (k - 1) = sig 0 (k - 1) + (k - 1) := by unfold sig; ring
    have hsum1 : (last0 + (power 120199 m - (k - 1)) + sig 1 (k - 1)) % power 120199 m =
        (x / (94517 * 120199)) % power 120199 m := by
      rw [hsig, show last0 + (power 120199 m - (k - 1)) + (sig 0 (k - 1) + (k - 1)) =
          (last0 + sig 0 (k - 1)) + ((power 120199 m - (k - 1)) + (k - 1)) by ring,
        tsub_add_cancel_of_le hk1P, show last0 + sig 0 (k - 1) + power 120199 m =
          last0 + sig 0 (k - 1) + power 120199 m * 1 by ring, mod_add_mul' _ _ hP, lastOK 0]
    -- the shifted last coordinate is at least k
    have hkk : (k - 1) + k ≤ power 120199 m := by
      calc (k - 1) + k ≤ k + k := add_le_add tsub_le_self le_rfl
        _ ≤ 94517 * 120199 + 94517 * 120199 := add_le_add hkC hkC
        _ = 2 * (94517 * 120199) := by ring
        _ ≤ power 120199 m := hP2.le
    have hge : k ≤ last0 + (power 120199 m - (k - 1)) :=
      le_trans (le_tsub_of_add_le_left hkk) (le_add_of_nonneg_left (Arithmetic.zero_le _))
    exact key 1 _ le_rfl hlastP hsum1 (fun h => absurd h.2 (not_lt.mpr (by
      rw [add_tsub_cancel_of_le hk1]; exact hge)))

/-- **Rank calibration (★).** For a unit `Γ` modulo `M = d·N` and any `R0`,
some admissible dummy map makes `Γ·P(S) + d·s ≡ R0 (mod M)`. -/
theorem rank_calibration (m s R0 Γ Γi : V) (hP2 : 2 * (94517 * 120199) < power 120199 m)
    (hs : s ≤ power 120199 m)
    (hΓ : (Γ * Γi) % (94517 * power 120199 (m + 1)) = 1 % (94517 * power 120199 (m + 1))) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 120199 (m + 1) ∧ j + s < power 120199 (m + 1)) ∧
      (Γ * bsum 94517 δ (power 120199 (m + 1)) + 94517 * s) % (94517 * power 120199 (m + 1)) =
        R0 % (94517 * power 120199 (m + 1)) := by
  have hM : (0 : V) < 94517 * power 120199 (m + 1) := mul_pos (by norm_num) (power_pos _ _ p_pos)
  obtain ⟨δ, hδd, hδb, hδs, hδ⟩ := controller_choice m s
    ((R0 + (94517 * power 120199 (m + 1) - 1) * (94517 * s)) * Γi) hP2 hs
  refine ⟨δ, hδd, hδb, hδs, ?_⟩
  have h1 : (Γ * bsum 94517 δ (power 120199 (m + 1))) % (94517 * power 120199 (m + 1)) =
      (R0 + (94517 * power 120199 (m + 1) - 1) * (94517 * s)) %
        (94517 * power 120199 (m + 1)) := by
    rw [cong_mul Γ hM hδ, show Γ * ((R0 + (94517 * power 120199 (m + 1) - 1) * (94517 * s)) * Γi) =
        (Γ * Γi) * (R0 + (94517 * power 120199 (m + 1) - 1) * (94517 * s)) by ring,
      ← mod_mul_mod_left _ _ hM, hΓ, mod_mul_mod_left _ _ hM, one_mul]
  rw [cong_add hM h1 rfl, add_assoc,
    show (94517 * power 120199 (m + 1) - 1) * (94517 * s) + 94517 * s =
        94517 * power (120199 : V) (m + 1) * (94517 * s) by
      rw [show (94517 * power 120199 (m + 1) - 1) * (94517 * s) + 94517 * s =
          (94517 * power (120199 : V) (m + 1) - 1 + 1) * (94517 * s) by ring,
        tsub_add_cancel_of_le (pos_iff_one_le.mp hM)],
    mod_add_mul' _ _ hM]

/-- With the exact rank variation `R + Γ·P(S) = R0` (K1), the calibrated rank
satisfies (★): `R ≡ d·s (mod d·N)`. -/
theorem calibrated {M R R0 Γ Pδ ds : V} (hM : 0 < M) (hvar : R + Γ * Pδ = R0)
    (hcal : (Γ * Pδ + ds) % M = R0 % M) : R % M = ds % M := by
  apply add_cancel_mod (a := Γ * Pδ) hM
  rw [hcal, ← hvar, add_comm]

end DiophantineConsistency.ArithmeticControllerChoice
