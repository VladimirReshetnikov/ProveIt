import GowersSzemeredi.Proofs16CoarseFunctionCover

/-! Regime splitting for multiple multilinearity.

`MultiplyLinear gamma r` asks, for every inner loss `theta` in `(0,1]`, for
covers whose graph count and width exponent are polynomial in `theta`. This
module shows that it suffices to have covers whose loss does not depend on
`theta` at all, provided the loss decays as a power of the box width:
`C * width^(-delta)`. Boxes where the target width `width^e` is at most two
are covered exactly by cells of at most `3^k` points. On the remaining boxes
the width is so large that `C * width^(-delta) <= theta`.

The four budget hypotheses compare the loss-free constants with
`b = c(r^-1,gamma,k)^r` and `1/b = q(r^-1,gamma,k)^r`, which are the extreme
values of the targets over `theta`. This reduces Theorem 16.2 to a structure
theorem whose losses do not depend on the requested loss. See
`Research/GowersSzemeredi/SECTION16_RESEARCH_NOTES.md`, part E. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-! ### Exact coarse covers of relations with bounded fibres -/

/-- A relation whose fibres have at most `M` points is covered exactly, with no
exceptional points, by `3^k * M` constant graphs on each cell of a proper
partition whose cells have width at least `min 2 width`. -/
theorem section16_coarse_relation_cover {N k : Nat} [NeZero N] (hk : 0 < k)
    (Gamma : Finset (Point N k × ZMod N)) (M : Nat)
    (hfib : ∀ x : Point N k, (Gamma.filter fun z => z.1 = x).card ≤ M)
    (P : Box N k) (hP : P.IsProper) :
    ∃ L : Nat, ∃ R : Fin L → Box N k,
      ∃ mu : Fin L → Fin (3 ^ k * M) → Point N k → ZMod N,
        IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
        (∀ j, min 2 P.width ≤ (R j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (R j).carrier → ∀ y, (x, y) ∈ Gamma → ∃ i, y = mu j i x := by
  classical
  have hcells : ∃ L : Nat, ∃ R : Fin L → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, min 2 P.width ≤ (R j).width) ∧ ∀ j, (R j).carrier.card ≤ 3 ^ k := by
    by_cases hw : 2 ≤ P.width
    · obtain ⟨L, R, hpart, hproper, haxes, _⟩ := P.bounded_partition hP hk 2 (by omega) hw
      refine ⟨L, R, hpart, fun j => (hproper j).1,
        fun j => (min_le_left _ _).trans (hproper j).2, fun j => ?_⟩
      apply (R j).card_le_pow_of_axis_card_le
      intro i
      rw [(hproper j).1 i]
      have hh := (haxes j i).2
      omega
    · obtain ⟨L, x, hpart⟩ := box_singleton_partition P
      refine ⟨L, fun j => pointSingletonBox (x j), hpart,
        fun j => pointSingletonBox_isProper _, fun j => ?_, fun j => ?_⟩
      · rw [pointSingletonBox_width hk]
        omega
      · rw [pointSingletonBox_carrier, Finset.card_singleton]
        exact Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨L, R, hpart, hproper, hwidth, hcard⟩ := hcells
  let S : Fin L → Finset (Point N k × ZMod N) := fun j =>
    Gamma.filter fun z => z.1 ∈ (R j).carrier
  have hS (j : Fin L) : (S j).card ≤ 3 ^ k * M := by
    have hsub : S j ⊆ (R j).carrier.biUnion (fun x => Gamma.filter fun z => z.1 = x) := by
      intro z hz
      obtain ⟨hzG, hzR⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_biUnion.mpr ⟨z.1, hzR, Finset.mem_filter.mpr ⟨hzG, rfl⟩⟩
    calc (S j).card
        ≤ ((R j).carrier.biUnion (fun x => Gamma.filter fun z => z.1 = x)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ x ∈ (R j).carrier, (Gamma.filter fun z => z.1 = x).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ (R j).carrier, M := Finset.sum_le_sum (fun x _ => hfib x)
      _ = (R j).carrier.card * M := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 3 ^ k * M := Nat.mul_le_mul_right _ (hcard j)
  let e := fun j : Fin L => (S j).equivFin.symm
  let mu : Fin L → Fin (3 ^ k * M) → Point N k → ZMod N := fun j i _x =>
    if hi : (i : Nat) < (S j).card then ((e j) ⟨i, hi⟩).val.2 else 0
  refine ⟨L, R, mu, hpart, hproper, hwidth, fun j i => isMultilinear_constant _, ?_⟩
  intro j x hx y hxy
  have hz : (x, y) ∈ S j := Finset.mem_filter.mpr ⟨hxy, hx⟩
  let a := (e j).symm ⟨(x, y), hz⟩
  let i : Fin (3 ^ k * M) := ⟨a.val, a.isLt.trans_le (hS j)⟩
  refine ⟨i, ?_⟩
  have hi : (i : Nat) < (S j).card := a.isLt
  dsimp only [mu]
  rw [dif_pos hi]
  have ha : (⟨i.val, hi⟩ : Fin (S j).card) = a := rfl
  rw [ha]
  simp [a]

/-! ### The two control functions at the extreme inner loss -/

theorem multipleC_pos {theta gamma : Real} (k : Nat) (ht : 0 < theta) (hg : 0 < gamma) :
    0 < multipleC theta gamma k := by
  unfold multipleC
  positivity

/-- The width-exponent target is at most `theta` times its value at `theta = 1`. -/
theorem multipleC_rpow_le_mul {theta gamma r : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hr : 1 ≤ r) :
    (multipleC (r⁻¹ * theta) gamma k) ^ r ≤ theta * (multipleC r⁻¹ gamma k) ^ r := by
  have hr0 : 0 < r := by linarith
  have hc1 := multipleC_pos k (inv_pos.mpr hr0) hg
  have hsplit : multipleC (r⁻¹ * theta) gamma k =
      theta ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) * multipleC r⁻¹ gamma k := by
    unfold multipleC
    rw [show gamma * (r⁻¹ * theta) = theta * (gamma * r⁻¹) by ring, mul_pow]
  rw [hsplit, Real.mul_rpow (by positivity) hc1.le]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hc1.le r)
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  have hn : (1 : Real) ≤ ((2 ^ (2 ^ (k + 8)) : Nat) : Real) := by
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  calc theta ^ (((2 ^ (2 ^ (k + 8)) : Nat) : Real) * r)
      ≤ theta ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_ge ht ht1 (one_le_mul_of_one_le_of_one_le hn hr)
    _ = theta := Real.rpow_one theta

/-- The graph-count target is at least its value at `theta = 1`. -/
theorem multipleQ_rpow_le {theta gamma r : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hr : 1 ≤ r) :
    (multipleQ r⁻¹ gamma k) ^ r ≤ (multipleQ (r⁻¹ * theta) gamma k) ^ r := by
  have hr0 : 0 < r := by linarith
  have hc1 := multipleC_pos k (inv_pos.mpr hr0) hg
  have hct := multipleC_pos k (mul_pos (inv_pos.mpr hr0) ht) hg
  unfold multipleQ
  rw [Real.inv_rpow hc1.le, Real.inv_rpow hct.le]
  apply inv_anti₀ (Real.rpow_pos_of_pos hct r)
  calc (multipleC (r⁻¹ * theta) gamma k) ^ r
      ≤ theta * (multipleC r⁻¹ gamma k) ^ r := multipleC_rpow_le_mul k ht ht1 hg hr
    _ ≤ (multipleC r⁻¹ gamma k) ^ r :=
        mul_le_of_le_one_left (Real.rpow_nonneg hc1.le r) ht1

/-! ### Power-decaying losses are below every requested loss on large boxes -/

/-- If `W^e > 2` with `e <= theta * b`, then a loss `C * W^(-delta)` is at most
`theta` as soon as `b * C <= delta * log 2`. -/
theorem section16_power_loss_le {W C delta theta e b : Real}
    (hW : 0 ≤ W) (he : 0 < e) (heb : e ≤ theta * b) (hb : 0 < b) (ht : 0 < theta)
    (hdelta : 0 < delta) (hC : 0 ≤ C) (hCb : b * C ≤ delta * Real.log 2)
    (hWe : 2 < W ^ e) : C * W ^ (-delta) ≤ theta := by
  have hW1 : 1 < W := by
    by_contra hle
    push_neg at hle
    have := Real.rpow_le_one hW hle he.le
    linarith
  have hWpos : 0 < W := by linarith
  have hlogW : 0 < Real.log W := Real.log_pos hW1
  have hlog : Real.log 2 < e * Real.log W := by
    have h := Real.log_lt_log (by norm_num) hWe
    rwa [Real.log_rpow hWpos] at h
  have hlog2 : Real.log 2 < b * theta * Real.log W := by
    have h := mul_le_mul_of_nonneg_right heb hlogW.le
    nlinarith
  set kappa := delta * Real.log 2 / b with hkappa
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkpos : 0 < kappa := by positivity
  have hlt : kappa / theta < delta * Real.log W := by
    rw [hkappa, div_div, div_lt_iff₀ (mul_pos hb ht)]
    nlinarith [mul_lt_mul_of_pos_left hlog2 hdelta]
  have hrpow : W ^ (-delta) = Real.exp (-(delta * Real.log W)) := by
    rw [Real.rpow_def_of_pos hWpos]
    congr 1
    ring
  have hexp : Real.exp (-(delta * Real.log W)) ≤ Real.exp (-(kappa / theta)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hx : 0 < kappa / theta := div_pos hkpos ht
  have hexp2 : Real.exp (-(kappa / theta)) ≤ theta / kappa := by
    rw [Real.exp_neg]
    calc (Real.exp (kappa / theta))⁻¹
        ≤ (kappa / theta)⁻¹ := inv_anti₀ hx (by linarith [Real.add_one_le_exp (kappa / theta)])
      _ = theta / kappa := inv_div _ _
  have hCk : C ≤ kappa := by
    rw [hkappa, le_div_iff₀ hb]
    linarith
  calc C * W ^ (-delta) = C * Real.exp (-(delta * Real.log W)) := by rw [hrpow]
    _ ≤ C * (theta / kappa) := mul_le_mul_of_nonneg_left (hexp.trans hexp2) hC
    _ ≤ kappa * (theta / kappa) :=
        mul_le_mul_of_nonneg_right hCk (div_nonneg ht.le hkpos.le)
    _ = theta := by rw [mul_comm]; exact div_mul_cancel₀ theta hkpos.ne'

/-! ### The reduction -/

/-- Covers whose exceptional fraction `C * width^(-delta)` does not depend on
a requested loss, with at most `Q` graphs on proper cells of width at least
`width^E`, on every proper box of width at least `T`. -/
def Section16PowerLossCover {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) (C delta Q E T : Real) : Prop :=
  ∀ P : Box N k, P.IsProper → T ≤ (P.width : Real) →
    ∃ L q : Nat, ∃ H : Finset (Point N k), ∃ R : Fin L → Box N k,
      ∃ mu : Fin L → Fin q → Point N k → ZMod N,
        H ⊆ P.carrier ∧
        (1 - C * (P.width : Real) ^ (-delta)) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧ (q : Real) ≤ Q ∧
        (∀ j, (P.width : Real) ^ E ≤ (R j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (R j).carrier → x ∈ H → ∀ y, (x, y) ∈ Gamma → ∃ i, y = mu j i x

/-- **Regime splitting.** Loss-independent covers with power-decaying losses
and bounded fibres give multiple multilinearity with the source's control
functions, once their constants fit the extreme targets `b = c(r^-1,gamma,k)^r`
and `1/b = q(r^-1,gamma,k)^r`. -/
theorem multiplyLinear_of_powerLossCover {N k : Nat} [NeZero N] (hk : 0 < k)
    {Gamma : Finset (Point N k × ZMod N)} {gamma r C delta Q E T : Real} (M : Nat)
    (hg : 0 < gamma) (hr : 1 ≤ r) (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hfib : ∀ x : Point N k, (Gamma.filter fun z => z.1 = x).card ≤ M)
    (hcov : Section16PowerLossCover Gamma C delta Q E T)
    (hQ : Q ≤ (multipleQ r⁻¹ gamma k) ^ r)
    (hM : ((3 ^ k * M : Nat) : Real) ≤ (multipleQ r⁻¹ gamma k) ^ r)
    (hE : (multipleC r⁻¹ gamma k) ^ r ≤ E)
    (hloss : (multipleC r⁻¹ gamma k) ^ r * C ≤ delta * Real.log 2)
    (hT : T ≤ (2 : Real) ^ (((multipleC r⁻¹ gamma k) ^ r)⁻¹)) :
    MultiplyLinear gamma r Gamma := by
  intro theta ht ht1 P hP
  have hr0 : 0 < r := by linarith
  set b := (multipleC r⁻¹ gamma k) ^ r with hb_def
  set e := (multipleC (r⁻¹ * theta) gamma k) ^ r with he_def
  have hb : 0 < b := Real.rpow_pos_of_pos (multipleC_pos k (inv_pos.mpr hr0) hg) r
  have he : 0 < e :=
    Real.rpow_pos_of_pos (multipleC_pos k (mul_pos (inv_pos.mpr hr0) ht) hg) r
  have heb : e ≤ theta * b := multipleC_rpow_le_mul k ht ht1 hg hr
  have hqmono := multipleQ_rpow_le k ht ht1 hg hr
  have hcard0 : (0 : Real) ≤ (P.carrier.card : Real) := Nat.cast_nonneg _
  by_cases hsmall : (P.width : Real) ^ e ≤ 2
  · obtain ⟨L, R, mu, hpart, hproper, hwidth, hmu, hcover⟩ :=
      section16_coarse_relation_cover hk Gamma M hfib P hP
    refine ⟨L, 3 ^ k * M, P.carrier, R, mu, Finset.Subset.refl _, ?_, hpart, hproper,
      hM.trans hqmono, ?_, hmu, fun j x hx _ y hy => hcover j x hx y hy⟩
    · nlinarith [mul_nonneg ht.le hcard0]
    · intro j
      have hmin : (P.width : Real) ^ e ≤ ((min 2 P.width : Nat) : Real) := by
        rcases Nat.lt_or_ge P.width 2 with hlt | hge
        · rw [min_eq_right hlt.le]
          interval_cases h : P.width
          · simp [Real.zero_rpow he.ne']
          · simp
        · rw [min_eq_left hge]
          exact_mod_cast hsmall
      exact hmin.trans (by exact_mod_cast hwidth j)
  · push_neg at hsmall
    have hW0 : (0 : Real) ≤ (P.width : Real) := Nat.cast_nonneg _
    have hW1 : 1 < (P.width : Real) := by
      by_contra hle
      push_neg at hle
      have := Real.rpow_le_one hW0 hle he.le
      linarith
    have hWpos : (0 : Real) < (P.width : Real) := by linarith
    have hTW : T ≤ (P.width : Real) := by
      have hlog : Real.log 2 < e * Real.log (P.width : Real) := by
        have h := Real.log_lt_log (by norm_num) hsmall
        rwa [Real.log_rpow hWpos] at h
      have hlogW : 0 < Real.log (P.width : Real) := Real.log_pos hW1
      have heb1 : e ≤ b := heb.trans (mul_le_of_le_one_left hb.le ht1)
      have hlogb : Real.log 2 < b * Real.log (P.width : Real) := by
        nlinarith [mul_le_mul_of_nonneg_right heb1 hlogW.le]
      refine hT.trans (le_of_lt ?_)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 2)]
      calc Real.exp (Real.log 2 * b⁻¹) < Real.exp (Real.log (P.width : Real)) := by
            apply Real.exp_lt_exp.mpr
            rw [← div_eq_mul_inv, div_lt_iff₀ hb]
            linarith
        _ = (P.width : Real) := Real.exp_log hWpos
    obtain ⟨L, q, H, R, mu, hH, hmass, hpart, hproper, hq, hw, hmu, hc⟩ := hcov P hP hTW
    have hlossle := section16_power_loss_le hW0 he heb hb ht hdelta hC hloss hsmall
    refine ⟨L, q, H, R, mu, hH, ?_, hpart, hproper, hq.trans (hQ.trans hqmono), ?_, hmu, hc⟩
    · calc (1 - theta) * (P.carrier.card : Real)
          ≤ (1 - C * (P.width : Real) ^ (-delta)) * (P.carrier.card : Real) :=
            mul_le_mul_of_nonneg_right (by linarith) hcard0
        _ ≤ H.card := hmass
    · intro j
      have heE : e ≤ E := (heb.trans (mul_le_of_le_one_left hb.le ht1)).trans hE
      exact (Real.rpow_le_rpow_of_exponent_le hW1.le heE).trans (hw j)

end LeanProofs.GowersSzemeredi
