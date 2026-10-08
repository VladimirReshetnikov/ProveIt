import GowersSzemeredi.Proofs16Slicing

/-! Bohr-set doubling: `|B(K;ρ)| ≤ 4^|K| · |B(K;ρ/2)|`.

Each coordinate `r · x` of a point of `B(K;ρ)` has centered value in
`[−ρN, ρN]`. Split that range into four cells of width `ρN/2`. Two points
in the same cell of every coordinate differ by an element of `B(K;ρ/2)`.
So each of the `4^|K|` fibres embeds into `B(K;ρ/2)` by translation.

This is the basic size control behind Bohr-set regularity, which the
packing step of the readout (R) needs (research notes J.2). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The cell index (`0..3`) of an integer `v` in `[−W, W]`, cells of width `W/2`. -/
def doublingCell (W : Real) (v : Int) : Fin 4 :=
  ⟨min 3 (⌊((v : Real) + W) / (W / 2)⌋.toNat), by omega⟩

/-- Two integers in `[−W, W]` with the same cell differ by at most `W/2`. -/
theorem doublingCell_close {W : Real} (hW : 0 < W) {v w : Int}
    (hv : |(v : Real)| ≤ W) (hw : |(w : Real)| ≤ W)
    (h : doublingCell W v = doublingCell W w) : |(v : Real) - w| ≤ W / 2 := by
  have hW2 : 0 < W / 2 := by positivity
  set a := ((v : Real) + W) / (W / 2) with ha
  set b := ((w : Real) + W) / (W / 2) with hb
  have ha0 : 0 ≤ a := div_nonneg (by linarith [(abs_le.mp hv).1]) hW2.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith [(abs_le.mp hw).1]) hW2.le
  have ha4 : a ≤ 4 := by
    rw [ha, div_le_iff₀ hW2]; linarith [(abs_le.mp hv).2]
  have hb4 : b ≤ 4 := by
    rw [hb, div_le_iff₀ hW2]; linarith [(abs_le.mp hw).2]
  have hcell : min 3 (⌊a⌋.toNat) = min 3 (⌊b⌋.toNat) := congrArg Fin.val h
  -- `|a - b| ≤ 1`
  have hab : |a - b| ≤ 1 := by
    have hfa := Int.floor_le a
    have hfa' := Int.lt_floor_add_one a
    have hfb := Int.floor_le b
    have hfb' := Int.lt_floor_add_one b
    have hfa0 : 0 ≤ ⌊a⌋ := Int.floor_nonneg.mpr ha0
    have hfb0 : 0 ≤ ⌊b⌋ := Int.floor_nonneg.mpr hb0
    have hfa4 : ⌊a⌋ ≤ 4 := by
      have h := Int.floor_le_floor ha4
      simpa using h
    have hfb4 : ⌊b⌋ ≤ 4 := by
      have h := Int.floor_le_floor hb4
      simpa using h
    rcases le_or_gt 3 ⌊a⌋ with h3a | h3a <;> rcases le_or_gt 3 ⌊b⌋ with h3b | h3b
    · -- both in the top cell `[3, 4]`
      have : (3 : Real) ≤ a := by
        have h3 : (3 : Real) ≤ (⌊a⌋ : Real) := by exact_mod_cast h3a
        linarith
      have : (3 : Real) ≤ b := by
        have h3 : (3 : Real) ≤ (⌊b⌋ : Real) := by exact_mod_cast h3b
        linarith
      rw [abs_le]; constructor <;> linarith
    · exfalso
      have : (⌊b⌋.toNat : Int) = ⌊b⌋ := Int.toNat_of_nonneg hfb0
      omega
    · exfalso
      have : (⌊a⌋.toNat : Int) = ⌊a⌋ := Int.toNat_of_nonneg hfa0
      omega
    · have hfa_eq : (⌊a⌋.toNat : Int) = ⌊a⌋ := Int.toNat_of_nonneg hfa0
      have hfb_eq : (⌊b⌋.toNat : Int) = ⌊b⌋ := Int.toNat_of_nonneg hfb0
      have heq : ⌊a⌋ = ⌊b⌋ := by omega
      have : ((⌊a⌋ : Int) : Real) = ((⌊b⌋ : Int) : Real) := by exact_mod_cast heq
      rw [abs_le]; constructor <;> linarith
  have hdiff : (v : Real) - w = (a - b) * (W / 2) := by
    rw [ha, hb]; field_simp; ring
  rw [hdiff, abs_mul, abs_of_pos hW2]
  calc |a - b| * (W / 2) ≤ 1 * (W / 2) := mul_le_mul_of_nonneg_right hab hW2.le
    _ = W / 2 := one_mul _

/-- **Bohr-set doubling.** -/
theorem bohr_card_le_four_pow {N : Nat} [NeZero N] (K : Finset (ZMod N)) {ρ : Real} (hρ : 0 < ρ) :
    (bohr K ρ).card ≤ 4 ^ K.card * (bohr K (ρ / 2)).card := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  set W : Real := ρ * N with hWdef
  have hW : 0 < W := by positivity
  -- the cell signature of a point
  let sig : ZMod N → (K → Fin 4) := fun x r => doublingCell W ((r.1 * x).valMinAbs)
  -- points with the same signature differ by an element of `B(K; ρ/2)`
  have hclose : ∀ x ∈ bohr K ρ, ∀ y ∈ bohr K ρ, sig x = sig y → x - y ∈ bohr K (ρ / 2) := by
    intro x hx y hy hxy
    unfold bohr at hx hy ⊢
    obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, hy⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
    have hvx : |(((r * x).valMinAbs : Int) : Real)| ≤ W := by
      have h := hx r hr
      unfold centeredAbs at h
      have e : (((r * x).valMinAbs.natAbs : Nat) : Real) = |(((r * x).valMinAbs : Int) : Real)| := by
        rw [Nat.cast_natAbs]; push_cast; rfl
      rw [← e, hWdef]
      exact h
    have hvy : |(((r * y).valMinAbs : Int) : Real)| ≤ W := by
      have h := hy r hr
      unfold centeredAbs at h
      have e : (((r * y).valMinAbs.natAbs : Nat) : Real) = |(((r * y).valMinAbs : Int) : Real)| := by
        rw [Nat.cast_natAbs]; push_cast; rfl
      rw [← e, hWdef]
      exact h
    have hc := doublingCell_close hW hvx hvy (congrFun hxy ⟨r, hr⟩)
    -- `r (x - y)` is represented by `valMinAbs (r x) - valMinAbs (r y)`
    have hrep : (((((r * x).valMinAbs - (r * y).valMinAbs : Int)) : ZMod N)) = r * (x - y) := by
      rw [Int.cast_sub, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
      ring
    have h1 := centeredAbs_intCast_le (N := N) ((r * x).valMinAbs - (r * y).valMinAbs)
    rw [hrep] at h1
    have h1R : (centeredAbs (r * (x - y)) : Real) ≤
        |(((r * x).valMinAbs : Int) : Real) - (((r * y).valMinAbs : Int) : Real)| := by
      have : ((((r * x).valMinAbs - (r * y).valMinAbs).natAbs : Nat) : Real) =
          |(((r * x).valMinAbs : Int) : Real) - (((r * y).valMinAbs : Int) : Real)| := by
        rw [Nat.cast_natAbs]; push_cast; rfl
      rw [← this]; exact_mod_cast h1
    calc (centeredAbs (r * (x - y)) : Real) ≤ W / 2 := h1R.trans hc
      _ = ρ / 2 * N := by rw [hWdef]; ring
  -- fibres of the signature map embed into `B(K; ρ/2)`
  have hfib : ∀ s : K → Fin 4,
      ((bohr K ρ).filter fun x => sig x = s).card ≤ (bohr K (ρ / 2)).card := by
    intro s
    by_cases hne : ((bohr K ρ).filter fun x => sig x = s).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      obtain ⟨hx₀B, hx₀s⟩ := Finset.mem_filter.mp hx₀
      apply Finset.card_le_card_of_injOn (fun x => x - x₀)
      · intro x hx
        obtain ⟨hxB, hxs⟩ := Finset.mem_filter.mp hx
        exact hclose x hxB x₀ hx₀B (hxs.trans hx₀s.symm)
      · intro x _ y _ h
        simpa using h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  calc (bohr K ρ).card = ∑ s : K → Fin 4, ((bohr K ρ).filter fun x => sig x = s).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext x
          simp
        · intro s _ t _ hst
          rw [Function.onFun, Finset.disjoint_filter]
          intro x _ hs ht
          exact hst (hs.symm.trans ht)
    _ ≤ ∑ _s : K → Fin 4, (bohr K (ρ / 2)).card := Finset.sum_le_sum fun s _ => hfib s
    _ = 4 ^ K.card * (bohr K (ρ / 2)).card := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun]

end LeanProofs.GowersSzemeredi
