import DiophantineConsistency.P138.P138Cone

/-! # The strict cones of package 113

Package 113's guard `G = (A F)(B C) − (q − A F − B C)² > 0`, with the cones `A = 2^1113`,
`B = 2^666104`, needs more of the canonical cone registers `Uc = A F`, `Vc = B C` than package
138's calibration `q ≤ 2 Uc, 2 Vc ≤ 3 q` (`P138Cone.cones`): writing `2 Uc = q + u`,
`2 Vc = q + v`, `4 G = q² + q (u + v) − u² − u v − v²`, which is positive once `0 ≤ u, v < q`,
i.e. `Uc < q` and `Vc < q`. This module proves those two strict bounds (`strict_cones`).

They need the fine cell window of the P138 risk audit (§2.4):

* the source34 cell digits vanish on `[2196, 3296)` (`digit_zero_mid`, read off
  `Source34Cell.cellDigit`), so every cell is below `ρ^3296 + ρ^2196` (`cell_fine`);
* then the transport blocks satisfy `blk_j < (c0 + 2) ρ^8791` (`blk_fine`), instead of
  `2 (c0 + 2) ρ^8791`, and `c0 + 2 < 2^97` (from `4 c0 + 10 ≤ 3·2^97`);
* with `q = (2^1064921 − 1) rep + 1`, both `2^1113 (c0 + 2) ρ^8791` and
  `(ρ^3296 + ρ^2196) 2^666104` are at most `2^1064921 − 1`, so `Uc, Vc ≤ (2^1064921 − 1) rep < q`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P113Cone
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticStandardCasts ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPackingBlocks
  ArithmeticPacking ArithmeticRepunit
open Mixed121Kernel (rho)
open Mixed121Block (rho_pow_cast)
open Mixed121Column (perturb)
open Source34Kernel Source34KernelSplit Source34Cell Source34Word Source34Block P138Kernel P138Cone

attribute [local irreducible] paramKernel rho lowerKernelAt Source34Ports.lowNat Source34Ports.highNat

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The fine cell window -/

/-- The source34 cell digits vanish on `[2196, 3296)` (and beyond `3296`). -/
theorem digit_zero_mid (a d j : V) (h1 : 2196 ≤ j) (h2 : j ≠ 3296) : cellDigit a d j = 0 := by
  have hne : ∀ c : V, c < 2196 → j ≠ c := fun c hc h => absurd (h ▸ h1) (not_le.mpr hc)
  unfold cellDigit
  rw [if_neg (not_lt.mpr (le_trans (by norm_num) h1)),
    if_neg (hne 1063 (by norm_num)),
    if_neg (fun h => absurd h.2 (not_lt.mpr (le_trans (by norm_num) h1))),
    if_neg ?_]
  rintro (h | h | h | h)
  · exact hne 1095 (by norm_num) h
  · exact hne 1096 (by norm_num) h
  · exact hne 2195 (by norm_num) h
  · exact h2 h

/-- **The fine cell window**: `cell < ρ^3296 + ρ^2196`. -/
theorem cell_fine (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    packedCell a d < Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V) := by
  let f : V → V := cellDigit a d
  letI : 𝚺₁-Function₁ f := cellDigit_definable a d
  have hf : ∀ k : V, f k < Exp.exp 121 := fun k => digit_bound a d hd k
  -- the cell is the 3297-digit block sum
  have he : packedCell a d = bsum 121 f 3297 := by
    unfold packedCell
    apply bsum_unique (fun j _ => hf j)
    constructor
    · exact lt_of_lt_of_le (bsum_lt (fun j _ => hf j))
        (exp_monotone_le.mpr (by norm_num : (121:V)*3297 ≤ 121*8801))
    · intro j hj
      by_cases hlow : j < 3297
      · exact dig_bsum (fun k _ => hf k) hlow
      · have hge : 3297 ≤ j := not_lt.mp hlow
        have hjpow : Exp.exp (121*3297 : V) ≤ Exp.exp (121*j) :=
          exp_monotone_le.mpr (mul_le_mul_of_nonneg_left hge (by norm_num))
        have hz : dig 121 (bsum 121 f 3297) j = 0 := by
          unfold dig
          rw [div_eq_zero_of_lt _ (lt_of_lt_of_le (bsum_lt (fun k _ => hf k)) hjpow)]
          simp
        rw [hz]
        exact (digit_zero_after a d j ha hj hge).symm
  -- its top digit is the anchor
  have hs : bsum 121 f (3296 + 1) = bsum 121 f 3296 + f 3296 * Exp.exp (121 * 3296) :=
    bsum_succ (fun j _ => hf j)
  have h3296 : f 3296 = 1 := by
    have h := at_anchor a d 3296 (by norm_num)
    rw [Nat.cast_ofNat] at h
    exact h
  -- and the digits in `[2196, 3296)` vanish
  have hm : bsum 121 f 3296 = bsum 121 f 2196 := by
    apply bsum_unique (fun j _ => hf j)
    constructor
    · exact lt_of_lt_of_le (bsum_lt (fun j _ => hf j))
        (exp_monotone_le.mpr (by norm_num : (121:V)*2196 ≤ 121*3296))
    · intro j hj
      by_cases hlow : j < 2196
      · exact dig_bsum (fun k _ => hf k) hlow
      · have hge : 2196 ≤ j := not_lt.mp hlow
        have hjpow : Exp.exp (121*2196 : V) ≤ Exp.exp (121*j) :=
          exp_monotone_le.mpr (mul_le_mul_of_nonneg_left hge (by norm_num))
        have hz : dig 121 (bsum 121 f 2196) j = 0 := by
          unfold dig
          rw [div_eq_zero_of_lt _ (lt_of_lt_of_le (bsum_lt (fun k _ => hf k)) hjpow)]
          simp
        rw [hz]
        exact (digit_zero_mid a d j hge (ne_of_lt hj)).symm
  have hlt : bsum 121 f 2196 < Exp.exp (121 * 2196 : V) := bsum_lt (fun j _ => hf j)
  rw [he, show (3297 : V) = 3296 + 1 by norm_num, hs, hm, h3296, one_mul, add_comm]
  exact add_lt_add_of_le_of_lt le_rfl hlt

/-- The fine per-cell window `ρ^3296 ≤ X_j < ρ^3296 + ρ^2196`. -/
def FineCells (N : V) (X : V → V) : Prop :=
  ∀ j < N, Exp.exp (121*3296 : V) ≤ X j ∧ X j < Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V)

theorem fine_cells_of_word (row δ : V → V) (N : V) (hrow : ∀ j < N, row j ≠ 1)
    (hδ : ∀ j, δ j ≤ 1) : FineCells N (perturb (baseCell row) δ) := by
  intro j hj
  rw [cell_eq row δ j (hδ j)]
  exact ⟨cell_lower _ _ (hδ j), cell_fine _ _ (hrow j hj) (hδ j)⟩

theorem cells_of_fine {N : V} {X : V → V} (h : FineCells N X) : Cells N X := by
  intro j hj
  obtain ⟨h1, h2⟩ := h j hj
  refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
  have : Exp.exp (121*2196 : V) ≤ Exp.exp (121*3296 : V) := exp_monotone_le.mpr (by norm_num)
  calc Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V) ≤
        Exp.exp (121*3296 : V) + Exp.exp (121*3296 : V) := add_le_add le_rfl this
    _ = 2 * Exp.exp (121*3296 : V) := by ring

/-! ## The fine transport blocks -/

section Blocks
variable {N s : V} {X : V → V} [𝚺₁-Function₁ X]

omit [𝚺₁-Function₁ X] in
/-- **`blk_j < (c0 + 2) ρ^8791`** on the fine window. -/
theorem blk_fine (hN : 0 < N) (hX : FineCells N X) (j : V) (hj : j < N) :
    blk 1064921 (paramKernel rho : V) N s X j < (((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V) := by
  have hC := cells_of_fine hX
  obtain ⟨_, hL2⟩ := lower_model (V := V)
  obtain ⟨_, hx2⟩ := hX j hj
  have hx2' := (hC j hj).2
  have h1 := hC (cyc N j 1) (cyc_lt hN j 1)
  have hs := hC (cyc N j s) (cyc_lt hN j s)
  have hlo : lo 1064921 (paramKernel rho : V) X j = ((lowerKernelAt rho : ℕ) : V) * X j := by
    unfold lo; exact low_product_remainder (X j) (small_of_cell hx2')
  have hhi : hi 1064921 (paramKernel rho : V) X (cyc N j 1) = Exp.exp 121 * X (cyc N j 1) := by
    unfold hi; exact high_product _ (small_of_cell h1.2)
  have hE : Exp.exp (121*5495 : V) * Exp.exp (121*3296 : V) = Exp.exp (121*8791 : V) :=
    exp_mul_exp (by norm_num)
  have hE' : Exp.exp (121*5495 : V) * Exp.exp (121*2196 : V) = Exp.exp (121*7691 : V) :=
    exp_mul_exp (by norm_num)
  have hE1 : Exp.exp (121 : V) * Exp.exp (121*3296 : V) = Exp.exp (121*3297 : V) :=
    exp_mul_exp (by norm_num)
  -- `c0 + 1 ≤ ρ`
  have hc1 : ((c0 : ℕ) : V) + 1 ≤ Exp.exp 121 := by
    have h := c0_model_upper (V := V)
    have h97 : Exp.exp (97 : V) ≤ Exp.exp 121 := exp_monotone_le.mpr (by norm_num)
    have : 4 * (((c0 : ℕ) : V) + 1) ≤ 4 * Exp.exp 121 := calc
      4 * (((c0 : ℕ) : V) + 1) ≤ 4 * ((c0 : ℕ) : V) + 10 := by
          rw [mul_add]; exact add_le_add le_rfl (by norm_num)
      _ ≤ 3 * Exp.exp 97 := h
      _ ≤ 4 * Exp.exp 121 := mul_le_mul (by norm_num) h97 (Arithmetic.zero_le _) (by norm_num)
    exact le_of_mul_le_mul_left this (by norm_num)
  have hpos : (0 : V) < Exp.exp (121*5495 : V) := exp_pos _
  unfold blk
  rw [hlo, hhi]
  -- the low product
  have ha : ((lowerKernelAt rho : ℕ) : V) * X j <
      (((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) + Exp.exp (121*7692 : V) := calc
    ((lowerKernelAt rho : ℕ) : V) * X j ≤
        ((lowerKernelAt rho : ℕ) : V) * (Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V)) :=
        mul_le_mul_of_nonneg_left hx2.le (Arithmetic.zero_le _)
    _ < ((((c0 : ℕ) : V) + 1) * Exp.exp (121*5495 : V)) *
          (Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V)) :=
        mul_lt_mul_of_pos_right hL2 (lt_of_lt_of_le (exp_pos _) (le_add_of_nonneg_right
          (Arithmetic.zero_le _)))
    _ = (((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) +
          (((c0 : ℕ) : V) + 1) * Exp.exp (121*7691 : V) := by rw [← hE, ← hE']; ring
    _ ≤ (((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) + Exp.exp (121*7692 : V) := by
        apply add_le_add le_rfl
        calc (((c0 : ℕ) : V) + 1) * Exp.exp (121*7691 : V) ≤
              Exp.exp 121 * Exp.exp (121*7691 : V) := mul_le_mul_of_nonneg_right hc1
                (Arithmetic.zero_le _)
          _ = Exp.exp (121*7692 : V) := exp_mul_exp (by norm_num)
  have hb : Exp.exp 121 * X (cyc N j 1) ≤ Exp.exp (121*7692 : V) := calc
    Exp.exp 121 * X (cyc N j 1) ≤ Exp.exp 121 * (2 * Exp.exp (121*3296 : V)) :=
        mul_le_mul_of_nonneg_left h1.2.le (Arithmetic.zero_le _)
    _ = Exp.exp (121*3297+1 : V) := by rw [exp_succ, ← hE1]; ring
    _ ≤ Exp.exp (121*7692 : V) := exp_monotone_le.mpr (by norm_num)
  have hc : X (cyc N j s) ≤ Exp.exp (121*7692 : V) := calc
    X (cyc N j s) ≤ 2 * Exp.exp (121*3296 : V) := hs.2.le
    _ = Exp.exp (121*3296+1 : V) := by rw [exp_succ]
    _ ≤ Exp.exp (121*7692 : V) := exp_monotone_le.mpr (by norm_num)
  have h3 : 3 * Exp.exp (121*7692 : V) ≤ Exp.exp (121*8791 : V) := calc
    3 * Exp.exp (121*7692 : V) ≤ Exp.exp 2 * Exp.exp (121*7692 : V) := by
        apply mul_le_mul_of_nonneg_right _ (Arithmetic.zero_le _)
        rw [show (2 : V) = 0 + 1 + 1 by norm_num, exp_succ, exp_succ, exp_zero]; norm_num
    _ = Exp.exp (2 + 121*7692 : V) := exp_mul_exp rfl
    _ ≤ Exp.exp (121*8791 : V) := exp_monotone_le.mpr (by norm_num)
  calc ((lowerKernelAt rho : ℕ) : V) * X j + Exp.exp 121 * X (cyc N j 1) + X (cyc N j s) <
      ((((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) + Exp.exp (121*7692 : V)) +
        Exp.exp (121*7692 : V) + Exp.exp (121*7692 : V) :=
        add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le ha hb) hc
    _ = (((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) + 3 * Exp.exp (121*7692 : V) := by ring
    _ ≤ (((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) + Exp.exp (121*8791 : V) :=
        add_le_add le_rfl h3
    _ = (((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V) := by ring

end Blocks

/-! ## The strict cones -/

section Cones
variable {N s : V} {X : V → V} [𝚺₁-Function₁ X]

/-- **The strict cones** `2^1113 F < q` and `C 2^666104 < q`, `q = 2^(1064921 N)`. -/
theorem strict_cones (hN : 0 < N) (hX : FineCells N X) :
    Exp.exp 1113 * Fw 1064921 (paramKernel rho : V) N s X < Exp.exp (1064921*N) ∧
      Cw 1064921 N X * Exp.exp 666104 < Exp.exp (1064921*N) := by
  have hrep := repunit_identity (V := V) 1064921 N
  set R : V := rep 1064921 N with hRdef
  have hBm : Exp.exp (1064921 : V) - 1 + 1 = Exp.exp 1064921 := tsub_add_cancel_of_le (one_le_exp _)
  set Bm : V := Exp.exp (1064921 : V) - 1 with hBmdef
  -- `q = Bm R + 1`
  have hq : Exp.exp (1064921*N : V) = Bm * R + 1 := hrep.symm
  have hlt : ∀ {Z : V}, Z ≤ Bm * R → Z < Exp.exp (1064921*N) := fun hZ => by
    rw [hq]; exact lt_of_le_of_lt hZ (lt_add_one _)
  -- `x < 2^1064921 ⇒ x ≤ Bm`
  have hle_Bm : ∀ {x : V}, x < Exp.exp 1064921 → x ≤ Bm := fun {x} h => by
    have h' : x + 1 ≤ Bm + 1 := by rw [hBm]; exact lt_iff_succ_le.mp h
    exact le_of_add_le_add_right h'
  have hXc := cells_of_fine hX
  constructor
  · -- the block bound and `(c0 + 2) 2^1113 ρ^8791 ≤ Bm`
    have hcB : (((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V) < Exp.exp 1064921 := by
      have h1 : ((c0 : ℕ) : V) + 2 < Exp.exp 97 := by
        have hc2 := c0_model_upper (V := V)
        have : 4 * (((c0 : ℕ) : V) + 2) < 4 * Exp.exp 97 := calc
          4 * (((c0 : ℕ) : V) + 2) < 4 * ((c0 : ℕ) : V) + 10 := by
              rw [show 4 * (((c0 : ℕ) : V) + 2) = 4 * ((c0 : ℕ) : V) + 8 by ring]
              exact add_lt_add_of_le_of_lt le_rfl (by norm_num)
          _ ≤ 3 * Exp.exp 97 := hc2
          _ ≤ 4 * Exp.exp 97 := mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
        exact lt_of_mul_lt_mul_left this (by norm_num)
      calc (((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V) < Exp.exp 97 * Exp.exp (121*8791 : V) :=
            mul_lt_mul_of_pos_right h1 (exp_pos _)
        _ = Exp.exp (97+121*8791 : V) := exp_mul_exp rfl
        _ ≤ Exp.exp 1064921 := exp_monotone_le.mpr (by norm_num)
    have hF : Fw 1064921 (paramKernel rho : V) N s X ≤
        ((((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V)) * R := by
      unfold Fw
      exact bsum_le_rep hcB (fun j hj => (blk_fine (s := s) hN hX j hj).le)
    have hP : Exp.exp 1113 * ((((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V)) ≤ Bm := by
      apply hle_Bm
      have h1 : ((c0 : ℕ) : V) + 2 < Exp.exp 97 := by
        have hc2 := c0_model_upper (V := V)
        have : 4 * (((c0 : ℕ) : V) + 2) < 4 * Exp.exp 97 := calc
          4 * (((c0 : ℕ) : V) + 2) < 4 * ((c0 : ℕ) : V) + 10 := by
              rw [show 4 * (((c0 : ℕ) : V) + 2) = 4 * ((c0 : ℕ) : V) + 8 by ring]
              exact add_lt_add_of_le_of_lt le_rfl (by norm_num)
          _ ≤ 3 * Exp.exp 97 := hc2
          _ ≤ 4 * Exp.exp 97 := mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
        exact lt_of_mul_lt_mul_left this (by norm_num)
      calc Exp.exp 1113 * ((((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V)) =
            (((c0 : ℕ) : V) + 2) * (Exp.exp 1113 * Exp.exp (121*8791 : V)) := by ring
        _ < Exp.exp 97 * (Exp.exp 1113 * Exp.exp (121*8791 : V)) :=
            mul_lt_mul_of_pos_right h1 (mul_pos (exp_pos _) (exp_pos _))
        _ = Exp.exp 1064921 := by
            rw [exp_mul_exp (by norm_num : (1113 : V) + 121*8791 = 1064824),
              exp_mul_exp (by norm_num : (97 : V) + 1064824 = 1064921)]
    apply hlt
    calc Exp.exp 1113 * Fw 1064921 (paramKernel rho : V) N s X ≤
          Exp.exp 1113 * (((((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V)) * R) :=
          mul_le_mul_of_nonneg_left hF (Arithmetic.zero_le _)
      _ = (Exp.exp 1113 * ((((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V))) * R := by ring
      _ ≤ Bm * R := mul_le_mul_of_nonneg_right hP (Arithmetic.zero_le _)
  · -- the cell bound and `(ρ^3296 + ρ^2196) 2^666104 ≤ Bm`
    have hXB : Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V) < Exp.exp 1064921 := by
      have h1 : Exp.exp (121*2196 : V) ≤ Exp.exp (121*3296 : V) := exp_monotone_le.mpr (by norm_num)
      calc Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V) ≤ 2 * Exp.exp (121*3296 : V) := by
            rw [two_mul]; exact add_le_add le_rfl h1
        _ = Exp.exp (121*3296 + 1 : V) := by rw [exp_succ]
        _ < Exp.exp 1064921 := exp_monotone.mpr (by norm_num)
    have hC : Cw 1064921 N X ≤ (Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V)) * R := by
      unfold Cw
      exact bsum_le_rep hXB (fun j hj => (hX j hj).2.le)
    have hP : (Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V)) * Exp.exp 666104 ≤ Bm := by
      apply hle_Bm
      have e1 : Exp.exp (121*3296 : V) * Exp.exp 666104 = Exp.exp 1064920 := exp_mul_exp (by norm_num)
      have e2 : Exp.exp (121*2196 : V) * Exp.exp 666104 = Exp.exp 931820 := exp_mul_exp (by norm_num)
      have h2 : Exp.exp (931820 : V) < Exp.exp 1064920 := exp_monotone.mpr (by norm_num)
      calc (Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V)) * Exp.exp 666104 =
            Exp.exp 1064920 + Exp.exp 931820 := by rw [add_mul, e1, e2]
        _ < Exp.exp 1064920 + Exp.exp 1064920 := add_lt_add_of_le_of_lt le_rfl h2
        _ = Exp.exp 1064921 := by
            rw [show (1064921 : V) = 1064920 + 1 by norm_num, exp_succ]; ring
    apply hlt
    calc Cw 1064921 N X * Exp.exp 666104 ≤
          ((Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V)) * R) * Exp.exp 666104 :=
          mul_le_mul_of_nonneg_right hC (Arithmetic.zero_le _)
      _ = ((Exp.exp (121*3296 : V) + Exp.exp (121*2196 : V)) * Exp.exp 666104) * R := by ring
      _ ≤ Bm * R := mul_le_mul_of_nonneg_right hP (Arithmetic.zero_le _)

end Cones

#print axioms digit_zero_mid
#print axioms cell_fine
#print axioms fine_cells_of_word
#print axioms blk_fine
#print axioms strict_cones

end DiophantineConsistency.P113Cone
