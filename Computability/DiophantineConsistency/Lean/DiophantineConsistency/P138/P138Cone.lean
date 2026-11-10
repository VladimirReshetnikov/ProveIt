import DiophantineConsistency.Source34.Source34High
import DiophantineConsistency.Source34.Source34Block
import DiophantineConsistency.P138.P138Kernel

/-! # Canonical cone calibration (C2) for package 138

At the source34 tuple, `q = B^N` with `B = 2^1064921 = ρ^8801`, `ρ = 2^121`, and the packing
words are `C = Σ_{j<N} B^j X_j`, `F = Σ_{j<N} B^j blk_j` (`ArithmeticPacking.Cw`, `Fw`). The
138 cone registers are `Uc = 2^1113 F` and `Vc = 2^666104 C`. This module proves the weakened
targets of the P138 risk audit (§2.4):

    (C2a)  q ≤ 2·2^1113·F ≤ 3q,        (C2b)  q ≤ 2·C·2^666104 ≤ 3q        (`cones`)

for every `N > 0`, stride `s` and every cell word with `ρ^3296 ≤ X_j < 2ρ^3296` (`Cells`).
The route's stronger `5Uc < 4q`, `5Vc < 3q` are true but need the fine cell bound
`X_j < ρ^3296 + ρ^2196`, which is not in the tree; (C2a)/(C2b) already give `Derr ≤ q²/2`.

Ingredients:

* the top coefficient `c0 = clause(row 0)` of the lower kernel (`P138Kernel`), cast:
  `c0 ρ^5495 ≤ lower < (c0+1) ρ^5495` (`lower_model`), `2^97 ≤ 2c0`, `4c0 + 10 ≤ 3·2^97`;
* every cell has digit `1` at the anchor `3296` (`cell_lower`) and is below `2ρ^3296`;
* `lo_j = lower·X_j`, `hi = ρ X` (`Source34Block`), so
  `c0 ρ^8791 ≤ blk_j < 2(c0+2) ρ^8791` (`blk_bounds`);
* `B^(N−1) f_(N−1) ≤ bsum f N ≤ m·rep N` (`bsum_top`, `bsum_le_rep`) and
  `(B − 1) rep + 1 = q`, with `121·8791 + 1113 + 97 = 121·3296 + 666104 + 1 = 1064921`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P138Cone
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticStandardCasts ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPackingBlocks
  ArithmeticPacking ArithmeticRepunit
open Mixed121Kernel (rho)
open Mixed121Block (rho_pow_cast)
open Mixed121Column (perturb)
open Source34Kernel Source34KernelSplit Source34Cell Source34Word Source34Block P138Kernel

attribute [local irreducible] paramKernel rho lowerKernelAt Source34Ports.lowNat Source34Ports.highNat

/-! ## Model forms -/

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem lower_model :
    ((c0 : ℕ) : V) * Exp.exp (121*5495 : V) ≤ ((lowerKernelAt rho : ℕ) : V) ∧
      ((lowerKernelAt rho : ℕ) : V) < (((c0 : ℕ) : V) + 1) * Exp.exp (121*5495 : V) := by
  obtain ⟨h1, h2⟩ := lower_nat
  have e : ((rho ^ 5495 : ℕ) : V) = Exp.exp (121*5495 : V) := by
    rw [rho_pow_cast]; simp only [Nat.cast_mul, Nat.cast_ofNat]
  have h1' : ((c0 * rho ^ 5495 : ℕ) : V) ≤ ((lowerKernelAt rho : ℕ) : V) := by exact_mod_cast h1
  have h2' : ((lowerKernelAt rho : ℕ) : V) < (((c0 + 1) * rho ^ 5495 : ℕ) : V) := by exact_mod_cast h2
  rw [Nat.cast_mul, e] at h1' h2'
  rw [Nat.cast_add, Nat.cast_one] at h2'
  exact ⟨h1', h2'⟩

theorem c0_model_lower : Exp.exp (97 : V) ≤ 2 * ((c0 : ℕ) : V) := by
  have h : ((2 ^ 97 : ℕ) : V) ≤ ((2 * c0 : ℕ) : V) := by exact_mod_cast c0_lower
  rw [← cast_exp, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat] at h
  exact h

theorem c0_model_upper : 4 * ((c0 : ℕ) : V) + 10 ≤ 3 * Exp.exp (97 : V) := by
  have h : ((4 * c0 + 10 : ℕ) : V) ≤ ((3 * 2 ^ 97 : ℕ) : V) := by exact_mod_cast c0_upper
  rw [Nat.cast_mul 3, ← cast_exp, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat,
    Nat.cast_ofNat, Nat.cast_ofNat] at h
  exact h

theorem exp_mul_exp {a b c : V} (h : a + b = c) : Exp.exp a * Exp.exp b = Exp.exp c := by
  rw [← exp_add, h]

/-! ## Cells -/

/-- Every cell has digit `1` at the anchor `3296`. -/
theorem cell_lower (a d : V) (hd : d ≤ 1) : Exp.exp (121*3296 : V) ≤ packedCell a d := by
  have h := packedCell_digit a d 3296 hd (by norm_num)
  have h1 := at_anchor a d 3296 (by norm_num)
  rw [Nat.cast_ofNat] at h1
  rw [h1] at h
  unfold dig at h
  by_contra hlt
  rw [div_eq_zero_of_lt _ (not_le.mp hlt)] at h
  simp at h

theorem cell_eq (row δ : V → V) (j : V) (hδ : δ j ≤ 1) :
    perturb (baseCell row) δ j = packedCell (row j) (δ j) := by
  rcases le_one_iff_eq_zero_or_one.mp hδ with hz | ho
  · simp [perturb, baseCell, hz]
  · change packedCell (row j) 0 + Exp.exp (121*1063) * δ j = _
    rw [ho, mul_one, ← cell_one]

/-- The per-cell window `ρ^3296 ≤ X_j < 2ρ^3296`. -/
def Cells (N : V) (X : V → V) : Prop :=
  ∀ j < N, Exp.exp (121*3296 : V) ≤ X j ∧ X j < 2 * Exp.exp (121*3296 : V)

theorem cells_of_word (row δ : V → V) (N : V) (hrow : ∀ j < N, row j ≠ 1) (hδ : ∀ j, δ j ≤ 1) :
    Cells N (perturb (baseCell row) δ) := by
  intro j hj
  rw [cell_eq row δ j (hδ j)]
  exact ⟨cell_lower _ _ (hδ j), packedCell_lt_twice_top _ _ (hrow j hj) (hδ j)⟩

theorem small_of_cell {x : V} (h : x < 2 * Exp.exp (121*3296 : V)) :
    x < Exp.exp (121*3297+1 : V) := by
  calc x < 2 * Exp.exp (121*3296 : V) := h
    _ = Exp.exp (121*3296+1 : V) := by rw [exp_succ]
    _ ≤ Exp.exp (121*3297+1 : V) := exp_monotone_le.mpr (by norm_num)

/-! ## Transport blocks -/

section Blocks
variable {N s : V} {X : V → V} [𝚺₁-Function₁ X]

theorem blk_bounds (hN : 0 < N) (hX : Cells N X) (j : V) (hj : j < N) :
    ((c0 : ℕ) : V) * Exp.exp (121*8791 : V) ≤ blk 1064921 (paramKernel rho : V) N s X j ∧
      blk 1064921 (paramKernel rho : V) N s X j <
        2 * (((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V) := by
  obtain ⟨hL1, hL2⟩ := lower_model (V := V)
  obtain ⟨hx1, hx2⟩ := hX j hj
  have h1 := hX (cyc N j 1) (cyc_lt hN j 1)
  have hs := hX (cyc N j s) (cyc_lt hN j s)
  have hlo : lo 1064921 (paramKernel rho : V) X j = ((lowerKernelAt rho : ℕ) : V) * X j := by
    unfold lo; exact low_product_remainder (X j) (small_of_cell hx2)
  have hhi : hi 1064921 (paramKernel rho : V) X (cyc N j 1) = Exp.exp 121 * X (cyc N j 1) := by
    unfold hi; exact high_product _ (small_of_cell h1.2)
  have hE : Exp.exp (121*5495 : V) * Exp.exp (121*3296 : V) = Exp.exp (121*8791 : V) :=
    exp_mul_exp (by norm_num)
  have hE1 : Exp.exp (121 : V) * Exp.exp (121*3296 : V) = Exp.exp (121*3297 : V) :=
    exp_mul_exp (by norm_num)
  have hpos : (0 : V) < Exp.exp (121*3296 : V) := exp_pos _
  unfold blk
  rw [hlo, hhi]
  constructor
  · calc ((c0 : ℕ) : V) * Exp.exp (121*8791 : V) =
          (((c0 : ℕ) : V) * Exp.exp (121*5495 : V)) * Exp.exp (121*3296 : V) := by rw [← hE]; ring
      _ ≤ ((lowerKernelAt rho : ℕ) : V) * X j :=
          mul_le_mul hL1 hx1 (Arithmetic.zero_le _) (Arithmetic.zero_le _)
      _ ≤ ((lowerKernelAt rho : ℕ) : V) * X j + Exp.exp 121 * X (cyc N j 1) + X (cyc N j s) := by
          rw [add_assoc]; exact le_add_of_nonneg_right (Arithmetic.zero_le _)
  · have ha : ((lowerKernelAt rho : ℕ) : V) * X j <
        2 * (((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) := calc
      ((lowerKernelAt rho : ℕ) : V) * X j ≤ ((lowerKernelAt rho : ℕ) : V) * (2 * Exp.exp (121*3296 : V)) :=
          mul_le_mul_of_nonneg_left hx2.le (Arithmetic.zero_le _)
      _ < ((((c0 : ℕ) : V) + 1) * Exp.exp (121*5495 : V)) * (2 * Exp.exp (121*3296 : V)) :=
          mul_lt_mul_of_pos_right hL2 (mul_pos (by norm_num) hpos)
      _ = 2 * (((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) := by rw [← hE]; ring
    have hb : Exp.exp 121 * X (cyc N j 1) ≤ Exp.exp (121*8791 : V) := calc
      Exp.exp 121 * X (cyc N j 1) ≤ Exp.exp 121 * (2 * Exp.exp (121*3296 : V)) :=
          mul_le_mul_of_nonneg_left h1.2.le (Arithmetic.zero_le _)
      _ = Exp.exp (121*3297+1 : V) := by rw [exp_succ, ← hE1]; ring
      _ ≤ Exp.exp (121*8791 : V) := exp_monotone_le.mpr (by norm_num)
    have hc : X (cyc N j s) ≤ Exp.exp (121*8791 : V) := calc
      X (cyc N j s) ≤ 2 * Exp.exp (121*3296 : V) := hs.2.le
      _ = Exp.exp (121*3296+1 : V) := by rw [exp_succ]
      _ ≤ Exp.exp (121*8791 : V) := exp_monotone_le.mpr (by norm_num)
    calc ((lowerKernelAt rho : ℕ) : V) * X j + Exp.exp 121 * X (cyc N j 1) + X (cyc N j s) <
        2 * (((c0 : ℕ) : V) + 1) * Exp.exp (121*8791 : V) + Exp.exp (121*8791 : V) +
          Exp.exp (121*8791 : V) := add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le ha hb) hc
      _ = 2 * (((c0 : ℕ) : V) + 2) * Exp.exp (121*8791 : V) := by ring

end Blocks

/-! ## Block sums -/

theorem bsum_top {w : V} {f : V → V} [𝚺₁-Function₁ f] {n : V}
    (hf : ∀ j < n + 1, f j < Exp.exp w) : Exp.exp (w * n) * f n ≤ bsum w f (n + 1) := by
  calc Exp.exp (w * n) * f n = f n * Exp.exp (w * n) := mul_comm _ _
    _ ≤ bsum w f n + f n * Exp.exp (w * n) := le_add_of_nonneg_left (Arithmetic.zero_le _)
    _ = bsum w f (n + 1) := (bsum_succ hf).symm

theorem bsum_le_rep {w c : V} {f : V → V} [𝚺₁-Function₁ f] {n : V} (hc : c < Exp.exp w)
    (hf : ∀ j < n, f j ≤ c) : bsum w f n ≤ c * rep w n := by
  let g : V → V := fun j => c - f j
  haveI : 𝚺₁-Function₁ g := by definability
  haveI : 𝚺₁-Function₁ (fun _ : V => c) := by definability
  have hadd := bsum_add (w := w) (f := f) (g := g) (h := fun _ => c) (n := n)
    (fun j hj => by
      show f j + (c - f j) < Exp.exp w
      rw [add_tsub_cancel_of_le (hf j hj)]; exact hc)
    (fun j hj => (add_tsub_cancel_of_le (hf j hj)).symm)
  rw [bsum_const_rep hc] at hadd
  rw [hadd]
  exact le_add_of_nonneg_right (Arithmetic.zero_le _)

/-! ## The cones -/

section Cones
variable {N s : V} {X : V → V} [𝚺₁-Function₁ X]

/-- **(C2a) and (C2b).** -/
theorem cones (hN : 0 < N) (hX : Cells N X) :
    Exp.exp (1064921*N) ≤ 2 * (Exp.exp 1113 * Fw 1064921 (paramKernel rho : V) N s X) ∧
      2 * (Exp.exp 1113 * Fw 1064921 (paramKernel rho : V) N s X) ≤ 3 * Exp.exp (1064921*N) ∧
      Exp.exp (1064921*N) ≤ 2 * (Cw 1064921 N X * Exp.exp 666104) ∧
      2 * (Cw 1064921 N X * Exp.exp 666104) ≤ 3 * Exp.exp (1064921*N) := by
  have hrep := repunit_identity (V := V) 1064921 N
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (tsub_add_cancel_of_le (pos_iff_one_le.mp hN)).symm⟩
  obtain ⟨hc1, hc2⟩ := And.intro (c0_model_lower (V := V)) (c0_model_upper (V := V))
  set c : V := ((c0 : ℕ) : V) with hcdef
  set R : V := rep 1064921 (M + 1) with hRdef
  set Q : V := Exp.exp (1064921*M) with hQdef
  have hq : Exp.exp (1064921*(M+1) : V) = Exp.exp 1064921 * Q := by
    rw [hQdef, ← exp_add]; congr 1; ring
  rw [hq] at hrep ⊢
  -- constants
  have hP : Exp.exp (97 : V) * (Exp.exp 1113 * Exp.exp (121*8791 : V)) = Exp.exp 1064921 := by
    rw [exp_mul_exp (by norm_num : (1113 : V) + 121*8791 = 1064824),
      exp_mul_exp (by norm_num : (97 : V) + 1064824 = 1064921)]
  set P : V := Exp.exp 1113 * Exp.exp (121*8791 : V) with hPdef
  have hP2 : (2 : V) ≤ P := by
    rw [hPdef, exp_mul_exp (by norm_num : (1113 : V) + 121*8791 = 1064824)]
    have := exp_monotone_le.mpr (show (1 : V) ≤ 1064824 by norm_num)
    have e1 : Exp.exp (1 : V) = 2 := by
      have := exp_succ (0 : V); rw [zero_add, exp_zero, mul_one] at this; exact this
    rwa [e1] at this
  have hBm : Exp.exp (1064921 : V) - 1 + 1 = Exp.exp 1064921 := tsub_add_cancel_of_le (one_le_exp _)
  set Bm : V := Exp.exp (1064921 : V) - 1 with hBmdef
  have hBm2 : (2 : V) ≤ Bm := by
    have h4 : (4 : V) ≤ Exp.exp 1064921 := by
      have := exp_monotone_le.mpr (show (2 : V) ≤ 1064921 by norm_num)
      rwa [show Exp.exp (2 : V) = 4 by
        rw [show (2 : V) = 0 + 1 + 1 by norm_num, exp_succ, exp_succ, exp_zero]; norm_num] at this
    by_contra hlt
    have : Bm + 1 < 3 := by
      have : Bm < 2 := not_le.mp hlt
      calc Bm + 1 < 2 + 1 := (add_lt_add_iff_right 1).mpr this
        _ = 3 := by norm_num
    rw [hBm] at this
    exact absurd (lt_of_le_of_lt h4 this) (by norm_num)
  -- the blocks
  have hblk := blk_bounds (s := s) hN hX
  have hcB : 2 * (c + 2) * Exp.exp (121*8791 : V) < Exp.exp 1064921 := by
    have h1 : c + 2 < Exp.exp 97 := by
      have : 4 * (c + 2) < 4 * Exp.exp 97 := calc
        4 * (c + 2) < 4 * c + 10 := by
            rw [show 4 * (c + 2) = 4 * c + 8 by ring]
            exact add_lt_add_of_le_of_lt le_rfl (by norm_num)
        _ ≤ 3 * Exp.exp 97 := hc2
        _ ≤ 4 * Exp.exp 97 := mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
      exact lt_of_mul_lt_mul_left this (by norm_num)
    calc 2 * (c + 2) * Exp.exp (121*8791 : V) < 2 * Exp.exp 97 * Exp.exp (121*8791 : V) :=
          mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h1 (by norm_num)) (exp_pos _)
      _ = Exp.exp (97+1+121*8791 : V) := by rw [exp_add, exp_succ]
      _ ≤ Exp.exp 1064921 := exp_monotone_le.mpr (by norm_num)
  have hblk_lt : ∀ j < M + 1, blk 1064921 (paramKernel rho : V) (M+1) s X j < Exp.exp 1064921 :=
    fun j hj => lt_trans (hblk j hj).2 hcB
  have hXB : 2 * Exp.exp (121*3296 : V) < Exp.exp 1064921 := by
    rw [← exp_succ]; exact exp_monotone.mpr (by norm_num)
  have hX_lt : ∀ j < M + 1, X j < Exp.exp 1064921 := fun j hj => lt_trans (hX j hj).2 hXB
  have hF1 : Q * (c * Exp.exp (121*8791 : V)) ≤ Fw 1064921 (paramKernel rho : V) (M+1) s X := by
    unfold Fw
    exact le_trans (mul_le_mul_of_nonneg_left (hblk M (lt_add_one M)).1 (Arithmetic.zero_le _))
      (bsum_top hblk_lt)
  have hF2 : Fw 1064921 (paramKernel rho : V) (M+1) s X ≤ (2 * (c + 2) * Exp.exp (121*8791 : V)) * R := by
    unfold Fw
    exact bsum_le_rep hcB (fun j hj => (hblk j hj).2.le)
  have hC1 : Q * Exp.exp (121*3296 : V) ≤ Cw 1064921 (M+1) X := by
    unfold Cw
    exact le_trans (mul_le_mul_of_nonneg_left (hX M (lt_add_one M)).1 (Arithmetic.zero_le _))
      (bsum_top hX_lt)
  have hC2 : Cw 1064921 (M+1) X ≤ (2 * Exp.exp (121*3296 : V)) * R := by
    unfold Cw
    exact bsum_le_rep hXB (fun j hj => (hX j hj).2.le)
  have hV : 2 * Exp.exp (121*3296 : V) * Exp.exp 666104 = Exp.exp 1064921 := by
    rw [mul_assoc, exp_mul_exp (by norm_num : (121*3296 : V) + 666104 = 1064920), ← exp_succ]
    norm_num
  have hrep' : Exp.exp 1064921 * Q = Bm * R + 1 := hrep.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Exp.exp 1064921 * Q = Exp.exp 97 * P * Q := by rw [← hP]
      _ ≤ (2 * c) * P * Q := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc1 (Arithmetic.zero_le _)) (Arithmetic.zero_le _)
      _ = 2 * (Exp.exp 1113 * (Q * (c * Exp.exp (121*8791 : V)))) := by rw [hPdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF1 (Arithmetic.zero_le _))
          (Arithmetic.zero_le _)
  · have hA : (4 * c + 8) * P * R + 2 * P * R ≤ 3 * Bm * R + 3 * R := calc
        (4 * c + 8) * P * R + 2 * P * R = (4 * c + 10) * P * R := by ring
        _ ≤ (3 * Exp.exp 97) * P * R := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc2 (Arithmetic.zero_le _)) (Arithmetic.zero_le _)
        _ = 3 * (Bm + 1) * R := by rw [hBm, ← hP, hPdef]; ring
        _ = 3 * Bm * R + 3 * R := by ring
    have h3R : 3 * R ≤ 2 * P * R := by
      apply mul_le_mul_of_nonneg_right _ (Arithmetic.zero_le _)
      calc (3 : V) ≤ 4 := by norm_num
        _ = 2 * 2 := by norm_num
        _ ≤ 2 * P := mul_le_mul_of_nonneg_left hP2 (by norm_num)
    have hB : (4 * c + 8) * P * R ≤ 3 * Bm * R := by
      have : (4 * c + 8) * P * R + 2 * P * R ≤ 3 * Bm * R + 2 * P * R :=
        le_trans hA (add_le_add le_rfl h3R)
      exact le_of_add_le_add_right this
    calc 2 * (Exp.exp 1113 * Fw 1064921 (paramKernel rho : V) (M+1) s X) ≤
          2 * (Exp.exp 1113 * ((2 * (c + 2) * Exp.exp (121*8791 : V)) * R)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF2 (Arithmetic.zero_le _))
            (Arithmetic.zero_le _)
      _ = (4 * c + 8) * P * R := by rw [hPdef]; ring
      _ ≤ 3 * Bm * R := hB
      _ ≤ 3 * Bm * R + 3 := le_add_of_nonneg_right (Arithmetic.zero_le _)
      _ = 3 * (Exp.exp 1064921 * Q) := by rw [hrep']; ring
  · calc Exp.exp 1064921 * Q = 2 * (Q * Exp.exp (121*3296 : V) * Exp.exp 666104) := by
          rw [← hV]; ring
      _ ≤ 2 * (Cw 1064921 (M+1) X * Exp.exp 666104) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hC1 (Arithmetic.zero_le _)) (Arithmetic.zero_le _)
  · have h2R : 2 * R ≤ Bm * R := mul_le_mul_of_nonneg_right hBm2 (Arithmetic.zero_le _)
    calc 2 * (Cw 1064921 (M+1) X * Exp.exp 666104) ≤
          2 * ((2 * Exp.exp (121*3296 : V)) * R * Exp.exp 666104) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC2 (Arithmetic.zero_le _))
            (Arithmetic.zero_le _)
      _ = 2 * (Bm + 1) * R := by rw [hBm, ← hV]; ring
      _ = 2 * Bm * R + 2 * R := by ring
      _ ≤ 2 * Bm * R + Bm * R := add_le_add le_rfl h2R
      _ ≤ 3 * Bm * R + 3 := by
          rw [show 2 * Bm * R + Bm * R = 3 * Bm * R by ring]
          exact le_add_of_nonneg_right (Arithmetic.zero_le _)
      _ = 3 * (Exp.exp 1064921 * Q) := by rw [hrep']; ring

end Cones

#print axioms lower_model
#print axioms cell_lower
#print axioms cells_of_word
#print axioms blk_bounds
#print axioms bsum_top
#print axioms bsum_le_rep
#print axioms cones

end DiophantineConsistency.P138Cone
