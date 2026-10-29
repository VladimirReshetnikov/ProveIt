import DiophantineConsistency.ArithmeticWangPlane

/-! One machine step inside the walled strip of an internal marked word.

`RowInv` says that row `k` of the plane has seam walls at columns `lW, rW`, and
that between them it carries the north colours of the represented
configuration `run k` with some interior head column. From an operating
configuration the next row carries `run (k+1)`: the head tile writes, its
active-side receiver takes the next head colour, and every other interior tile
passes its bit. A finish tile anywhere inside is excluded by an internal
interval induction: it would force reset tiles across the whole seam-free
row above, hence a south colour438 at the operating head. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticWangRowStep
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWangTable ArithmeticWangPlane ArithmeticCantor
open ArithmeticMachineRun215 (run run_succ)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] ArithmeticWangPlane.pl ArithmeticWangPlane.adr
  ArithmeticMachineRun215.run ArithmeticWangPlane.Colored

/-- Row `k` encodes `run k` between the seam walls `lW < rW`. -/
def RowInv (a : V → V) (N s lW rW k : V) : Prop :=
  northC (pl a N s lW k) = 437 ∧ northC (pl a N s rW k) = 437 ∧
  first (run k) ≤ 215 ∧
  ∃ H < rW, lW < H ∧ ∀ X < rW, lW < X → Colored (northC (pl a N s X k)) (run k) H X

theorem one_le_of_lt' {x y : V} (hxy : x < y) : 1 ≤ y :=
  pos_iff_one_le.mp (lt_of_le_of_lt (Arithmetic.zero_le x) hxy)

section step
variable {a : V → V} [𝚺₁-Function₁ a] {N s : V} (h : MarkedWord a N s) {lW rW : V}
include h

/-- No finish tile inside the strip, by reset propagation along the row above. -/
theorem no_finish (k H : V) (hHl : lW < H) (hHr : H < rW)
    (hcol : ∀ X, lW < X → X < rW → northC (pl a N s X k) ≤ 433)
    (hsH : southC (pl a N s H k) ≤ 1) :
    ∀ X, lW < X → X < rW → southC (pl a N s X k) ≠ 438 := by
  intro X0 hl hr h438
  have ns : ∀ Y, lW < Y → Y < rW → northC (pl a N s Y (k + 1)) ≠ 437 := by
    intro Y hYl hYr h7
    rw [← pl_south h, ← seam_iff (pl_lt h _ _)] at h7
    have := hcol Y hYl hYr
    rw [h7] at this
    exact absurd this (by norm_num)
  have right : ∀ m, X0 + m < rW → northC (pl a N s (X0 + m) (k + 1)) = 438 := by
    intro m
    induction m using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro _; rw [add_zero, ← pl_south h]; exact h438
    case succ m ih =>
      intro hm
      have hm' : X0 + m < rW := lt_trans (by rw [← add_assoc]; exact lt_add_one _) hm
      have he := (north_438 (pl_lt h _ _) (ih hm')).2
      rw [pl_east h] at he
      rw [← add_assoc] at hm ⊢
      rcases west_one (pl_lt h _ _) he with h8 | h7
      · exact h8
      · exact absurd h7 (ns _ (lt_of_lt_of_le hl (by
          rw [add_assoc]; exact le_add_self' _ _)) hm)
  have left : ∀ m, m < X0 - lW → northC (pl a N s (X0 - m) (k + 1)) = 438 := by
    intro m
    induction m using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro _; rw [tsub_zero, ← pl_south h]; exact h438
    case succ m ih =>
      intro hm
      have hm' : m < X0 - lW := lt_trans (lt_add_one m) hm
      have hw := (north_438 (pl_lt h _ _) (ih hm')).1
      have hle : m + 1 ≤ X0 := le_trans hm.le tsub_le_self
      have hY : X0 - (m + 1) + 1 = X0 - m := by
        rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hle)]
      rw [← hY, ← pl_east h] at hw
      rcases east_one (pl_lt h _ _) hw with h8 | h7
      · exact h8
      · refine absurd h7 (ns _ ?_ (lt_of_le_of_lt tsub_le_self hr))
        exact lt_tsub_iff_right.mpr (lt_tsub_iff_left.mp hm)
  have hH : northC (pl a N s H (k + 1)) = 438 := by
    rcases le_or_gt X0 H with hle | hlt
    · simpa only [add_tsub_cancel_of_le hle] using
        right (H - X0) (by rwa [add_tsub_cancel_of_le hle])
    · simpa only [tsub_tsub_cancel_of_le hlt.le] using
        left (X0 - H) (tsub_lt_tsub_left_of_le hlt.le hHl)
  rw [pl_south h, hH] at hsH
  exact absurd hsH (by norm_num)

/-- One represented machine step from an operating configuration. -/
theorem row_step (k : V) (hinv : RowInv a N s lW rW k) (hlive : first (run k) ≠ 0) :
    RowInv a N s lW rW (k + 1) := by
  obtain ⟨hwl, hwr, hst, H, hHr, hHl, hcol⟩ := hinv
  set c := run k with hc
  have col : ∀ X, lW < X → X < rW → northC (pl a N s X k) = colorV c H X :=
    fun X hXl hXr => (colored_iff _ _ _ _).mp (hcol X hXr hXl)
  have colle : ∀ X, lW < X → X < rW → northC (pl a N s X k) ≤ 433 :=
    fun X hXl hXr => (col X hXl hXr).trans_le (colorV_le hst)
  have plain : ∀ X, lW < X → X < rW → X ≠ H → northC (pl a N s X k) = tb (first (second c)) (second (second c)) H X := by
    intro X hXl hXr hne; rw [col X hXl hXr]; simp [colorV, hne]
  have plain_le : ∀ X, lW < X → X < rW → X ≠ H → northC (pl a N s X k) ≤ 1 := by
    intro X hXl hXr hne; rw [plain X hXl hXr hne]; exact tb_le _ _ _ _
  have hb : (second (second c)) % 2 ≤ 1 := le_one_iff_eq_zero_or_one.mpr (mod_two _)
  have hn : northC (pl a N s H k) = 2 * first c + (second (second c)) % 2 := by
    rw [col H hHl hHr]; simp [colorV, hcV, hlive]
  obtain ⟨st', d, w, hst', hd, hw, hA, hsH, hR, hL⟩ :=
    head_step (pl_lt h H k) hlive hst hb hn
  have hstep := step_apply c st' d w hd hw hA
  have hrun : run (k + 1) = ArithmeticMachineStep215.stepValue c := run_succ k
  have nf := no_finish h k H hHl hHr colle (by rw [hsH]; exact hw)
  have wl : northC (pl a N s lW (k + 1)) = 437 := by
    rw [← pl_south h]; exact (seam_iff (pl_lt h _ _)).mp hwl
  have wr : northC (pl a N s rW (k + 1)) = 437 := by
    rw [← pl_south h]; exact (seam_iff (pl_lt h _ _)).mp hwr
  -- every other interior tile passes its bit
  have far : ∀ X, lW < X → X < rW → X ≠ H → (d = 1 → X ≠ H + 1) → (d = 0 → X + 1 ≠ H) →
      southC (pl a N s X k) = northC (pl a N s X k) := by
    intro X hXl hXr hXH h1 h0
    have hp := plain_le X hXl hXr hXH
    obtain ⟨hws, hes⟩ := plain_sides (pl_lt h _ _) hp
    have hw0 : westC (pl a N s X k) = 0 := by
      obtain ⟨Y, rfl⟩ : ∃ Y, X = Y + 1 :=
        ⟨X - 1, (tsub_add_cancel_of_le (one_le_of_lt' hXl)).symm⟩
      have he := pl_east h Y k
      rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hXl) with hY | hY
      · have hb2 := (seam_sides (pl_lt h _ _) hwl).2
        rw [hY, he] at hb2
        rcases hws with e | ⟨e6, _⟩
        · exact e
        · exact absurd (le_trans e6 hb2) (by norm_num)
      · by_cases hYH : Y = H
        · subst hYH
          rcases bit_cases hd with hd0 | hd1
          · rw [← he, (hL hd0).1]
          · exact absurd rfl (h1 hd1)
        · have hpY := plain_le Y hY (lt_trans (lt_add_one Y) hXr) hYH
          obtain ⟨_, hesY⟩ := plain_sides (pl_lt h _ _) hpY
          rcases hws with e | ⟨e6, e205⟩
          · exact e
          rcases hesY with eY | ⟨eY205, _⟩
          · rw [← he, eY]
          · rw [he] at eY205; exact absurd e205 (not_lt.mpr eY205)
    have he0 : eastC (pl a N s X k) = 0 := by
      have he := pl_east h X k
      rcases eq_or_lt_of_le (lt_iff_succ_le.mp hXr) with hZ | hZ
      · have hb4 := (seam_sides (pl_lt h _ _) hwr).1
        rw [← hZ, ← he] at hb4
        rcases hes with e | ⟨e205, _⟩
        · exact e
        · exact absurd (le_trans e205 hb4) (by norm_num)
      · by_cases hZH : X + 1 = H
        · rcases bit_cases hd with hd0 | hd1
          · exact absurd hZH (h0 hd0)
          · rw [he, hZH, (hR hd1).1]
        · have hZl : lW < X + 1 := lt_trans hXl (lt_add_one X)
          have hpZ := plain_le (X + 1) hZl hZ hZH
          obtain ⟨hwsZ, _⟩ := plain_sides (pl_lt h _ _) hpZ
          rcases hes with e | ⟨e205, _⟩
          · exact e
          rcases hwsZ with eZ | ⟨_, eZ205⟩
          · rw [he, eZ]
          · rw [← he] at eZ205; exact absurd e205 (not_le.mpr eZ205)
    rcases plain_pass (pl_lt h _ _) hp hw0 he0 with e | e
    · exact e
    · exact absurd e (nf X hXl hXr)
  refine ⟨wl, wr, ?_, ?_⟩
  · rw [hrun, hstep]; split <;> simpa using hst'
  rcases bit_cases hd with hd0 | hd1
  · -- left move
    obtain ⟨G, rfl⟩ : ∃ G, H = G + 1 := ⟨H - 1, (tsub_add_cancel_of_le (one_le_of_lt' hHl)).symm⟩
    have hGl : lW < G := by
      rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hHl) with e | e
      · exfalso
        have hb2 := (seam_sides (pl_lt h _ _) hwl).2
        rw [e, pl_east h] at hb2
        exact absurd (le_trans (hL hd0).2.1 hb2) (by norm_num)
      · exact e
    refine ⟨G, lt_trans (lt_add_one G) hHr, hGl, ?_⟩
    intro X hXr hXl
    rw [colored_iff, ← pl_south h, hrun, hstep, if_pos hd0]
    simp only [colorV, first_cantor, second_cantor]
    have hm : (first (second c)) % 2 ≤ 1 := le_one_iff_eq_zero_or_one.mpr (mod_two _)
    by_cases hXG : X = G
    · subst hXG
      rw [if_pos rfl, push_mod _ _ hm]
      have hXH : X ≠ X + 1 := ne_of_lt (lt_add_one X)
      rw [(hL hd0).2.2 _ (pl_lt h _ _) (plain_le X hXl hXr hXH) (pl_east h X k),
        plain X hXl hXr hXH]
      congr 1
      simp [tb, fbit_zero_eq]
    · rw [if_neg hXG]
      by_cases hXH : X = G + 1
      · subst hXH; rw [tb_left_old _ _ _ _ hw, hsH]
      · rw [tb_left _ _ _ _ _ hw hXH,
          far X hXl hXr hXH (fun hd1 => absurd (hd0.symm.trans hd1) zero_ne_one)
            (fun _ he => hXG (add_right_cancel he)),
          plain X hXl hXr hXH]
  · -- right move
    have hHr' : H + 1 < rW := by
      rcases eq_or_lt_of_le (lt_iff_succ_le.mp hHr) with e | e
      · exfalso
        have hb4 := (seam_sides (pl_lt h _ _) hwr).1
        rw [← e, ← pl_east h] at hb4
        exact absurd (le_trans (hR hd1).2.1 hb4) (by norm_num)
      · exact e
    refine ⟨H + 1, hHr', lt_trans hHl (lt_add_one H), ?_⟩
    intro X hXr hXl
    have hd0 : d ≠ 0 := by rw [hd1]; exact _root_.one_ne_zero
    rw [colored_iff, ← pl_south h, hrun, hstep, if_neg hd0]
    simp only [colorV, first_cantor, second_cantor]
    by_cases hX1 : X = H + 1
    · subst hX1
      rw [if_pos rfl]
      have hXH : H + 1 ≠ H := ne_of_gt (lt_add_one H)
      rw [(hR hd1).2.2 _ (pl_lt h _ _) (plain_le _ hXl hXr hXH) (pl_east h H k).symm,
        plain _ hXl hXr hXH]
      congr 1
      have e1 : fbit (second (second c)) 1 = (second (second c)) / 2 % 2 := by
        rw [show (1 : V) = 0 + 1 by simp, fbit_succ, fbit_zero_eq]
      simp only [tb, le_add_self' H 1, if_true, add_tsub_cancel_left, e1]
    · rw [if_neg hX1]
      by_cases hXH : X = H
      · subst hXH; rw [tb_right_old _ _ _ _ hw, hsH]
      · rw [tb_right _ _ _ _ _ hw hXH,
          far X hXl hXr hXH (fun _ => hX1) (fun hd0' => absurd (hd0'.symm.trans hd1) zero_ne_one),
          plain X hXl hXr hXH]

end step

end DiophantineConsistency.ArithmeticWangRowStep
