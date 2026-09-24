import Diophantine.Paper1980.GraphDecode100
import Diophantine.Paper1980.GridCompiled100

/-!
# A compiled graph ROM

`graph_path100` assumes the ROM inequalities `ROM100.Ok` and the port-grid layout
`Graph.PortGrid`.  This module builds, for every graph controller, one grid numeral that meets
both, so the decoded nondeterministic path is not vacuous.

The spacing is the graph's own, `B₀ = 3^sp`, which is at least `9` because `sp ≥ 2`.  The
table's block exponents are all below `bmark + bz`, so `K < hz` as for the deterministic
table.  The grid numeral marks the two port columns and one high column `sp · zonChoice`,
all multiples of the spacing; the high column makes the numeral exceed every bound of
`ROM100.Ok`.  Unlike the deterministic grid numeral it need not mark the target columns.

`graph_decoded_compiled100` is the payoff: for a graph controller under the terminal
convention, every positive solution of `Sys100` over its own ROM has the radix geometry, the
decoded-control bound, and a state field tracing a path of permitted edges from the entry
back to the entry, with the sign and zero fields carrying the labels.
-/

namespace Jones1980

open Ternary Finset

namespace Graph

variable (Gr : Graph)

theorem romS_pos : 0 < Gr.romS := by
  have hne : (range Gr.n).Nonempty := ⟨0, Finset.mem_range.2 (by have := Gr.two_le; omega)⟩
  exact Finset.sum_pos (fun i _ => by positivity) hne

theorem romK_pos : 0 < Gr.romK := by have := Gr.romK_mod; omega

/-- **`K < hz`.**  Every block exponent of the table is below `bmark + bz`. -/
theorem romK_lt_hz : Gr.romK < Gr.romhz := by
  have hsub : Gr.bexpSet.image (fun E => Gr.sp * E) ⊆ range (Gr.sp * (Gr.bmark + Gr.bz)) := by
    intro e he
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.1 he
    exact Finset.mem_range.2 (Nat.mul_lt_mul_of_pos_left (Gr.bexp_lt hE) Gr.sp_pos)
  calc Gr.romK = ∑ e ∈ Gr.bexpSet.image (fun E => Gr.sp * E), 3 ^ e := Gr.romK_eq_image
    _ ≤ ∑ e ∈ range (Gr.sp * (Gr.bmark + Gr.bz)), 3 ^ e :=
        Finset.sum_le_sum_of_subset hsub
    _ < 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) := Controller.sum_pow_lt _

/-- A bound wide enough for the fixed program. -/
def zonChoice : ℕ :=
  81 + 4 * Gr.romS + Gr.romg * (Gr.romI + 1) + (Gr.romK + Gr.romg) * (Gr.romS + 1)
    + 8 * (Gr.romhs + Gr.romhz)

/-- The columns the compiled grid numeral marks: both port columns and one high column. -/
def gridSet : Finset ℕ :=
  {Gr.sp * (Gr.bmark + Gr.bs), Gr.sp * (Gr.bmark + Gr.bz), Gr.sp * Gr.zonChoice}

/-- The compiled grid numeral. -/
def gridZon : ℕ := ∑ e ∈ Gr.gridSet, 3 ^ e

theorem zonChoice_lt_gridZon : Gr.zonChoice < Gr.gridZon := by
  have h1 : 3 ^ (Gr.sp * Gr.zonChoice) ≤ Gr.gridZon :=
    Finset.single_le_sum (f := fun e => 3 ^ e) (fun _ _ => Nat.zero_le _) (by simp [gridSet])
  have h2 : Gr.zonChoice < 3 ^ Gr.zonChoice := Ternary.lt_three_pow _
  have h3 : (3 : ℕ) ^ Gr.zonChoice ≤ 3 ^ (Gr.sp * Gr.zonChoice) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ Gr.sp_pos)
  omega

/-- **The compiled graph ROM meets the fixed grid inequalities.** -/
theorem rom_grid_ok : (Gr.rom Gr.gridZon (3 ^ Gr.sp)).Ok where
  B0_ge := by
    show 9 ≤ 3 ^ Gr.sp
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ Gr.sp := Nat.pow_le_pow_right (by norm_num) Gr.sp_ge
  Zon_ge := by
    have h2 := Gr.zonChoice_lt_gridZon
    show 81 ≤ Gr.gridZon
    unfold zonChoice at h2
    omega
  Zon_gt_S := by
    have h2 := Gr.zonChoice_lt_gridZon
    show 4 * Gr.romS < Gr.gridZon
    unfold zonChoice at h2
    omega
  Zon_gt_gI := by
    have h2 := Gr.zonChoice_lt_gridZon
    show Gr.romg * (Gr.romI + 1) < Gr.gridZon
    unfold zonChoice at h2
    omega
  Zon_gt_KgS := by
    have h2 := Gr.zonChoice_lt_gridZon
    show (Gr.romK + Gr.romg) * (Gr.romS + 1) < Gr.gridZon
    unfold zonChoice at h2
    omega
  S_pos := Gr.romS_pos
  I_pos := by show (0 : ℕ) < 3 ^ (Gr.sp * coord 0); positivity
  g_pow := ⟨Gr.sp * Gr.bmark, rfl⟩
  K_lt_hz := Gr.romK_lt_hz
  Zon_gt_ports := by
    have h2 := Gr.zonChoice_lt_gridZon
    show 8 * (Gr.romhs + Gr.romhz) < Gr.gridZon
    unfold zonChoice at h2
    omega
  K_pos := Gr.romK_pos

/-- **The compiled graph numeral has the port-grid layout.** -/
theorem rom_port_grid : Gr.PortGrid (Gr.rom Gr.gridZon (3 ^ Gr.sp)) where
  spacing := rfl
  bool_Zon := by
    show Bool3 (∑ e ∈ Gr.gridSet, 3 ^ e)
    exact Ternary.bool3_sum_pow _
  marks_sgn := by
    show dg (∑ e ∈ Gr.gridSet, 3 ^ e) (Gr.sp * (Gr.bmark + Gr.bs)) = 1
    rw [Ternary.dg_sum_pow, if_pos (by simp [gridSet])]
  marks_zreq := by
    show dg (∑ e ∈ Gr.gridSet, 3 ^ e) (Gr.sp * (Gr.bmark + Gr.bz)) = 1
    rw [Ternary.dg_sum_pow, if_pos (by simp [gridSet])]
  on_grid := fun p hp => by
    have hp' : dg (∑ e ∈ Gr.gridSet, 3 ^ e) p = 1 := hp
    have hmem : p ∈ Gr.gridSet := by
      by_contra hc
      rw [Ternary.dg_sum_pow, if_neg hc] at hp'
      omega
    simp only [gridSet, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl <;> exact Nat.mul_mod_right _ _

end Graph

/-- **The decoded path of a compiled graph controller.**  Under the terminal convention, every
positive solution of `Sys100` over a graph controller's own ROM has the radix geometry, the
decoded-control bound, and a state sequence from the entry along permitted edges whose last
state has an edge back to the entry; rows of the halved state, sign and zero fields are the
states and their labels.  Every hypothesis about the fixed ROM is supplied by the
compilation. -/
theorem graph_decoded_compiled100 {Gr : Graph}
    (hconv : ∀ ii, ii < Gr.n → Gr.adj ii 0 = true → Gr.zreq ii = true)
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (Gr.rom Gr.gridZon (3 ^ Gr.sp)) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a
      c d f h i j k o s w τ η ζ γ y) :
    ∃ e m u, Geometry100 H R q e m u ∧ 2 * q ≤ R * D ∧
      ∃ pc kp dd : ℕ, ∃ st : ℕ → ℕ, PC = 2 * pc ∧ Kp = 2 * kp ∧ D = 2 * dd ∧ st 0 = 0 ∧
        (∀ jj, jj < u → st jj < Gr.n ∧ row pc m jj = 3 ^ (Gr.sp * coord (st jj)) ∧
          row kp m jj = (if Gr.sgn (st jj) = true then 1 else 0) ∧
          row dd m jj = (if Gr.zreq (st jj) = true then 1 else 0)) ∧
        (∀ jj, jj + 1 < u → Gr.adj (st jj) (st (jj + 1)) = true) ∧
        Gr.adj (st (u - 1)) 0 = true := by
  have hOk := Gr.rom_grid_ok
  obtain ⟨e, m, u, hG⟩ := geometry100 hP hS hOk.Zon_ge hOk.B0_ge
  exact ⟨e, m, u, hG, graph_decode_bound100 hOk hP hS hG Gr.rom_port_grid hconv,
    graph_path100 hOk hP hS hG Gr.rom_port_grid⟩

end Jones1980
