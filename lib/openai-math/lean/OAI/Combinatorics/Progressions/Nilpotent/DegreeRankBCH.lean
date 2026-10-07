import OAI.Combinatorics.Progressions.Polynomial.DegreeRankSunflower

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def layerIdeal (d i : ℕ) : LieIdeal ℚ L :=
  { F.layer d i with
    lie_mem := by
      intro x y hy
      have hx : x ∈ F.layer 1 0 := by simp only [F.one_eq_top, Submodule.mem_top]
      exact F.lex_antitone (Or.inl (show d < 1 + d by omega)) (F.lie_mem hx hy) }

@[simp] theorem mem_layerIdeal (d i : ℕ) (x : L) :
    x ∈ F.layerIdeal d i ↔ x ∈ F.layer d i := Iff.rfl

abbrev Group := F.associatedDegree.Group

def subgroup (d i : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal d i).toLieSubalgebra

@[simp] theorem mem_subgroup (d i : ℕ) (x : F.Group) :
    x ∈ F.subgroup d i ↔ x.coord ∈ F.layer d i := Iff.rfl

theorem subgroup_normal (d i : ℕ) : (F.subgroup d i).Normal :=
  NilpotentLieBCHGroup.subgroup_ideal_normal (F.layerIdeal d i)

theorem subgroup_lex_antitone {d e i j : ℕ} (h : d < e ∨ d = e ∧ i ≤ j) :
    F.subgroup e j ≤ F.subgroup d i := fun _ hx => F.lex_antitone h hx

theorem subgroup_zero (d : ℕ) : F.subgroup d 0 = F.associatedDegree.subgroup d := by
  ext x
  rfl

theorem subgroup_one (d : ℕ) : F.subgroup d 1 = F.associatedDegree.subgroup d := by
  ext x
  change x.coord ∈ F.layer d 1 ↔ x.coord ∈ F.layer d 0
  rw [F.rank_zero_eq_one]

theorem subgroup_le_associatedDegree (d i : ℕ) : F.subgroup d i ≤ F.associatedDegree.subgroup d :=
  fun _ hx => F.layer_le_associatedDegree d i hx

theorem subgroup_commutator_mem {d e i j : ℕ} {x y : F.Group}
    (hx : x ∈ F.subgroup d i) (hy : y ∈ F.subgroup e j) :
    x * y * x⁻¹ * y⁻¹ ∈ F.subgroup (d + e) (i + j) :=
  NilpotentLieBCHGroup.commutator_mem_ideal (F.layerIdeal (d + e) (i + j)) x y (F.lie_mem hx hy)

theorem subgroup_eq_bot_of_past_top {d i : ℕ} (h : s < d ∨ s = d ∧ r < i) :
    F.subgroup d i = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply NilpotentLieBCHGroup.ext
  change x.coord = 0
  have hm := (F.mem_subgroup d i x).mp hx
  simpa only [F.layer_eq_bot_of_past_top h, Submodule.mem_bot] using hm

theorem subgroup_terminal : F.subgroup s (r + 1) = ⊥ :=
  F.subgroup_eq_bot_of_past_top (Or.inr ⟨rfl, by omega⟩)

end Erdos3.DegreeRankLieFiltration

end

end OAI
