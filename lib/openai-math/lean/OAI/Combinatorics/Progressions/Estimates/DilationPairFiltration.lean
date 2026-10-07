import Mathlib.Algebra.Lie.Prod
import OAI.Combinatorics.Progressions.Geometry.DilationPairCoordinates
import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairLayer (q : ℚ) (n : ℕ) : Submodule ℚ (L × L) :=
  scaledPairLayer (F.layer n) (F.layer (n + 1)) (q ^ n)

@[simp] theorem mem_dilationPairLayer (q : ℚ) (n : ℕ) (x : L × L) :
    x ∈ F.dilationPairLayer q n ↔
      x.1 ∈ F.layer n ∧ x.2 ∈ F.layer n ∧ x.1 - q ^ n • x.2 ∈ F.layer (n + 1) := Iff.rfl

theorem dilationPairLayer_antitone (q : ℚ) : Antitone (F.dilationPairLayer q) := by
  intro i j hij x hx
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact hx
  refine ⟨F.antitone hij hx.1, F.antitone hij hx.2.1, ?_⟩
  change x.1 - q ^ i • x.2 ∈ F.layer (i + 1)
  have hdiff : x.1 - q ^ i • x.2 = (x.1 - q ^ j • x.2) + (q ^ j - q ^ i) • x.2 := by
    rw [sub_smul]
    abel
  rw [hdiff]
  exact (F.layer (i + 1)).add_mem
    (F.antitone (Nat.add_le_add_right hij 1) hx.2.2)
    ((F.layer (i + 1)).smul_mem _ (F.antitone (Nat.succ_le_of_lt hlt) hx.2.1))

theorem dilationPairLayer_lie_mem (q : ℚ) {i j : ℕ} {x y : L × L}
    (hx : x ∈ F.dilationPairLayer q i) (hy : y ∈ F.dilationPairLayer q j) :
    ⁅x, y⁆ ∈ F.dilationPairLayer q (i + j) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - q ^ (i + j) • ⁅x.2, y.2⁆ ∈ F.layer (i + j + 1)
  have hdiff : ⁅x.1, y.1⁆ - q ^ (i + j) • ⁅x.2, y.2⁆ =
      ⁅x.1 - q ^ i • x.2, y.1⁆ + q ^ i • ⁅x.2, y.1 - q ^ j • y.2⁆ := by
    simp only [sub_lie, lie_sub, smul_lie, lie_smul, smul_sub, smul_smul, pow_add]
    abel
  rw [hdiff]
  exact (F.layer (i + j + 1)).add_mem
    (by simpa only [scaledPairDifference_apply, Nat.add_right_comm i 1 j] using F.lie_mem hx.2.2 hy.1)
    ((F.layer (i + j + 1)).smul_mem _
      (by simpa only [scaledPairDifference_apply, Nat.add_assoc] using F.lie_mem hx.2.1 hy.2.2))

theorem dilationPairLayer_terminal (q : ℚ) : F.dilationPairLayer q (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Prod.ext
  · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.1)
  · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.2.1)

theorem dilationPairLayer_top_relation (q : ℚ) {x : L × L}
    (hx : x ∈ F.dilationPairLayer q s) : x.1 = q ^ s • x.2 := by
  have h : x.1 - q ^ s • x.2 ∈ F.layer (s + 1) := hx.2.2
  rw [F.terminal, Submodule.mem_bot, sub_eq_zero] at h
  exact h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairSubalgebra (q : ℚ) : LieSubalgebra ℚ (L × L) :=
  { F.dilationPairLayer q 1 with
    lie_mem' := fun hx hy => F.dilationPairLayer_antitone q (by decide : 1 ≤ 1 + 1)
      (F.dilationPairLayer_lie_mem q hx hy) }

@[simp] theorem mem_dilationPairSubalgebra (q : ℚ) (x : L × L) :
    x ∈ F.dilationPairSubalgebra q ↔ x.1 - q • x.2 ∈ F.layer 2 := by
  change x ∈ F.dilationPairLayer q 1 ↔ _
  simp only [mem_dilationPairLayer, F.one_eq_top, Submodule.mem_top, pow_one, true_and]

def dilationPairFiltration (q : ℚ) : NilpotentLieFiltration (F.dilationPairSubalgebra q) s where
  layer n := (F.dilationPairLayer q n).comap (F.dilationPairSubalgebra q).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.dilationPairLayer_antitone q h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.dilationPairLayer_lie_mem q hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × L)
    have h : x.val ∈ F.dilationPairLayer q (s + 1) := hx
    simpa only [F.dilationPairLayer_terminal, Submodule.mem_bot] using h

@[simp] theorem mem_dilationPairFiltration_layer (q : ℚ) (n : ℕ)
    (x : F.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairFiltration q).layer n ↔ x.val ∈ F.dilationPairLayer q n := Iff.rfl

def dilationPairFirst (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp (F.dilationPairSubalgebra q).incl

def dilationPairSecond (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp (F.dilationPairSubalgebra q).incl

theorem dilationPairTop_relation (q : ℚ) {x : F.dilationPairSubalgebra q}
    (hx : x ∈ (F.dilationPairFiltration q).layer s) :
    F.dilationPairFirst q x = q ^ s • F.dilationPairSecond q x :=
  F.dilationPairLayer_top_relation q hx

def dilationPairLayerEquiv (q : ℚ) (n : ℕ) :
    (F.layer (n + 1) × F.layer n) ≃ₗ[ℚ] F.dilationPairLayer q n :=
  scaledPairLayerEquiv (F.layer n) (F.layer (n + 1)) (F.antitone (Nat.le_succ n)) (q ^ n)

def dilationPairFiltrationLayerEquiv (q : ℚ) (n : ℕ) (hn : 1 ≤ n) :
    (F.dilationPairFiltration q).layer n ≃ₗ[ℚ] F.dilationPairLayer q n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.dilationPairLayer_antitone q hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
