import OAI.Combinatorics.Progressions.Nilpotent.FreeWeightedNilpotentLieAlgebra

namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : X → ℕ) (f : X → L)
  (hf : ∀ x, f x ∈ F.layer (w x))

include hf in
theorem FreeNilpotentLieAlgebra.lift_weightedLayer {d : ℕ} {x : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ FreeNilpotentLieAlgebra.weightedLayer X s w d) :
    FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot x ∈ F.layer d :=
  weightedLieUpperSpan_le_comap F (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (FreeNilpotentLieAlgebra.of X s) w
    (fun i => by rw [FreeNilpotentLieAlgebra.lift_of]; exact hf i) d hx

namespace FreeWeightedNilpotentLieAlgebra

noncomputable def lift : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend (FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1))
    (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (fun x hx => by
      have h := FreeNilpotentLieAlgebra.lift_weightedLayer F w f hf hx
      simpa only [F.terminal, Submodule.mem_bot] using h)

theorem lift_mk (x : FreeNilpotentLieAlgebra X s) :
    lift F w f hf (mk X s w x) = FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot x := rfl

@[simp] theorem lift_of (x : X) : lift F w f hf (of X s w x) = f x :=
  FreeNilpotentLieAlgebra.lift_of f F.lowerCentralSeries_eq_bot x

theorem lift_mem_layer (hw : ∀ i, 0 < w i) {d : ℕ} {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (filtration X s w hw).layer d) : lift F w f hf x ∈ F.layer d := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact FreeNilpotentLieAlgebra.lift_weightedLayer F w f hf ha

theorem hom_ext {φ ψ : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ L}
    (h : ∀ x, φ (of X s w x) = ψ (of X s w x)) : φ = ψ := by
  have heq : φ.comp (mk X s w) = ψ.comp (mk X s w) := FreeNilpotentLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective X s w x
  exact LieHom.congr_fun heq a

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

open Module
open scoped Matrix

variable {X ι κ L : Type*} [Fintype X] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem lift_basis_matrix_logHeight
    (F : NilpotentLieFiltration L s) (w : X → ℕ) (f : X → L)
    (hf : ∀ x, f x ∈ F.layer (w x))
    (e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (he : ∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s)
    (b : Basis κ ℚ (FreeWeightedNilpotentLieAlgebra X s w)) (t : Basis ι ℚ L)
    (S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) κ ℚ)
    (hS : LinearMap.toMatrix e b (mk X s w).toLinearMap * S = 1)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ p)
    (ht : (Fintype.card ι : ℝ) ≤ p)
    (hSH : ∀ i j, rationalLogHeight (S i j) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants t i j k) ≤ p)
    (hg : ∀ x i, rationalLogHeight (t.repr (f x) i) ≤ p) (i : ι) (j : κ) :
    rationalLogHeight (LinearMap.toMatrix b t (lift F w f hf).toLinearMap i j) ≤
      ((p + 3) ^ (6 * s + 2) + p + 2) ^ 4 := by
  classical
  let R := (p + 3) ^ (6 * s + 2) + p
  have hpR : p ≤ R := le_add_of_nonneg_left (by positivity)
  have hpowR : (p + 3) ^ (6 * s + 2) ≤ R := le_add_of_nonneg_right hp
  let σ := Matrix.toLin b e S
  have hσ : mk X s w (σ (b j)) = b j := basisMatrix_section e b (mk X s w).toLinearMap S hS (b j)
  have hcoord (k) : e.repr (σ (b j)) k = S k j := by
    simpa only [σ, LinearMap.toMatrix_toLin] using
      (LinearMap.toMatrix_apply b e (Matrix.toLin b e S) k j).symm
  rw [LinearMap.toMatrix_apply]
  have heval : lift F w f hf (b j) =
      FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot (σ (b j)) := by
    calc
      _ = lift F w f hf (mk X s w (σ (b j))) := congrArg (lift F w f hf) hσ.symm
      _ = _ := lift_mk F w f hf (σ (b j))
  change rationalLogHeight (t.repr (lift F w f hf (b j)) i) ≤ (R + 2) ^ 4
  rw [heval]
  apply linearMap_coordinate_logHeight e t
    (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot).toLinearMap (hp.trans hpR)
    (by simpa only [Fintype.card_fin] using hn.trans hpR) ?_ (σ (b j)) ?_ i
  · intro u v
    have h := FreeNilpotentLieAlgebra.lift_basis_matrix_logHeight t f
      F.lowerCentralSeries_eq_bot e he hp ht hc hg v u
    apply le_trans _ hpowR
    simpa only [LinearMap.toMatrix_apply] using h
  · intro k
    rw [hcoord]
    exact (hSH k j).trans hpR

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

end OAI
