import GowersSzemeredi.Proofs16MilicevicColumns
import GowersSzemeredi.Proofs16DenseRowExtraction

/-! Dense columns of a bihomomorphism contain uniformly dense Freiman
8-homomorphism subsets, with explicit density parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnOf {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) (x : ZMod N) : Finset (ZMod N) :=
  Finset.univ.filter fun y => (x, y) ∈ A

theorem rowOf_swap_eq_columnOf {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) (x : ZMod N) :
    rowOf (A.image Prod.swap) x = columnOf A x := by
  ext y
  simp only [rowOf, columnOf, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    have heq' := congrArg Prod.swap heq
    change p = (x, y) at heq'
    simpa only [heq'] using hp
  · intro h
    exact Finset.mem_image.mpr ⟨(x, y), h, rfl⟩

def columnEightDensity (alpha : Real) : Real :=
  (2 : Real)^(-(1882 : Real)) * ((alpha / 2)^4)^1164

theorem columnEightDensity_pos {alpha : Real} (ha : 0 < alpha) : 0 < columnEightDensity alpha := by
  unfold columnEightDensity
  positivity

/-- Uniformly dense order-eight subcolumns, starting only from global
density and the original Freiman bihomomorphism. -/
theorem dense_column_eight_family {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0}) :
    ∃ (X : Finset (ZMod N)) (B : ZMod N → Finset (ZMod N)),
      (alpha / (2 - alpha)) * N ≤ X.card ∧
      ∀ x ∈ X, B x ⊆ columnOf A x ∧ columnEightDensity alpha * N ≤ (B x).card ∧
        FreimanHom 8 (B x) (fun y => phi (x, y)) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hswap : (A.image Prod.swap).card = A.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.swap h)
  obtain ⟨X, hX, hcols⟩ := exists_dense_rows (A.image Prod.swap) ha ha1 (by rwa [hswap])
  simp only [rowOf_swap_eq_columnOf] at hcols
  have hex : ∀ x ∈ X, ∃ B : Finset (ZMod N), B ⊆ columnOf A x ∧
      columnEightDensity alpha * N ≤ B.card ∧ FreimanHom 8 B (fun y => phi (x, y)) := by
    intro x hx
    let mu : Real := (columnOf A x).card / N
    have hmu : 0 < mu := (by linarith : (0 : Real) < alpha / 2).trans_le (hcols x hx)
    have hcard : ((columnOf A x).card : Real) = mu * N := (div_mul_cancel₀ _ hN.ne').symm
    have hf : FreimanHom 2 (columnOf A x) (fun y => phi (x, y)) := by
      rw [FreimanHom, isAddFreimanHom_two]
      refine ⟨Set.mapsTo_univ _ _, ?_⟩
      intro a ha b hb c hc d hd heq
      have h := Set.mem_singleton_iff.mp (hphi.2 x a b c d heq
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
        (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hd).2)
      linear_combination h
    obtain ⟨B, hB, hBcard, hB8, _⟩ := column_freiman_bohr (columnOf A x) (fun y => phi (x, y)) hf hmu hcard
    refine ⟨B, hB, ?_, hB8⟩
    apply le_trans _ hBcard
    unfold columnEightDensity
    gcongr
    exact hcols x hx
  choose! B hB using hex
  exact ⟨X, B, hX, hB⟩

end LeanProofs.GowersSzemeredi
