import GowersSzemeredi.Proofs16LiftAllScales
import GowersSzemeredi.Proofs16CompressedCandidateBounds

/-! # Uniform finite candidate families for global affine lifting -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Reindex an arbitrary finite family and pad it with zero functions. -/
def padFiniteMultilinearFamily {N k : Nat} {C : Type*} [Fintype C]
    (mu : C → Point N k → ZMod N) (q : Nat) : Fin q → Point N k → ZMod N :=
  padMultilinearFamily (fun i => mu ((Fintype.equivFin C).symm i)) q

theorem padFiniteMultilinearFamily_isMultilinear {N k q : Nat} {C : Type*} [Fintype C]
    (mu : C → Point N k → ZMod N) (hmu : ∀ c, IsMultilinear (mu c)) :
    ∀ i, IsMultilinear (padFiniteMultilinearFamily mu q i) := by
  intro i
  exact padMultilinearFamily_isMultilinear _ (fun _ => hmu _) i

theorem padFiniteMultilinearFamily_covers {N k q : Nat} {C : Type*} [Fintype C]
    (mu : C → Point N k → ZMod N) (hq : Fintype.card C ≤ q)
    (x : Point N k) (y : ZMod N) (hy : ∃ c, y = mu c x) :
    ∃ i, y = padFiniteMultilinearFamily mu q i x := by
  apply padMultilinearFamily_covers _ hq x y
  obtain ⟨c, hc⟩ := hy
  exact ⟨(Fintype.equivFin C) c, by simpa using hc⟩

theorem section16_recovered_candidate_mono {r p q : Nat} (hpq : p ≤ q) :
    Fintype.card ((Fin r × Fin p) ⊕ (Fin r × Fin r × Fin p × Fin p)) ≤
      r * q + r * r * q * q := by
  rw [section16_recovered_candidate_count]
  gcongr

theorem section16_recovered_candidate_bound {r p : Nat} {b : ℝ} (hp : (p : ℝ) ≤ b) :
    ((r * p + r * r * p * p : Nat) : ℝ) ≤
      (r : ℝ) * b + (r : ℝ) * r * b * b := by
  have hb : 0 ≤ b := (Nat.cast_nonneg p).trans hp
  push_cast
  gcongr

end LeanProofs.GowersSzemeredi
