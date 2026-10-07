import GowersSzemeredi.Proofs16AlphabetLargeModulus

/-! Embed a finite uniform alphabet into the cyclic field without changing
symbol counts. The balance conclusion is quantified over all field values. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem alphabet_natCast_injective {N R : Nat} [NeZero N] (hRN : R ≤ N) :
    Function.Injective (fun c : Fin R => (c.val : ZMod N)) := by
  intro c d h
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt (c.isLt.trans_le hRN),
    ZMod.val_natCast_of_lt (d.isLt.trans_le hRN)] using hv

theorem balanced_word_embed {N R : Nat} [NeZero N] (hRN : R ≤ N)
    (w : ZMod N → Fin R) (L beta : Real) (hbeta : 0 ≤ beta)
    (hw : ∀ P : ModAP N, P.IsProper → L ≤ P.length →
      ∀ c : Fin R, ((P.carrier.filter (fun x => w x = c)).card : Real) ≤ beta * P.length) :
    ∃ S : Finset (ZMod N), ∃ f : ZMod N → ZMod N,
      S.card = R ∧ (∀ x, f x ∈ S) ∧
      ∀ P : ModAP N, P.IsProper → L ≤ P.length →
        ∀ c : ZMod N, ((P.carrier.filter (fun x => f x = c)).card : Real) ≤ beta * P.length := by
  classical
  let e : Fin R → ZMod N := fun c => (c.val : ZMod N)
  let S := Finset.univ.image e
  let f : ZMod N → ZMod N := fun x => e (w x)
  have he : Function.Injective e := alphabet_natCast_injective hRN
  have hS : S.card = R := by simp only [S, Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin]
  have hf (x : ZMod N) : f x ∈ S := Finset.mem_image.mpr ⟨w x, Finset.mem_univ _, rfl⟩
  refine ⟨S, f, hS, hf, ?_⟩
  intro P hP hPL c
  by_cases hc : c ∈ S
  · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hc
    have hfilter : P.carrier.filter (fun x => f x = e d) = P.carrier.filter (fun x => w x = d) := by
      ext x
      simp only [Finset.mem_filter, f, he.eq_iff]
    rw [hfilter]
    exact hw P hP hPL d
  · have hfilter : P.carrier.filter (fun x => f x = c) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have heq := (Finset.mem_filter.mp hx).2
      exact hc (heq ▸ hf x)
    rw [hfilter, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hbeta (Nat.cast_nonneg P.length)

theorem exists_balanced_field_word_large_N (R : Nat) (hR : 0 < R)
    {delta epsilon : Real} (hδ : 0 < delta) (hδone : delta ≤ 1) (hε : 0 < epsilon) :
    ∃ N₀ : Nat, ∀ (N : Nat) [NeZero N], N₀ ≤ N →
      ∃ S : Finset (ZMod N), ∃ f : ZMod N → ZMod N,
        S.card = R ∧ (∀ x, f x ∈ S) ∧
        ∀ P : ModAP N, P.IsProper → (N : Real) ^ delta ≤ P.length →
          ∀ c : ZMod N, ((P.carrier.filter (fun x => f x = c)).card : Real) ≤
            (1 / (R : Real) + epsilon) * P.length := by
  obtain ⟨N₀, hN₀⟩ := exists_balanced_progression_word_large_N R hR hδ hδone hε
  refine ⟨max N₀ R, fun N _ hN => ?_⟩
  obtain ⟨w, hw⟩ := hN₀ N ((le_max_left _ _).trans hN)
  exact balanced_word_embed ((le_max_right _ _).trans hN) w ((N : Real) ^ delta)
    (1 / (R : Real) + epsilon) (by positivity) hw

end LeanProofs.GowersSzemeredi
