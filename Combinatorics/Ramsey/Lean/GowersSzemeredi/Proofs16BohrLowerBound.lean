import GowersSzemeredi.Proofs16BohrDoubling
import GowersSzemeredi.Proofs05SimultaneousDirichlet

/-! The Bohr-set lower bound `N ≤ M^|K| · |B(K;ρ)|` for `M ≥ 1/ρ`.

Bucket all residues by their Dirichlet-cell signature over `K`, giving
`M^|K|` cells. Two points of the same cell differ by less than `N/M ≤ ρN`
in every coordinate (`dirichletCell_close`). So each cell embeds into
`B(K;ρ)` by translation, and the cells cover all `N` residues.

With `bohr_card_le_four_pow` this bounds `|B(K;ρ)| / |B(K;ρ/2)|` and,
summed over fibres, the size ratios of bilinear Bohr varieties. That gives
the regular step for varieties needed by the packing in research notes
J.2. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **The Bohr-set lower bound.** -/
theorem bohr_card_lower {N : Nat} [NeZero N] (K : Finset (ZMod N)) {ρ : Real} (M : Nat) [NeZero M]
    (hM : 1 ≤ ρ * M) : N ≤ M ^ K.card * (bohr K ρ).card := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMR : (0 : Real) < M := by exact_mod_cast NeZero.pos M
  let sig : ZMod N → (K → Fin M) := fun x r => dirichletCell M (r.1 * x)
  -- each fibre embeds into `B(K; ρ)`
  have hfib : ∀ s : K → Fin M, (Finset.univ.filter fun x => sig x = s).card ≤ (bohr K ρ).card := by
    intro s
    by_cases hne : (Finset.univ.filter fun x => sig x = s).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      have hx₀s := (Finset.mem_filter.mp hx₀).2
      apply Finset.card_le_card_of_injOn (fun x => x - x₀)
      · intro x hx
        have hxs := (Finset.mem_filter.mp hx).2
        unfold bohr
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
        have hcell : dirichletCell M (r * x) = dirichletCell M (r * x₀) :=
          (congrFun hxs ⟨r, hr⟩).trans (congrFun hx₀s ⟨r, hr⟩).symm
        have hc := dirichletCell_close hcell
        have hrw : r * (x - x₀) = r * x - r * x₀ := by ring
        rw [hrw]
        have hcR : (centeredAbs (r * x - r * x₀) : Real) * M < N := by exact_mod_cast hc
        have : (centeredAbs (r * x - r * x₀) : Real) < N / M := by rw [lt_div_iff₀ hMR]; exact hcR
        have h2 : (N : Real) / M ≤ ρ * N := by
          rw [div_le_iff₀ hMR]; nlinarith
        linarith
      · intro x _ y _ h
        simpa using h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hcover : (Finset.univ : Finset (ZMod N)).card =
      ∑ s : K → Fin M, (Finset.univ.filter fun x => sig x = s).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext x; simp
    · intro s _ t _ hst
      rw [Function.onFun, Finset.disjoint_filter]
      intro x _ hs ht
      exact hst (hs.symm.trans ht)
  have hN : (Finset.univ : Finset (ZMod N)).card = N := by simp [ZMod.card]
  calc N = ∑ s : K → Fin M, (Finset.univ.filter fun x => sig x = s).card := hN.symm.trans hcover
    _ ≤ ∑ _s : K → Fin M, (bohr K ρ).card := Finset.sum_le_sum fun s _ => hfib s
    _ = M ^ K.card * (bohr K ρ).card := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun]

end LeanProofs.GowersSzemeredi
