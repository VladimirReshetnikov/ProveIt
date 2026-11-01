import DiophantineConsistency.AdaptiveGap85PartialRankRemainder
import DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FixedSpecialization
open AdaptiveGap85Factors AdaptiveGap85FamilyBinding AdaptiveGap85PartialRankRemainder
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

theorem one_lt_pow_general (x n : ℕ) (hx : 1<x) (hn : n ≠ 0) : 1<x^n :=
  Nat.one_lt_pow hn hx

theorem fixed_ports_partial_family_blocks_rank_normalization :
    ∃ w : Fin 13 → ℤ, (∀ i,0<w i) ∧
      ((factors CurrentWindowCarry2011.ports).1).eval w=1 ∧
      ((factors CurrentWindowCarry2011.ports).2.2.1).eval w=1 ∧
      (AdaptiveGap85Literal.expressionAt85 CurrentWindowCarry2011.ports).eval w ≠ 0 ∧
      let q := 1+w 0*(CurrentMasks2011.beta:ℤ)
      ∀ F' C' : ℤ, 0<F' → 0<C' → F'+C'<q →
        ¬((rankPlus q (w 1) (w 2) (w 0) (CurrentMasks2011.lowPort:ℤ)
             ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):ℤ)+rankMinus q F' C')%q =
          (rankMinus q (w 1) (w 2)+rankPlus q F' C' (w 0) (CurrentMasks2011.lowPort:ℤ)
             ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):ℤ))%q) := by
  let b : ℤ := CurrentMasks2011.beta
  let k : ℤ := CurrentKernel2011.K
  let mu : ℤ := CurrentMasks2011.lowPort
  let nu : ℤ := (CurrentMasks2011.highPort+CurrentMasks2011.beta : ℕ)
  have hβ : 0<(CurrentMasks2011.beta:ℤ) := by
    have hr : 1<CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; decide
    have hp : 1<CurrentMasks2011.radix^2011 := one_lt_pow_general _ _ hr (by decide)
    have hn : 0<CurrentMasks2011.beta := by
      unfold CurrentMasks2011.beta
      exact Nat.sub_pos_of_lt hp
    exact_mod_cast hn
  have hb : 1≤b := by dsimp [b]; omega
  have hk : 0≤k := by dsimp [k]; exact Int.natCast_nonneg _
  have hp : ports b k mu nu = CurrentWindowCarry2011.ports := by
    dsimp only [b,k,mu,nu]
    change _ = ![(CurrentMasks2011.beta:ℤ), (CurrentKernel2011.K:ℤ), (CurrentMasks2011.lowPort:ℤ), (CurrentMasks2011.highPort:ℤ)+(CurrentMasks2011.beta:ℤ)]
    simp only [ports,Nat.cast_add]
  obtain ⟨w,hw,hfirst,haux,hfull,hblock⟩ := partial_family_blocks_rank_normalization b k mu nu hb hk
  refine ⟨w,hw,?_,?_,?_,?_⟩
  · simpa only [hp] using hfirst
  · simpa only [hp] using haux
  · simpa only [hp] using hfull
  · exact hblock
end DiophantineConsistency.AdaptiveGap85FixedSpecialization
