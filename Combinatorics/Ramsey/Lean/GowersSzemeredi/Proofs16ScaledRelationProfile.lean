import GowersSzemeredi.Proofs16PrimeProfileBudget

/-! A Bohr graph estimate with a modulus-independent cutoff. The analytic
truncation and size conditions are discharged by explicit scalar budgets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Proportional smoothing discharges the analytic budgets in the sparse
relation profile; the remaining assumptions are scalar bounds. -/
theorem sparse_relation_profile_scaled {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D C : Finset (ZMod N)) (hC : C ⊆ D) (hCne : C.Nonempty)
    (L : κ → ZMod N → ZMod N) (hzero : ∀ j, L j 0 = 0)
    (a : ι → Nat) (b : κ → Nat) (R : Nat) {tau beta theta : Real}
    (htau : 0 < tau) (htauHalf : tau < 1 / 2) (hN : 1 ≤ tau * N)
    (hbeta : 0 < beta) (hbetaOne : beta ≤ 1)
    (hR : 1 / tau^2 ≤ R + 1)
    (hsmall : 120 * Fintype.card (ι ⊕ (κ ⊕ κ)) * tau ≤ beta)
    (hbase : beta * N ≤ ((mixedBohr gamma (fun i => a i - ⌊tau * N⌋₊)).card : Real))
    (hca : ∀ i, ⌊tau * N⌋₊ ≤ a i) (hcb : ∀ j, ⌊tau * N⌋₊ ≤ b j)
    (ha : ∀ i, 2 * a i < N) (hb : ∀ j, 2 * b j < N)
    (htheta : theta < 1)
    (hbad : ((boundedBadRelationPairs gamma D L C R).card : Real) ≤ theta * (C.card : Real)^2) :
    ∃ delta : Real, 0 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (x : ↥(mixedBohr gamma (fun i => a i - ⌊tau * N⌋₊))) (y : ↥C) =>
        (if (x : ZMod N) ∈ mixedBohr (fun j => L j y) (fun j => b j - ⌊tau * N⌋₊)
          then (1 : Real) else 0) - delta) ≤
      3 * (480 * Fintype.card (ι ⊕ (κ ⊕ κ)) * tau / beta + theta) *
        ((mixedBohr gamma (fun i => a i - ⌊tau * N⌋₊)).card : Real)^2 * (C.card : Real)^2 := by
  have hscalar : (Fintype.card (ι ⊕ (κ ⊕ κ)) : Real) * tau ≤ 1 / 2 := by linarith
  have htrunc := (prime_profile_truncation_scaled (N := N) _ R htau htauHalf hscalar hR).trans
    (prime_profile_band_scaled (N := N) _ htau hN).1
  obtain ⟨hsize, hratio⟩ := prime_profile_size_scaled (N := N) _ _ htau hN hbeta hbase hsmall
  obtain ⟨delta, hd0, hd1, hbox⟩ := sparse_relation_profile_quasirandom gamma D C hC hCne L hzero
    a b hca hcb ha hb (centeredBall_floor_mass (N := N) htau htauHalf).1 htheta hbad htrunc hsize
  refine ⟨delta, hd0, hd1, hbox.trans ?_⟩
  gcongr

end LeanProofs.GowersSzemeredi
