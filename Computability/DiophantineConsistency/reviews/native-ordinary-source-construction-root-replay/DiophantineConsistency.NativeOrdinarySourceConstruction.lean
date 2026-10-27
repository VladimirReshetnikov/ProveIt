import DiophantineConsistency.CurrentPositiveZero2011

/-! A positive zero of the literal ordinary old-z source supplies the same
scalar packing data and rank for a fresh Carrier65 construction. The private
Pell witnesses are rebuilt; no divisibility of the supplied ordinary multiplier
by the discriminant is assumed. The final current-port corollaries are external
Lean equivalences, not an object-language HA or ZFC derivation. -/

namespace DiophantineConsistency.NativeOrdinarySourceConstruction

open NativePellBootstrap NativeBinaryScale NativeSourceMask
  NativePositiveSourceConstruction

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- All source arithmetic uses the same rank and the same transport gap. -/
theorem source_rank_window (p : Fin 4 → ℤ) (hp : PortBox p)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) :
    NativeRankVariation.windowRank (sourceQ p x : ℤ) (gap p x) (x 1)
      (p 2) (p 3) (x 0) = nativeRank x := by
  have hb := (source_gap_bounds p hp x hx hs).2.1
  have hC : (gap p x : ℤ) = (sourceQ p x : ℤ) - x 1 - x 2 := by
    have hh := congrArg (fun n : ℕ => (n : ℤ)) hb
    push_cast at hh
    omega
  rw [source_rank_eq_target p x hs]
  dsimp only [nativeTarget]
  rw [← sourceQ_cast p hp.beta_pos.le x, hC]
  unfold NativeRankVariation.windowRank
  ring

/-- The rank's natural conversion is justified before filling the scalar Data. -/
theorem source_rank_cast (p : Fin 4 → ℤ) (hp : PortBox p)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) :
    ((nativeRank x).toNat : ℤ) = nativeRank x := by
  have h := source_native_rank_ge_twentyfour p hp.beta_pos hp.K_nonneg
    hp.MC_nonneg hp.MF_nonneg x hx hs
  exact Int.toNat_of_nonneg (by omega)

/-- Every scalar field is copied from the supplied positive source. Only the
already derived binary exponent is an explicit argument to this constructor. -/
def sourceData (p : Fin 4 → ℤ) (hp : PortBox p) (hβ : 15 ≤ p 0)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0)
    (u : ℕ) (hq : sourceQ p x = 2^u) :
    Data p u (nativeRank x).toNat where
  J := x 0
  F := x 1
  alpha := x 2
  z := x 3
  w := x 10
  C := gap p x
  J_pos := hx 0
  F_pos := hx 1
  alpha_pos := hx 2
  z_pos := hx 3
  w_pos := hx 10
  C_pos := (source_gap_bounds p hp x hx hs).1
  q_balance := by
    have hh := sourceQ_cast p hp.beta_pos.le x
    rw [hq] at hh
    linear_combination -hh
  balance := (source_gap_bounds p hp x hx hs).2.1.trans hq
  forced_product := by
    have hX := NativePellPower.source_X_eq_two_pow_rank p hp hβ x hx hs
    have hmul := source_X_eq_q_mul p hp.beta_pos.le x hs
    rw [hq] at hmul
    rw [Nat.mul_comm, ← hmul, hX]
  transport := by
    have ht := NativeSourceWindow.source_transport_identity p hp x hx hs
    have hqpos : 1 ≤ sourceQ p x := by simp [sourceQ]
    have hz := congrArg (fun n : ℕ => (n : ℤ)) ht
    push_cast [Nat.cast_sub (hx 3), Nat.cast_sub hqpos,
      Int.toNat_of_nonneg hp.K_nonneg] at hz
    rw [hq] at hz
    linear_combination hz
  rank := by
    rw [← hq, source_rank_window p hp x hx hs, source_rank_cast p hp x hx hs]

/-- A positive ordinary source, its finite mask interface, and MC mod4 suffice.
Neither a canonical private seed nor a Carrier65 zero is a premise. -/
theorem source_constructs_carrier65 (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) :
    ∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p) = 0 ∧
      v 0 = x 0 ∧ v 1 = x 1 ∧ v 2 = x 2 ∧
      v 3 = x 3 ∧ v 8 = x 10 := by
  obtain ⟨N,hN,hq,_,_,_,_,_,hpop,_,_⟩ :=
    NativeSourceWindow.source_native_window p hi x hx hs
  have hqu : sourceQ p x = 2^(d*N) := by rw [hq, pow_mul]
  let data := sourceData p hi.portBox hi.beta_ge_fifteen x hx hs (d*N) hqu
  have hu : 0 < d*N := Nat.mul_pos (by have := hi.width; omega) hN
  have hmod := ThirteenCarrierComplete.source_rank_mod_four p hi hMC4 x hx hs
  exact population_positive_polynomial_zero hi.portBox.beta_pos data hu hpop hmod

/-- Strictly positive natural coordinates of the actual old-z source. -/
def PositiveSource (p : Fin 4 → ℤ) : Prop :=
  ∃ x : Fin 31 → ℕ, (∀ j, 0 < x j) ∧
    ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0

/-- The source endpoint uses the identical once-shifted four current ports. -/
def CurrentPositiveSource : Prop :=
  PositiveSource (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ))

/-- All positive ordinary current-source zeros yield an actual current zero. -/
theorem current_source_positive_zero (h : CurrentPositiveSource) :
    CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial := by
  obtain ⟨x,hx,hs⟩ := h
  obtain ⟨v,hv,hzero,_⟩ := source_constructs_carrier65
    (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ))
    CurrentWindowCarry2011.interface CurrentMasks2011.lowPort_four x hx hs
  exact ⟨v,hv,hzero⟩

/-- The reverse existence map starts with the actual zero's proved canonical
restoration. It does not say that arbitrary private ordinary seeds are canonical. -/
theorem current_positive_zero_source
    (h : CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial) :
    CurrentPositiveSource := by
  obtain ⟨v,hv,hzero⟩ := h
  change MvPolynomial.eval v
    (Carrier65.polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ))) = 0 at hzero
  rw [Carrier65.eval_polynomial] at hzero
  have hK : (0 : ℤ) < CurrentKernel2011.K := by exact_mod_cast CurrentKernel2011.K_pos
  have hb : 0 < CurrentMasks2011.ports (CurrentKernel2011.K : ℤ) 0 := by
    change (0 : ℤ) < CurrentMasks2011.beta
    exact_mod_cast CurrentMasks2011.beta_pos
  obtain ⟨n,_,hn,hcanonical⟩ := Carrier66.positive_zero_restores_canonical
    (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ))
    (CurrentCarrierArithmetic2011.portBounds _ hK) v hv hzero
  let w := Carrier66.restore (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) v n
  exact ⟨Carrier66Source.sourceNat _ w,
    Carrier66Source.sourceNat_pos _ w hb hn hcanonical,
    Carrier66Source.sourceNat_rows _ w hb hn hcanonical⟩

theorem current_source_iff_positive_zero :
    CurrentPositiveSource ↔
      CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial :=
  ⟨current_source_positive_zero, current_positive_zero_source⟩

/-- External Lean equivalence with the repository's actual axiom predicate. -/
theorem current_source_iff_not_conZFC :
    CurrentPositiveSource ↔ ¬ DiophantineConsistency.ConZFC :=
  current_source_iff_positive_zero.trans CurrentPositiveZero2011.positive_zero_iff_not_conZFC

theorem no_current_source_iff_conZFC :
    (¬ CurrentPositiveSource) ↔ DiophantineConsistency.ConZFC :=
  (not_congr current_source_iff_positive_zero).trans
    CurrentPositiveZero2011.no_positive_zero_iff_conZFC

end DiophantineConsistency.NativeOrdinarySourceConstruction
