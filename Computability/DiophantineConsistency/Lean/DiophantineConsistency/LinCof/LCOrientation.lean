import DiophantineConsistency.LinCof.LCProjector
import DiophantineConsistency.P138.P138Orientation

/-! # Orientation for the linear cofactor: every sign is positive

The linear-cofactor form of `P138Orientation.oriented`. At a zero, after the signed projector
`σX = 2^R` (`LCProjector.projector`):

* `X ≡ 2 (mod 3)` (`LCBootstrap.X_mod`) and `2^R ≡ 2 (mod 3)` for odd `R` force `σ = 1`:
  `c > 0` and `X = 2^R > 0`;
* `k > 0` (`LCFirstIndex.FirstIndex.hpos`), then `Y > 0` from `0 < c (kY)`
  (`LCBudget.c_interval`; the scale `Y` is a free unknown here, so its sign is a consequence of
  the zero), and `A > 0`;
* `q > 0` (`q_pos`): `|q|` divides `X = 2^R`, so `|q| = 2^m`; `q = −2^m` would make
  `β = 2^N − 1` divide `2^m + 1` (`P138Orientation.not_dvd_exp_add_one`). `q_pow2` records the
  power-of-two form of `q` for the scale divisibility of `LCScale`;
* then `J, F, C, q − F − C > 0` from the centered signs (`LCWindow.signs`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCOrientation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCSquares LCBudget LCAdjacent LCWindow
  LCEarlyFold LCRank LCFirstIndex LCProjector
open ArithmeticPellRecurrence ArithmeticPow
open ZRowsCoprimeSquares (abs_eq_ι ι_dvd_iff)
open P138Bootstrap (int_split)
open P138Adjacent (ι_pos)
open P138Orientation (not_dvd_exp_add_one)
open LCNorm (Weight)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Pure
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- Once `X = 2^R`, `|q|` is a power of two. -/
theorem abs_q_pow2 (Rn : V) (hX : (𝓡).X = ι (Exp.exp Rn)) :
    ∃ Qn : V, |(𝓡).q| = ι Qn ∧ Pow2 Qn := by
  obtain ⟨Qn, hQn⟩ := abs_eq_ι (𝓡).q
  have hdvd : Qn ∣ Exp.exp Rn := by
    apply ι_dvd_iff.mp
    rw [← hQn, ← hX, X_def, ← abs_of_nonneg (show (0 : DiffRing V) ≤ (𝓡).q * (𝓡).W by
      rw [← X_def, hX]; exact ι_nonneg _)]
    exact (abs_dvd_abs _ _).mpr (dvd_mul_right _ _)
  exact ⟨Qn, hQn, Pow2.of_dvd hdvd (exp_pow2 _)⟩

/-- **`q > 0`** once `X = 2^R`. -/
theorem q_pos (hp : PortFacts p) (Rn : V) (hX : (𝓡).X = ι (Exp.exp Rn)) : 0 < (𝓡).q := by
  obtain ⟨Qn, hQn, hpow⟩ := abs_q_pow2 p x κ ω Λ ψ wt Rn hX
  have hQe : Exp.exp (log Qn) = Qn := exp_of_exponential (exponential_of_pow2 hpow)
  rcases lt_or_gt_of_ne (q_ne p x κ ω Λ ψ wt hp) with hneg | hpos
  · exfalso
    have hq : (𝓡).q = -ι (Exp.exp (log Qn)) := by rw [hQe, ← hQn, abs_of_neg hneg]; ring
    have hb := hp.beta_exp
    have hβ := beta_pos p hp
    have hbJ := beta_J p x κ ω Λ ψ wt
    -- `J < 0`
    have hJneg : (𝓡).J < 0 := by
      have : p 0 * (𝓡).J < 0 := by
        rw [hbJ, hq]; have := ι_nonneg (Exp.exp (log Qn)); linarith
      by_contra hc
      have := mul_nonneg hβ.le (le_of_not_gt hc); linarith
    obtain ⟨jn, hjn⟩ := abs_eq_ι (𝓡).J
    have hJ : (𝓡).J = -ι jn := by rw [← hjn, abs_of_neg hJneg]; ring
    have hβn : p 0 = ι (Exp.exp (1064921 : V) - 1) := by
      rw [P138EarlyFold.ι_tsub' (one_le_exp _), map_one]; linear_combination hb
    have hdiv : (Exp.exp (1064921 : V) - 1) ∣ Exp.exp (log Qn) + 1 := by
      refine ι_dvd_iff.mp ⟨ι jn, ?_⟩
      rw [map_add, map_one, ← hβn]
      linear_combination hbJ - p 0 * hJ + hq
    exact not_dvd_exp_add_one 1064921 (log Qn) (by norm_num) hdiv
  · exact hpos

/-- Once `X = 2^R`, `q` itself is a power of two. -/
theorem q_pow2 (hp : PortFacts p) (Rn : V) (hX : (𝓡).X = ι (Exp.exp Rn)) :
    ∃ Qn : V, (𝓡).q = ι Qn ∧ Pow2 Qn := by
  obtain ⟨Qn, hQn, hpow⟩ := abs_q_pow2 p x κ ω Λ ψ wt Rn hX
  exact ⟨Qn, by rw [← hQn, abs_of_pos (q_pos p x κ ω Λ ψ wt hp Rn hX)], hpow⟩

/-- **The oriented data.** -/
structure Oriented (E : EarlyFold p x κ ω Λ ψ wt) (M : MainIndex p x κ ω Λ ψ wt E) where
  hq : 0 < (𝓡).q
  hJ : 0 < (𝓡).J
  hF : 0 < (𝓡).F
  hC : 0 < x 1
  hα : 0 < (𝓡).q - (𝓡).F - x 1
  hX : (𝓡).X = ι (Exp.exp M.Rn)
  hk : 0 < (𝓡).k
  hY : 0 < (𝓡).Y
  hc : x 8 = ι E.cn
  hA : (𝓡).A = ι E.Bn

end Pure

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

set_option maxHeartbeats 1000000 in
/-- **Orientation.** At a zero every sign is positive and `X = 2^R`. -/
theorem oriented (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hwt : Weight wt)
    (hz : valueK p x κ ω Λ ψ wt = 0) (E : EarlyFold p x κ ω Λ ψ wt)
    (M : MainIndex p x κ ω Λ ψ wt E) (Fi : FirstIndex p x κ ω Λ ψ wt E M) :
    Nonempty (Oriented p x κ ω Λ ψ wt E M) := by
  obtain ⟨σ, hσ, hcσ, hσX⟩ := projector ψ wt hp h hwt hz E M Fi
  obtain ⟨t, ht⟩ := P72ConvArith.odd_of_mod_two M.hodd
  -- `σ = 1`
  have hσ1 : σ = 1 := by
    rcases hσ with h' | h'
    · exact h'
    · exfalso
      obtain ⟨_, m, hm⟩ := X_mod p x κ ω Λ ψ wt hp
      have h3 := P72ConvArith.exp_odd_mod_three t
      rw [← ht] at h3
      have hd := div_add_mod (Exp.exp M.Rn) 3
      rw [h3] at hd
      have hι := congrArg (ι (V := V)) hd
      simp only [map_add, map_mul, map_ofNat] at hι
      rw [h'] at hσX
      -- `−X = 3 q' + 2` and `X = 3 m + 2`
      have : (3 : DiffRing V) * (ι (Exp.exp M.Rn / 3) + m + 1) = -1 := by
        linear_combination hι - hσX - hm
      rcases int_split (ι (Exp.exp M.Rn / 3) + m + 1) with h0 | h0 <;> linarith
  rw [hσ1, one_mul] at hcσ hσX
  have hXpos : 0 < (𝓡).X := by rw [hσX]; exact ι_pos (exp_pos _)
  have hk : 0 < (𝓡).k := (Fi.hpos hXpos).2
  have hcpos : 0 < x 8 := by rw [hcσ]; exact ι_pos E.hcn0
  have hB : 0 < (𝓡).Budget := budget_pos ψ wt hp h hwt hz
  have hY : 0 < (𝓡).Y := by
    have h' := (c_interval ψ wt hp h hB).2.2
    have h1 : 0 < (𝓡).k * (𝓡).Y := (pos_iff_pos_of_mul_pos h').mp hcpos
    exact (pos_iff_pos_of_mul_pos h1).mp hk
  have hApos : 0 < (𝓡).A := by
    rw [A_eq, a_eq]; have := mul_pos hXpos hY; linarith
  have hA : (𝓡).A = ι E.Bn := by rw [← E.hBn, abs_of_pos hApos]
  have hq := q_pos p x κ ω Λ ψ wt hp M.Rn hσX
  obtain ⟨hF, hC, hα⟩ := signs ψ wt hp h hB
  have hJ : 0 < (𝓡).J := by
    have h1 := abs_q p x κ ω Λ ψ wt hp
    rw [abs_of_pos hq] at h1
    have hb := beta_pos p hp
    have : 0 < p 0 * (𝓡).J := by rw [beta_J]; linarith
    exact (pos_iff_pos_of_mul_pos this).mp hb
  exact ⟨⟨hq, hJ, (pos_iff_pos_of_mul_pos hF).mpr hq, (pos_iff_pos_of_mul_pos hC).mpr hq,
    (pos_iff_pos_of_mul_pos hα).mpr hq, hσX, hk, hY, hcσ, hA⟩⟩

end Regs

#print axioms q_pos
#print axioms q_pow2
#print axioms oriented

end DiophantineConsistency.LCOrientation
