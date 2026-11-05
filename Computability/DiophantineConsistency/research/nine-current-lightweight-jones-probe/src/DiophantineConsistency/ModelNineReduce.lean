import DiophantineConsistency.ModelMaster

/-! # Jones 1982, §3 in every model of `𝗜𝚺₁`: membership through one central binomial

Internal counterpart of `Jones1982.Nine.reduced_of_mem`, `mem_of_reduced`,
`sizes_of_reduced` (`Diophantine/Paper1982/NineReduce.lean`) at the input `x = 1`, for a
seed `P = seed` of total degree `≤ 4` with index `z = indexZ seed 0`, `y = indexY seed 0`.

Membership is `∃ w : Fin ν → V, P(1, w) = 0`, evaluated in `DiffRing V`.  The ceiling is
`b = bN ε = y + 1 + ε` (so `ι b = 1·y + 1 + ι ε`, as in
`ModelJonesSyntax.mapVars_syntaxVars` with `a 0 = 1`, `a 1 = ι ε`), `B = b⁵`,
`q = qV ν b = B^(codingL4 ν)`, `N = q¹⁶`, and the packed code `R = RV seed b g`, whose value
in the ring of differences is (`sizes_of_reduced`, last component)
`NinePolynomial.rankCode 1 z (ι b) e (ι g) l N q (B − 2z) λ` with `e = eR seed (ι b)`,
`l = lR ν (ι b)`, `λ = lamR ν (ι b)`, `q = qR ν (ι b)`: literally the `let`-bound sums of
`mapVars_syntaxVars`.

* `reduced_of_mem`: membership gives `ε g k` with `0 < g`, `b = 2ᵏ`, `g < b B^(5^ν)` and
  `N² ∣ binom (2R) R`;
* `mem_of_reduced`: conversely from `0 < g`, `b = 2ᵏ`, `g < 4 b B^(5^ν)`, `N² ∣ binom (2R) R`;
* `reduced_iff`: the equivalence, with the bound `g < 4 b B^(5^ν)`;
* `sizes_of_reduced`: `8 ≤ N ≤ R`, `b ≤ N`, `b ≤ R`, and the rank-code value of `R`.

The normalization is only needed at the input `1`: `P(1, 0, …, 0) ≠ 0` as an integer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ModelNineReduce
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticBinomPascal ModelCarries ModelDigitTransfer ModelPacking
  ModelDifferenceRing ExecutableJones ModelMaster
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section
variable {ν : ℕ} (seed : Expr (Fin (ν + 1)))

/-- The ceiling `b = 1·y + 1 + ε`. -/
def bN (ε : V) : V := (indexY seed 0 : V) + 1 + ε

theorem ι_bN (ε : V) : ι (bN seed ε) = 1 * (indexY seed 0 : DiffRing V) + 1 + ι ε := by
  unfold bN
  rw [map_add, map_add, map_natCast, map_one, one_mul]

theorem y_lt_bN (ε : V) : (indexY seed 0 : V) < bN seed ε := by
  unfold bN
  exact lt_of_lt_of_le (lt_add_one _) (le_add_right le_rfl)

/-- **Necessity**, with the stronger bound `g < b B^(5^ν)`. -/
theorem reduced_of_mem (hP : seed.toPolynomial.totalDegree ≤ 4)
    (hnorm : seed.eval (fun j : Fin (ν + 1) => if j = 0 then (1 : ℤ) else 0) ≠ 0)
    (hW : ∃ w : Fin ν → V,
      seed.evalRing (fun j => ι ((Fin.cons (1 : V) w : Fin (ν + 1) → V) j)) = 0) :
    ∃ ε g k : V, 0 < g ∧ bN seed ε = Exp.exp k ∧ g < bN seed ε * (bN seed ε ^ 5) ^ (5 ^ ν) ∧
      (qV ν (bN seed ε) ^ 16) ^ 2 ∣
        binom (2 * RV seed (bN seed ε) g) (RV seed (bN seed ε) g) := by
  obtain ⟨w, hw⟩ := hW
  obtain ⟨K, hKdef⟩ : ∃ K : V, K = (indexY seed 0 : V) + ∑ i, w i + 1 := ⟨_, rfl⟩
  have hKe : K < Exp.exp K := lt_exp K
  have hyb : (indexY seed 0 : V) < Exp.exp K := by
    have h : (indexY seed 0 : V) < K := by
      rw [hKdef]
      exact lt_of_le_of_lt (le_add_right le_rfl) (lt_add_one _)
    exact lt_trans h hKe
  have hwb : ∀ i, w i < Exp.exp K := by
    intro i
    have h1 : w i ≤ ∑ j, w j :=
      Finset.single_le_sum (f := w) (fun j _ => Arithmetic.zero_le (w j)) (Finset.mem_univ i)
    have h2 : ∑ j, w j < K := by
      rw [hKdef]
      exact lt_of_le_of_lt (le_add_left le_rfl) (lt_add_one _)
    exact lt_of_le_of_lt h1 (lt_trans h2 hKe)
  obtain ⟨hτ1, hgb⟩ := tau1_of_code ν w hwb
  have hy1 : (indexY seed 0 : V) + 1 ≤ Exp.exp K := lt_iff_succ_le.mp hyb
  have hbN : bN seed (Exp.exp K - ((indexY seed 0 : V) + 1)) = Exp.exp K := by
    unfold bN
    exact add_tsub_cancel_of_le hy1
  have h4 : Exp.exp K ≤ 4 * Exp.exp K := by
    apply ι_le_ι.mp
    simp only [map_mul, map_ofNat]
    have := ι_nonneg (Exp.exp K)
    linarith
  have hg4 : gOf ν w (Exp.exp K ^ 5) < 4 * Exp.exp K * (Exp.exp K ^ 5) ^ (5 ^ ν) :=
    lt_of_lt_of_le hgb (mul_le_mul_of_nonneg_right h4 (Arithmetic.zero_le _))
  refine ⟨Exp.exp K - ((indexY seed 0 : V) + 1), gOf ν w (Exp.exp K ^ 5), K, ?_, hbN, ?_, ?_⟩
  · -- `g > 0` by the normalization
    rw [pos_iff_ne_zero]
    intro hg0
    have hg0' : ∑ i : Fin ν, w i * (Exp.exp K ^ 5) ^ (5 ^ ((i : ℕ) + 1)) = 0 := hg0
    have hw0 : ∀ i, w i = 0 := by
      intro i
      have h1 : w i * (Exp.exp K ^ 5) ^ (5 ^ ((i : ℕ) + 1)) = 0 :=
        (Finset.sum_eq_zero_iff.mp hg0') i (Finset.mem_univ i)
      have h2 : 1 ≤ (Exp.exp K ^ 5) ^ (5 ^ ((i : ℕ) + 1)) :=
        one_le_pow₀ (le_trans (one_le_exp K) (self_le_pow_five (one_le_exp K)))
      have h3 : w i ≤ w i * (Exp.exp K ^ 5) ^ (5 ^ ((i : ℕ) + 1)) :=
        le_mul_of_one_le_right (Arithmetic.zero_le _) h2
      rw [h1] at h3
      exact le_antisymm h3 (Arithmetic.zero_le _)
    have hpt : (fun j => ι ((Fin.cons (1 : V) w : Fin (ν + 1) → V) j)) =
        fun j : Fin (ν + 1) => (((if j = 0 then (1 : ℤ) else 0) : ℤ) : DiffRing V) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp
      · simp [hw0 i, Fin.succ_ne_zero]
    have h2 : seed.evalRing
        (fun j : Fin (ν + 1) => (((if j = 0 then (1 : ℤ) else 0) : ℤ) : DiffRing V)) = 0 := by
      rw [← hpt]
      exact hw
    rw [ModelCoding.evalRing_intCast] at h2
    exact hnorm (Int.cast_eq_zero.mp h2)
  · rw [hbN]
    exact hgb
  · rw [hbN]
    exact (pack_iff seed hyb hg4).mp
      ⟨hτ1, tau2_holds seed hyb, (tau3_iff seed hP hyb w hwb).mpr hw⟩

/-- **Sufficiency**, from the weaker bound `g < 4 b B^(5^ν)`. -/
theorem mem_of_reduced (hP : seed.toPolynomial.totalDegree ≤ 4) {ε g k : V}
    (hb : bN seed ε = Exp.exp k) (hgb : g < 4 * bN seed ε * (bN seed ε ^ 5) ^ (5 ^ ν))
    (hdvd : (qV ν (bN seed ε) ^ 16) ^ 2 ∣
      binom (2 * RV seed (bN seed ε) g) (RV seed (bN seed ε) g)) :
    ∃ w : Fin ν → V,
      seed.evalRing (fun j => ι ((Fin.cons (1 : V) w : Fin (ν + 1) → V) j)) = 0 := by
  have hyb : (indexY seed 0 : V) < Exp.exp k := by
    rw [← hb]
    exact y_lt_bN seed ε
  rw [hb] at hgb hdvd
  obtain ⟨hτ1, -, hτ3⟩ := (pack_iff seed hyb hgb).mpr hdvd
  obtain ⟨w, hw, hgw⟩ := code_of_tau1 ν (g_lt_q3 seed hyb hgb) hτ1
  subst hgw
  exact ⟨w, (tau3_iff seed hP hyb w hw).mp hτ3⟩

/-- **The reduction**: `P(1, w) = 0` is solvable iff the reduced conditions are. -/
theorem reduced_iff (hP : seed.toPolynomial.totalDegree ≤ 4)
    (hnorm : seed.eval (fun j : Fin (ν + 1) => if j = 0 then (1 : ℤ) else 0) ≠ 0) :
    (∃ w : Fin ν → V,
      seed.evalRing (fun j => ι ((Fin.cons (1 : V) w : Fin (ν + 1) → V) j)) = 0) ↔
    ∃ ε g k : V, 0 < g ∧ bN seed ε = Exp.exp k ∧
      g < 4 * bN seed ε * (bN seed ε ^ 5) ^ (5 ^ ν) ∧
      (qV ν (bN seed ε) ^ 16) ^ 2 ∣
        binom (2 * RV seed (bN seed ε) g) (RV seed (bN seed ε) g) := by
  constructor
  · intro hW
    obtain ⟨ε, g, k, hg0, hb, hgb, hdvd⟩ := reduced_of_mem seed hP hnorm hW
    refine ⟨ε, g, k, hg0, hb, ?_, hdvd⟩
    have h4 : bN seed ε ≤ 4 * bN seed ε := by
      apply ι_le_ι.mp
      simp only [map_mul, map_ofNat]
      have := ι_nonneg (bN seed ε)
      linarith
    exact lt_of_lt_of_le hgb (mul_le_mul_of_nonneg_right h4 (Arithmetic.zero_le _))
  · rintro ⟨ε, g, k, -, hb, hgb, hdvd⟩
    exact mem_of_reduced seed hP hb hgb hdvd

/-- The size facts (for Lemma 2.25) and the rank-code value of the packed code. -/
theorem sizes_of_reduced {ε g k : V} (hb : bN seed ε = Exp.exp k)
    (hgb : g < 4 * bN seed ε * (bN seed ε ^ 5) ^ (5 ^ ν)) :
    8 ≤ qV ν (bN seed ε) ^ 16 ∧ qV ν (bN seed ε) ^ 16 ≤ RV seed (bN seed ε) g ∧
      bN seed ε ≤ qV ν (bN seed ε) ^ 16 ∧ bN seed ε ≤ RV seed (bN seed ε) g ∧
      ι (RV seed (bN seed ε) g) =
        NinePolynomial.rankCode (1 : DiffRing V) (indexZ seed 0 : DiffRing V) (ι (bN seed ε))
          (eR seed (ι (bN seed ε))) (ι g) (lR ν (ι (bN seed ε)))
          (qR ν (ι (bN seed ε)) ^ 16) (qR ν (ι (bN seed ε)))
          (ι (bN seed ε) ^ 5 - 2 * (indexZ seed 0 : DiffRing V)) (lamR ν (ι (bN seed ε))) := by
  have hyb : (indexY seed 0 : V) < Exp.exp k := by
    rw [← hb]
    exact y_lt_bN seed ε
  rw [hb] at hgb ⊢
  obtain ⟨hb1, hbB, -, -, -⟩ := v_base seed hyb
  obtain ⟨h9, -, -, -, -⟩ := dr_base seed hyb
  obtain ⟨hL1, -, -, -, -, -, -, -⟩ := L_facts ν
  have hB1 : 1 ≤ Exp.exp k ^ 5 := le_trans hb1 hbB
  have hbq : Exp.exp k ≤ qV ν (Exp.exp k) := by
    rw [qV_eq]
    calc Exp.exp k ≤ Exp.exp k ^ 5 := hbB
      _ = (Exp.exp k ^ 5) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hB1 hL1
  have hqN : qV ν (Exp.exp k) ≤ qV ν (Exp.exp k) ^ 16 := by
    calc qV ν (Exp.exp k) = qV ν (Exp.exp k) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (le_trans hb1 hbq) (by omega)
  have hbN : Exp.exp k ≤ qV ν (Exp.exp k) ^ 16 := le_trans hbq hqN
  have h9N : (9 : DiffRing V) ≤ ι (qV ν (Exp.exp k) ^ 16) := le_trans h9 (ι_le_ι.mpr hbN)
  have hN2 : 2 ≤ qV ν (Exp.exp k) ^ 16 := by
    apply ι_le_ι.mp
    simp only [map_ofNat]
    linarith
  have hNR : qV ν (Exp.exp k) ^ 16 ≤ RV seed (Exp.exp k) g := by
    unfold RV
    exact centralCode_ge_base hN2
  refine ⟨?_, hNR, hbN, le_trans hbN hNR, RV_rank seed hyb hgb⟩
  apply ι_le_ι.mp
  simp only [map_ofNat]
  linarith

end

end DiophantineConsistency.ModelNineReduce
