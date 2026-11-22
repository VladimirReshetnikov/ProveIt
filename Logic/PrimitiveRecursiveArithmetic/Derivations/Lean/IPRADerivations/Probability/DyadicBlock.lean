import IPRADerivations.Probability.KolmogorovBlock

/-!
# Kolmogorov's inequality for one dyadic block, in the law of the whole sample

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`, proof of `thm:dyadic-slln`:
"Kolmogorov's inequality gives `P(bad block r) ≤ 2^{r+1} σ²/(2ε 2^r)²`", the probability taken in the law of the whole
sample of length `H`.

`KolmogorovBlock.block_kolmogorov` states the inequality for the `(N + m)`-fold law through reparametrized bodies. Here
it is restated for any crossing range `N ≤ H` with the crossing mass as an explicit sum,

  `Pc(N, H) = Σ_{t<M^H} P_H(t) Σ_{c≤N} I_c(t)`                                    (`pcB`, `Pc`)

(`P_H` the `H`-fold product weight `TB`, `I_c` the first-crossing indicator `IB` at the threshold `a(M, x)²`):

* `block_cross`: `a² Pc(N, H) + T_H N S² ≤ T_H N W Q`, with `W = Σ w`, `S = Σ w X`, `Q = Σ w X²` and `T_H = W^H` the
  total mass — i.e. `a² P(max_{c≤N} W²(S_c − cμ)² ≥ a²) ≤ N W² σ²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.DyadicBlock

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Probability.ProductPower (TB Tt Pr TB_at wdB total_pow)
open LeanProofs.IPRA.Probability.KolmogorovIid (IB rp Yp)
open LeanProofs.IPRA.Probability.KolmogorovIidGlue (Cv Cv_at)
open LeanProofs.IPRA.Probability.ProductMarginal (ρn hr rpn_at hr_at)
open LeanProofs.IPRA.Probability.KolmogorovBlock (hB block_kolmogorov hB_low)
open LeanProofs.IPRA.Probability.FirstCrossing (Ib nbB ge inst2_nbB ge_of_le cover)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A crossing witness: if `i < K` and `c_i ≤ D_i`, then `Σ_{k<K} I_k = 1` (one first crossing before `K`). -/
theorem crossing_witness (c D : PTm 2) {i K y : PTm n} (hi : Γ ⊢[PRAAx] lt i K)
    (hc : Γ ⊢[PRAAx] le (inst2 c i y) (inst2 D i y)) : Γ ⊢[PRAAx] ap2 (sumF (Ib c D)) K y ≐ one := by
  have hn : Γ ⊢[PRAAx] inst2 (nbB c D) i y ≐ zero := by
    rw [inst2_nbB]
    exact (congrMonus (.eqRefl _) (ge_of_le hc)).eqTrans (monus_self _)
  have p0 := prod_zero_of (nbB c D) hi hn
  exact (add_zero _).eqSymm.eqTrans ((congrAdd (.eqRefl _) p0.eqSymm).eqTrans (cover c D K y))

section Block

variable (w X a : PTm 2)

/-- The crossing mass summand `P_H(t) Σ_{c≤N} I_c(t)` over `(t, ⟨N, ⟨H, ⟨M, x⟩⟩⟩)`. -/
def pcB : PTm 2 :=
  ap2 (prodF (wdB w)) (fstT (sndT (var 1))) (pairT (var 0) (sndT (sndT (var 1)))) *
    ap2 (sumF (IB w X (Cv a))) (succ (fstT (var 1))) (pairT (var 0) (sndT (sndT (var 1))))

/-- `Pc(N, H) = Σ_{t<M^H} P_H(t) Σ_{c≤N} I_c(t)`. -/
abbrev Pc (N H M x : PTm n) : PTm n := ap2 (sumF (pcB w X a)) (pw M H) (pairT N (pairT H (pairT M x)))

/-- The crossing count `Σ_{c≤N} I_c(t)`. -/
abbrev Cc (N t M x : PTm n) : PTm n := ap2 (sumF (IB w X (Cv a))) (succ N) (pairT t (pairT M x))

theorem inst2_pcB (t N H M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pcB w X a) t (pairT N (pairT H (pairT M x))) ≐ Pr w H t M x * Cc w X a N t M x := by
  have e : inst2 (pcB w X a) t (pairT N (pairT H (pairT M x))) =
      ap2 (prodF (wdB w)) (fstT (sndT (pairT N (pairT H (pairT M x))))) (pairT t (sndT (sndT (pairT N (pairT H (pairT M x)))))) *
        ap2 (sumF (IB w X (Cv a))) (succ (fstT (pairT N (pairT H (pairT M x)))))
          (pairT t (sndT (sndT (pairT N (pairT H (pairT M x)))))) := by
    simp [pcB, inst2]
  rw [e]
  have h1 : Γ ⊢[PRAAx] fstT (sndT (pairT N (pairT H (pairT M x)))) ≐ H := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have h2 : Γ ⊢[PRAAx] sndT (sndT (pairT N (pairT H (pairT M x)))) ≐ pairT M x :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  exact congrMul (congrAp2 _ h1 (congrPairT (.eqRefl _) h2))
    (congrAp2 _ (congrSucc (fst_pair _ _)) (congrPairT (.eqRefl _) h2))

/-- Abstract algebra: `R = T`, `H = C₂ C`, `C₂ = A A`, `Pc = T C` give `R H = (A A) Pc`. -/
theorem sum_alg {R Hh T C A C2 Pc : PTm n} (f1 : Γ ⊢[PRAAx] R ≐ T) (f2 : Γ ⊢[PRAAx] Hh ≐ C2 * C)
    (f3 : Γ ⊢[PRAAx] C2 ≐ A * A) (f4 : Γ ⊢[PRAAx] Pc ≐ T * C) : Γ ⊢[PRAAx] R * Hh ≐ (A * A) * Pc := by
  have g1 := natEq f1; have g2 := natEq f2; have g3 := natEq f3; have g4 := natEq f4
  apply deriveNat; ipra_simps
  linear_combination 𝔞 Hh * g1 + 𝔞 T * g2 + 𝔞 T * 𝔞 C * g3 - 𝔞 A * 𝔞 A * g4

/-- The summand of `block_kolmogorov` is `a² · pcB`. -/
theorem summand_eq {M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (t N m x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rp (TB w) ρn * hr (hB w X a)) t (Yp N m M x) ≐
      (inst2 a M x * inst2 a M x) * inst2 (pcB w X a) t (pairT N (pairT (N + m) (pairT M x))) := by
  rw [inst2_mul']
  have e3 := Cv_at (Γ := Γ) (a * a) t N M x
  have e5 : inst2 (a * a) M x = inst2 a M x * inst2 a M x := by simp [inst2]
  rw [e5] at e3
  exact sum_alg ((rpn_at (TB w) t N m M x).eqTrans (TB_at w t (N + m) M x)) ((hr_at (hB w X a) t N m M x).eqTrans (hB_low w X a hM)) e3
    (inst2_pcB w X a t N (N + m) M x)

/-- Abstract algebra of the block bound. -/
theorem cross_alg {L1 A P P' Tm TN TH N S W Q : PTm n} (bk : Γ ⊢[PRAAx] le (L1 + Tm * (N * (S * S) * TN)) (Tm * (N * (W * Q) * TN)))
    (hL : Γ ⊢[PRAAx] L1 ≐ (A * A) * P') (hP : Γ ⊢[PRAAx] P' ≐ P) (hT : Γ ⊢[PRAAx] Tm * TN ≐ TH) :
    Γ ⊢[PRAAx] le (A * A * P + TH * (N * (S * S))) (TH * (N * (W * Q))) := by
  have e0 := natEq (eq_add_of_le bk)
  have e1 := natEq hL; have e2 := natEq hP; have e3 := natEq hT
  refine le_of_eq_add (d := monus (Tm * (N * (W * Q) * TN)) (L1 + Tm * (N * (S * S) * TN))) ?_
  apply deriveNat; ipra_simps
  linear_combination e0 + e1 + 𝔞 A * 𝔞 A * e2 - (𝔞 N * 𝔞 W * 𝔞 Q - 𝔞 N * 𝔞 S * 𝔞 S) * e3

/-- Kolmogorov's inequality for the crossings within the first `N ≤ H` coordinates, in the `H`-fold law:
`a² Pc(N, H) + T_H N S² ≤ T_H N W Q`. -/
theorem block_cross {M x H N : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w) M x ≐ succ (pred (ap2 (sumF w) M x))) (hNH : Γ ⊢[PRAAx] le N H) :
    Γ ⊢[PRAAx] le (inst2 a M x * inst2 a M x * Pc w X a N H M x + Tt w H M x * (N * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x)))
      (Tt w H M x * (N * (ap2 (sumF w) M x * ap2 (sumF (w * (X * X))) M x))) := by
  have eH := eq_add_of_le hNH
  have bk := block_kolmogorov w X a hM hW N (monus H N)
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have s1 : Syn.shift (Yp N (monus H N) M x) = Yp (Syn.shift N) (Syn.shift (monus H N)) (Syn.shift M) (Syn.shift x) := by
    simp [Syn.shift]
  have s2 : Syn.shift (pairT N (pairT (N + monus H N) (pairT M x))) =
      pairT (Syn.shift N) (pairT (Syn.shift N + Syn.shift (monus H N)) (pairT (Syn.shift M) (Syn.shift x))) := by
    simp [Syn.shift]
  have s3 : Syn.shift (inst2 a M x * inst2 a M x) = inst2 a (Syn.shift M) (Syn.shift x) * inst2 a (Syn.shift M) (Syn.shift x) := by
    rw [ProductPower.shift_mul'', ProductPower.shift_inst2']
  have hL : Γ ⊢[PRAAx] ap2 (sumF (rp (TB w) ρn * hr (hB w X a))) (pw M (N + monus H N)) (Yp N (monus H N) M x) ≐
      (inst2 a M x * inst2 a M x) * ap2 (sumF (pcB w X a)) (pw M (N + monus H N)) (pairT N (pairT (N + monus H N) (pairT M x))) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [s1, s2, s3]
    exact summand_eq w X a hM'.wk (var 0) (Syn.shift N) (Syn.shift (monus H N)) (Syn.shift x)
  have hP : Γ ⊢[PRAAx] ap2 (sumF (pcB w X a)) (pw M (N + monus H N)) (pairT N (pairT (N + monus H N) (pairT M x))) ≐
      Pc w X a N H M x :=
    congrAp2 _ (congrAp2 powF eH.eqSymm (.eqRefl M)) (congrPairT (.eqRefl _) (congrPairT eH.eqSymm (.eqRefl _)))
  have hT : Γ ⊢[PRAAx] Tt w (monus H N) M x * Tt w N M x ≐ Tt w H M x := by
    refine (congrMul (total_pow w hM _) (total_pow w hM _)).eqTrans ?_
    refine .eqTrans ?_ (total_pow w hM _).eqSymm
    exact (mul_comm _ _).eqTrans ((pw_add _ _ _).eqSymm.eqTrans (congrAp2 powF eH.eqSymm (.eqRefl _)))
  exact cross_alg bk hL hP hT

end Block

end LeanProofs.IPRA.Probability.DyadicBlock
