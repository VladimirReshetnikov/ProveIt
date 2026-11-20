import IPRADerivations.DiophantineNumberTheory.KhinchinOverlap
import IPRADerivations.DiophantineNumberTheory.KhinchinBlockGeo
import IPRADerivations.Foundations.SecondMoment
import IPRADerivations.DiophantineNumberTheory.FLTMultiples

/-!
# The scales of a Khinchin block as one family (`hurwitz_khinchin_ipra`, (K10)–(K11))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"A finite block covers a fixed
fraction of every interval": "Take any finite block `k = K, …, B` of admissible scales … let
`F = Σ_{k=K}^B 1_{E_k(J)}`."

The block is the family of scales `k < B` with `Q_k = 2^{K₀+k}`, `Q'_k = ⌊Q_k/4⌋`, members
`K_k = (Q_k − Q'_k) M` (`KhinchinScale`), common grid `T = R! G`, parameter
`y_k = ⟨M, Q'_k, T, α, γ, β⟩` (`β = b₀ + 1`) and widths `w_k = wb(k, X)` given by a body, where
`X = ⟨K₀, ⟨M, ⟨R, ⟨G, ⟨α, ⟨γ, b₀⟩⟩⟩⟩⟩⟩` packs the parameters.

* `bB wb`: the covering bit `b(c, k, X)` of scale `k` (the body of `Foundations/SecondMoment`), decoded at an
  explicit tuple by `b_at` (one `Prf.eqCongr` over 9-variable cores `KCore`, `yCore`);
* `uB wb`: `u_k = Q_k² w_k`;
* `scale_E`: `Σ_c b(c, k) = |E_k|` as an `IntervalCover.measure`;
* `scale_inter`: `Σ_c b(c, ℓ) b(c, k) = |E_k ∩ E_ℓ|` as an `IntervalOverlap.inter`;
* `b_bit`: `b² = b` at every instance (the hypothesis of `SecondMoment.ord_moment`);
* `pw_mono2`: `2^{K₀+k} ≤ 2^{K₀+B}` for `k ≤ B`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit shift_inst2')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.IntervalCover (covB measure)
open LeanProofs.IPRA.Foundations.IntervalPacking (loB hiB)
open LeanProofs.IPRA.Foundations.IntervalOverlap (inter ovB inst2_ovB)
open LeanProofs.IPRA.Foundations.SecondMoment (ppB inst3_ppB qB inst2_qB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScale (tup AK actK)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The packed parameters -/

/-- `X = ⟨K₀, ⟨M, ⟨R, ⟨G, ⟨α, ⟨γ, b₀⟩⟩⟩⟩⟩⟩`. -/
abbrev Xt (K0 M R G α γ b0 : PTm n) : PTm n := pairT K0 (pairT M (pairT R (pairT G (pairT α (pairT γ b0)))))

/-- The decoding `(k, X) ↦ (k, K₀, M, R, G, α, γ, b₀)`. -/
def decX (k X : PTm n) : Fin 8 → PTm n :=
  ![k, fstT X, fstT (sndT X), fstT (sndT (sndT X)), fstT (sndT (sndT (sndT X))),
    fstT (sndT (sndT (sndT (sndT X)))), fstT (sndT (sndT (sndT (sndT (sndT X))))),
    sndT (sndT (sndT (sndT (sndT (sndT X)))))]

/-- `Q_k = 2^{K₀+k}` in the core variables `0 = k, 1 = K₀, 2 = M, 3 = R, 4 = G, 5 = α, 6 = γ, 7 = b₀`. -/
abbrev QC : PTm 8 := pw two (var 1 + var 0)
/-- `K_k = (Q_k − ⌊Q_k/4⌋) M`. -/
def KCore : PTm 8 := monus QC (quo QC (num 4)) * var 2
/-- `y_k = ⟨M, ⌊Q_k/4⌋, R! G, α, γ, b₀ + 1⟩`. -/
def yCore : PTm 8 := tup (var 2) (quo QC (num 4)) (fact (var 3) * var 4) (var 5) (var 6) (succ (var 7))
/-- `Q_k²`. -/
def q2Core : PTm 8 := QC * QC

/-- The explicit scale data. -/
abbrev Qk (K0 k : PTm n) : PTm n := pw two (K0 + k)
abbrev Kk (K0 M k : PTm n) : PTm n := monus (Qk K0 k) (quo (Qk K0 k) (num 4)) * M
abbrev yk (K0 M R G α γ b0 k : PTm n) : PTm n :=
  tup M (quo (Qk K0 k) (num 4)) (fact R * G) α γ (succ b0)

theorem dec_Xt (k K0 M R G α γ b0 : PTm n) (i : Fin 8) :
    Γ ⊢[PRAAx] decX k (Xt K0 M R G α γ b0) i ≐ (![k, K0, M, R, G, α, γ, b0] : Fin 8 → PTm n) i := by
  have s1 : Γ ⊢[PRAAx] sndT (Xt K0 M R G α γ b0) ≐ pairT M (pairT R (pairT G (pairT α (pairT γ b0)))) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (Xt K0 M R G α γ b0)) ≐ pairT R (pairT G (pairT α (pairT γ b0))) :=
    (congrSnd s1).eqTrans (snd_pair _ _)
  have s3 : Γ ⊢[PRAAx] sndT (sndT (sndT (Xt K0 M R G α γ b0))) ≐ pairT G (pairT α (pairT γ b0)) :=
    (congrSnd s2).eqTrans (snd_pair _ _)
  have s4 : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (Xt K0 M R G α γ b0)))) ≐ pairT α (pairT γ b0) :=
    (congrSnd s3).eqTrans (snd_pair _ _)
  have s5 : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (Xt K0 M R G α γ b0))))) ≐ pairT γ b0 :=
    (congrSnd s4).eqTrans (snd_pair _ _)
  fin_cases i
  · exact .eqRefl _
  · exact fst_pair _ _
  · exact (congrFst s1).eqTrans (fst_pair _ _)
  · exact (congrFst s2).eqTrans (fst_pair _ _)
  · exact (congrFst s3).eqTrans (fst_pair _ _)
  · exact (congrFst s4).eqTrans (fst_pair _ _)
  · exact (congrFst s5).eqTrans (fst_pair _ _)
  · exact (congrSnd s5).eqTrans (snd_pair _ _)

theorem K_at (k K0 M R G α γ b0 : PTm n) :
    Γ ⊢[PRAAx] Syn.subst (decX k (Xt K0 M R G α γ b0)) KCore ≐ Kk K0 M k := by
  have e := Prf.eqCongr (Γ := Γ) KCore (dec_Xt k K0 M R G α γ b0)
  simpa [KCore, QC, subst_ap2] using e

theorem y_at (k K0 M R G α γ b0 : PTm n) :
    Γ ⊢[PRAAx] Syn.subst (decX k (Xt K0 M R G α γ b0)) yCore ≐ yk K0 M R G α γ b0 k := by
  have e := Prf.eqCongr (Γ := Γ) yCore (dec_Xt k K0 M R G α γ b0)
  simpa [yCore, QC, subst_ap2] using e

theorem q2_at (k K0 M R G α γ b0 : PTm n) :
    Γ ⊢[PRAAx] Syn.subst (decX k (Xt K0 M R G α γ b0)) q2Core ≐ Qk K0 k * Qk K0 k := by
  have e := Prf.eqCongr (Γ := Γ) q2Core (dec_Xt k K0 M R G α γ b0)
  simpa [q2Core, QC, subst_ap2] using e

/-! ## The bodies -/

section Bodies

variable (wb : PTm 2)

/-- The parameter `⟨K_k, ⟨w_k, y_k⟩⟩` of scale `k` over `0 = k`, `1 = X` (as a term in `(c, k, X)`). -/
def parT : PTm 3 :=
  pairT (Syn.subst (decX (var 1) (var 2)) KCore)
    (pairT (Syn.subst ![var 1, var 2] wb) (Syn.subst (decX (var 1) (var 2)) yCore))

/-- The covering bit `b(c, k, X)` of scale `k`. -/
def bB : PTm 3 := Syn.subst ![var 0, parT wb] (covB (loB AK) (hiB AK actK))

/-- `u_k = Q_k² w_k` over `0 = k`, `1 = X`. -/
def uB : PTm 2 := Syn.subst (decX (var 0) (var 1)) q2Core * wb

theorem subst_decX {m : ℕ} (σ : Fin 3 → PTm m) (C : PTm 8) :
    Syn.subst σ (Syn.subst (decX (var 1) (var 2)) C) = Syn.subst (decX (σ 1) (σ 2)) C := by
  simp only [Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp [decX]

theorem subst_decX2 {m : ℕ} (σ : Fin 2 → PTm m) (C : PTm 8) :
    Syn.subst σ (Syn.subst (decX (var 0) (var 1)) C) = Syn.subst (decX (σ 0) (σ 1)) C := by
  simp only [Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp [decX]

theorem subst_parT (c k X : PTm n) : Syn.subst ![c, k, X] (parT wb) =
    pairT (Syn.subst (decX k X) KCore) (pairT (inst2 wb k X) (Syn.subst (decX k X) yCore)) := by
  simp only [parT, subst_pairT]
  rw [subst_decX, subst_decX]
  have e : Syn.subst ![c, k, X] (Syn.subst ![var 1, var 2] wb) = inst2 wb k X := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> rfl
  rw [e]; rfl

theorem inst3_bB (c k X : PTm n) : inst3 (bB wb) c k X =
    inst2 (covB (loB AK) (hiB AK actK)) c
      (pairT (Syn.subst (decX k X) KCore) (pairT (inst2 wb k X) (Syn.subst (decX k X) yCore))) := by
  have e : inst3 (bB wb) c k X = inst2 (covB (loB AK) (hiB AK actK)) c (Syn.subst ![c, k, X] (parT wb)) := by
    simp only [inst3, inst2, bB, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> rfl
  rw [e, subst_parT]

theorem inst2_uB (k X : PTm n) : inst2 (uB wb) k X = Syn.subst (decX k X) q2Core * inst2 wb k X := by
  simp only [uB, inst2, PTm.subst_mul]
  rw [subst_decX2]
  simp

/-- The covering bit at an explicit tuple. -/
theorem b_at (c k K0 M R G α γ b0 : PTm n) :
    Γ ⊢[PRAAx] inst3 (bB wb) c k (Xt K0 M R G α γ b0) ≐
      inst2 (covB (loB AK) (hiB AK actK)) c
        (pairT (Kk K0 M k) (pairT (inst2 wb k (Xt K0 M R G α γ b0)) (yk K0 M R G α γ b0 k))) := by
  rw [inst3_bB]
  exact congrInst2 _ (.eqRefl _) (congrPairT (K_at _ _ _ _ _ _ _ _) (congrPairT (.eqRefl _) (y_at _ _ _ _ _ _ _ _)))

theorem u_at (k K0 M R G α γ b0 : PTm n) :
    Γ ⊢[PRAAx] inst2 (uB wb) k (Xt K0 M R G α γ b0) ≐ Qk K0 k * Qk K0 k * inst2 wb k (Xt K0 M R G α γ b0) := by
  rw [inst2_uB]; exact congrMul (q2_at _ _ _ _ _ _ _ _) (.eqRefl _)

/-- `b² = b` at every instance. -/
theorem b_bit {m : ℕ} (Δ : List (Fm PTm m)) (c k y : PTm m) :
    Δ ⊢[PRAAx] inst3 (bB wb) c k y * inst3 (bB wb) c k y ≐ inst3 (bB wb) c k y := by
  rw [inst3_bB, show ∀ z : PTm m, inst2 (covB (loB AK) (hiB AK actK)) c z =
    sg (inst2 (oB (Foundations.IntervalCover.indB (loB AK) (hiB AK actK))) c z) from fun z => by
      simp [covB, inst2, Signum.sg]]
  refine .orE (sg_bit (Γ := Δ) (inst2 (oB (Foundations.IntervalCover.indB (loB AK) (hiB AK actK))) c
    (pairT (Syn.subst (decX k y) KCore) (pairT (inst2 wb k y) (Syn.subst (decX k y) yCore))))) ?_ ?_
  · exact (congrMul Prf.hyp0 Prf.hyp0).eqTrans ((zero_mul _).eqTrans Prf.hyp0.eqSymm)
  · exact (congrMul Prf.hyp0 Prf.hyp0).eqTrans ((one_mul _).eqTrans Prf.hyp0.eqSymm)

/-- Shifting the parameter of a scale. -/
theorem shift_P (k K0 M R G α γ b0 : PTm n) :
    Syn.shift (pairT (Kk K0 M k) (pairT (inst2 wb k (Xt K0 M R G α γ b0)) (yk K0 M R G α γ b0 k))) =
      pairT (Kk (Syn.shift K0) (Syn.shift M) (Syn.shift k))
        (pairT (inst2 wb (Syn.shift k) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α)
            (Syn.shift γ) (Syn.shift b0)))
          (yk (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0)
            (Syn.shift k))) := by
  rw [shift_pairT, shift_pairT, shift_inst2']
  simp [Syn.shift]

theorem shift_kX (k K0 M R G α γ b0 : PTm n) :
    Syn.shift (pairT k (Xt K0 M R G α γ b0)) = pairT (Syn.shift k)
      (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0)) := by
  simp only [shift_pairT]

/-- `Σ_c b(c, k) = |E_k|`. -/
theorem scale_E (k T' K0 M R G α γ b0 : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (bB wb)) k (pairT T' (Xt K0 M R G α γ b0)) ≐
      measure (loB AK) (hiB AK actK) T' (Kk K0 M k) (pairT (inst2 wb k (Xt K0 M R G α γ b0)) (yk K0 M R G α γ b0 k)) := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB (bB wb))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_colB, shift_P, shift_kX]
  exact (congrInst3 (bB wb) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (b_at wb _ _ _ _ _ _ _ _ _)

/-- `Σ_c b(c, ℓ) b(c, k) = |E_k ∩ E_ℓ|`. -/
theorem scale_inter (l k T' K0 M R G α γ b0 : PTm n) :
    Γ ⊢[PRAAx] inst3 (ppB (bB wb)) l k (pairT T' (Xt K0 M R G α γ b0)) ≐
      inter (loB AK) (hiB AK actK) (loB AK) (hiB AK actK) T' (Kk K0 M k)
        (pairT (inst2 wb k (Xt K0 M R G α γ b0)) (yk K0 M R G α γ b0 k)) (Kk K0 M l)
        (pairT (inst2 wb l (Xt K0 M R G α γ b0)) (yk K0 M R G α γ b0 l)) := by
  rw [inst3_ppB]
  refine (congrAp2 (sumF (qB (bB wb))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_qB, inst2_ovB,
    show Syn.shift (pairT (pairT l k) (Xt K0 M R G α γ b0)) = pairT (pairT (Syn.shift l) (Syn.shift k))
      (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0)) by
        simp only [shift_pairT],
    shift_pairT (pairT (Kk K0 M k) (pairT (inst2 wb k (Xt K0 M R G α γ b0)) (yk K0 M R G α γ b0 k)))
      (pairT (Kk K0 M l) (pairT (inst2 wb l (Xt K0 M R G α γ b0)) (yk K0 M R G α γ b0 l))),
    shift_P, shift_P]
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift T') :: Γ.map Fm.shift
  have h1 : Θ ⊢[PRAAx] fstT (pairT (pairT (Syn.shift l) (Syn.shift k)) (Xt (Syn.shift K0) (Syn.shift M)
      (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0))) ≐ pairT (Syn.shift l) (Syn.shift k) :=
    fst_pair _ _
  have hX : Θ ⊢[PRAAx] sndT (pairT (pairT (Syn.shift l) (Syn.shift k)) (Xt (Syn.shift K0) (Syn.shift M)
      (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0))) ≐
      Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0) :=
    snd_pair _ _
  have hl := (congrFst h1).eqTrans (fst_pair (Γ := Θ) (Syn.shift l) (Syn.shift k))
  have hk := (congrSnd h1).eqTrans (snd_pair (Γ := Θ) (Syn.shift l) (Syn.shift k))
  refine (congrMul (congrInst3 (bB wb) (.eqRefl _) hl hX) (congrInst3 (bB wb) (.eqRefl _) hk hX)).eqTrans ?_
  refine (congrMul (b_at wb _ _ _ _ _ _ _ _ _) (b_at wb _ _ _ _ _ _ _ _ _)).eqTrans ?_
  refine (mul_comm _ _).eqTrans ?_
  exact congrMul (congrInst2 _ (.eqRefl _) (fst_pair _ _).eqSymm) (congrInst2 _ (.eqRefl _) (snd_pair _ _).eqSymm)

end Bodies

/-! ## Exponent monotonicity -/

theorem pw_mono2 {K0 k B : PTm n} (h : Γ ⊢[PRAAx] le k B) : Γ ⊢[PRAAx] le (pw two (K0 + k)) (pw two (K0 + B)) := by
  have e := eq_add_of_le h
  have hs : Γ ⊢[PRAAx] K0 + B ≐ (K0 + k) + monus B k := by
    have e' := natEq e; apply deriveNat; ipra_simps; linear_combination e'
  have ea := natEq ((KhinchinBlockGeo.congrPw2 hs).eqTrans (pw_add (Γ := Γ) two (K0 + k) (monus B k)))
  have hp := DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) one (monus B k)
  have ep := natEq hp
  ipra_le 𝔞 (pw two (K0 + k)) * 𝔞 (pred (pw two (monus B k))) with ea + 𝔞 (pw two (K0 + k)) * ep

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales
