import IPRADerivations.DiophantineNumberTheory.FoldedPermutation
import IPRADerivations.AnalyticNumberTheory.LcmBridgeExact
import IPRADerivations.Combinatorics.BellTouchard
import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Foundations.SignedSums

/-!
# Gauss's product

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"From products to
floor sums":

  "`a i ≡ (−1)^{e_i} b_i (mod p)` […] `∏ b_i = h!` […] Multiplying over `i` gives
  `a^h h! ≡ (−1)^{N_p(a)} h!`. The product `h!` has an inverse, obtained by multiplying the inverses of its
  factors."

The sign `−1` is the residue `p − 1`, so no negative numbers are needed: with `r_i = a i mod p`,
`e_i = [r_i > h]`, `b_i = min(r_i, p − r_i)`,

  `(p − 1)^{e_i} r_i ≡ b_i (mod p)`                                                          (`c_pt`),

and multiplying over `1 ≤ i ≤ h`, for an odd `p = 2h + 1`, `gcd(p, a) = 1` and an inverse `a'` of `a`,

  `(p − 1)^{N_p(a)} · (h! · a^h) ≡ h! (mod p)`                                               (`gauss_product`).

For a prime `p` the factor `h!` is cancelled (`Combinatorics/BellTouchard.not_dvd_fact`):

  `(p − 1)^{N_p(a)} · a^h ≡ 1 (mod p)`                                                        (`gauss_unit`),

which is `a^h ≡ (−1)^{N_p(a)}`.

The proof uses the multiplicative half of `eq:perm`, `∏ b_i = h!` (`Core/Permutation.prod_perm` with
`FoldedPermutation.perm_data`), the product of powers (`Euler.prod_pw`), products of two bodies
(`LcmBridgeExact.prod_mul`) and products of congruent bodies (`ModularCertificate.prod_congr_mod`).

Not derived: Euler's criterion `eq:euler`, and with it Gauss's lemma `eq:gauss` as a statement about the residue
symbol `signBit`.

* `big_alg`: `(p − 1) r = p (r − 1) + (p − r)`;
* `cancel_unit`: `u x ≡ u y (mod p)` gives `x ≡ y` for `gcd(u, p) = 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.GaussProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg prime_two inst2_mulB)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (shift_cop prod_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeExact (prod_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (inv inv_spec inv_cop mul_inv_rem)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_comm_one)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul rem_mul_congr2 prod_congr_mod)
open LeanProofs.IPRA.DiophantineNumberTheory.FoldedResidues (fold fold_small fold_large rem_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.FoldedPermutation (bF congrBF sB tB perm_data b_eq_succ_s)
open LeanProofs.IPRA.DiophantineNumberTheory.EisensteinParity (rV eV bV rB eB bB mB idB inst2_rB inst2_eB inst2_bB
  inst2_mB inst2_idB)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The pointwise congruence -/

/-- `(p − 1) r = p (r − 1) + (p − r)` for `p, r ≥ 1`. -/
theorem big_alg {p pp R pr M : PTm n} (xp : Γ ⊢[PRAAx] p ≐ succ pp) (xR : Γ ⊢[PRAAx] R ≐ succ pr)
    (xM : Γ ⊢[PRAAx] p ≐ R + M) : Γ ⊢[PRAAx] pp * R ≐ p * pr + M := by
  have a := natEq xp; have b := natEq xR; have c := natEq xM
  apply deriveNat; ipra_simps
  linear_combination c - 𝔞 R * a + 𝔞 p * b

/-- `(p − 1)^{e_i} r_i`. -/
abbrev cV (i p a : PTm n) : PTm n := pw (pred p) (eV i p a) * rV i p a

/-- `cV` over `0 = i`, `1 = p`, `2 = a`. -/
abbrev cV3 : PTm 3 := cV (var 0) (var 1) (var 2)

theorem inst3_cV3 (i p a : PTm n) : inst3 cV3 i p a = cV i p a := by simp [inst3, subst_ap1]

theorem congrC {i i' p p' a a' : PTm n} (h₁ : Γ ⊢[PRAAx] i ≐ i') (h₂ : Γ ⊢[PRAAx] p ≐ p')
    (h₃ : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] cV i p a ≐ cV i' p' a' := by
  have e := congrInst3 cV3 h₁ h₂ h₃
  rw [inst3_cV3 i p a, inst3_cV3 i' p' a'] at e
  exact e

/-- `(p − 1)^{e_i} r_i ≡ b_i (mod p)` for `i < h`, `p = 2h + 1`, `gcd(p, a) = 1`. -/
theorem c_pt {p a i : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (hi : Γ ⊢[PRAAx] lt i (half p)) : Γ ⊢[PRAAx] rem (cV i p a) p ≐ rem (bF i p a) p := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * half p) (ep.eqTrans (by apply deriveNat; ipra_simps; ring))
  have hR1 := rem_pos ep hc hi
  have hRp : Γ ⊢[PRAAx] lt (rV i p a) p := rem_lt' hp1 _
  refine .orE (lt_or_le (half p) (rV i p a)) ?_ ?_
  · let C : List (Fm PTm n) := lt (half p) (rV i p a) :: Γ
    have hl : C ⊢[PRAAx] lt (half p) (rV i p a) := Prf.hyp0
    have hE : C ⊢[PRAAx] eV i p a ≐ one := by
      refine .orE (zero_or_succ (monus (rV i p a) (half p))) ?_ (sg_pos Prf.hyp0)
      exact not_succ_le_self (half p) _ (le_trans hl.wk (Prf.hyp0 :
        ((monus (rV i p a) (half p) ≐ zero) :: C) ⊢[PRAAx] le (rV i p a) (half p)))
    have eM : C ⊢[PRAAx] p ≐ rV i p a + monus p (rV i p a) := eq_add_of_le (le_of_lt hRp.wk)
    have k := big_alg hp1.wk hR1.wk eM
    have c1 : C ⊢[PRAAx] cV i p a ≐ pred p * rV i p a :=
      congrMul ((congrPw (.eqRefl _) hE).eqTrans (pw_one _)) (.eqRefl _)
    exact (congrAp2 remF (c1.eqTrans k) (.eqRefl _)).eqTrans ((rem_add_mul hp1.wk _ _).eqTrans
      (congrAp2 remF (fold_large hl).eqSymm (.eqRefl _)))
  · let C : List (Fm PTm n) := le (rV i p a) (half p) :: Γ
    have hs : C ⊢[PRAAx] le (rV i p a) (half p) := Prf.hyp0
    have hE : C ⊢[PRAAx] eV i p a ≐ zero := (congrSg hs).eqTrans sg_zero
    have c1 : C ⊢[PRAAx] cV i p a ≐ rV i p a :=
      (congrMul ((congrPw (.eqRefl _) hE).eqTrans (pw_zero _)) (.eqRefl _)).eqTrans (one_mul _)
    exact congrAp2 remF (c1.eqTrans (fold_small hs).eqSymm) (.eqRefl _)

/-! ## The bodies, over `0 = i`, `1 = ⟨p, a⟩` -/

/-- `(p − 1)^{e_i}`. -/
abbrev pwB : PTm 2 := pw (pred (fstT (var 1))) eB
/-- `(p − 1)^{e_i} r_i`. -/
abbrev cB : PTm 2 := pwB * rB
/-- `a`. -/
abbrev aB : PTm 2 := sndT (var 1)

theorem inst2_pwB (i x : PTm n) : inst2 pwB i x = pw (pred (fstT x)) (inst2 eB i x) := by
  simp [inst2, subst_ap1]

theorem inst2_aB (i x : PTm n) : inst2 aB i x = sndT x := by simp [inst2]

theorem inst2_pwfst (e : PTm 2) (i y : PTm n) :
    inst2 (pw (fstT (var 1)) e) i y = pw (fstT y) (inst2 e i y) := by simp [inst2]

theorem c_at (i p a : PTm n) : Γ ⊢[PRAAx] inst2 cB i (pairT p a) ≐ cV i p a := by
  rw [inst2_mulB, inst2_pwB, inst2_eB, inst2_rB]
  exact congrC (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

theorem b_at (i p a : PTm n) : Γ ⊢[PRAAx] inst2 bB i (pairT p a) ≐ bF i p a := by
  rw [inst2_bB]
  exact congrBF (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

/-! ## Cancellation -/

theorem swap_alg (v u x : PTm n) : Γ ⊢[PRAAx] v * (u * x) ≐ u * v * x := by
  apply deriveNat; ipra_simps; ring

/-- `u x ≡ u y (mod p)` gives `x ≡ y (mod p)` for `gcd(u, p) = 1`, `p ≥ 2`. -/
theorem cancel_unit {u x y p : PTm n} (hq : Γ ⊢[PRAAx] le two p) (hu : Γ ⊢[PRAAx] gcd u p ≐ one)
    (h : Γ ⊢[PRAAx] rem (u * x) p ≐ rem (u * y) p) : Γ ⊢[PRAAx] rem x p ≐ rem y p := by
  have hp1 := p_pos hq
  have a := rem_mul_congr2 hp1 (.eqRefl (rem (inv u p) p)) h
  have bx : Γ ⊢[PRAAx] rem (inv u p * (u * x)) p ≐ rem x p :=
    (congrAp2 remF (swap_alg _ _ _) (.eqRefl _)).eqTrans (mul_inv_rem hq hu x)
  have by' : Γ ⊢[PRAAx] rem (inv u p * (u * y)) p ≐ rem y p :=
    (congrAp2 remF (swap_alg _ _ _) (.eqRefl _)).eqTrans (mul_inv_rem hq hu y)
  exact bx.eqSymm.eqTrans (a.eqTrans by')

/-! ## The product -/

/-- `∏_{i<h} (i + 1) = h!`, with any parameter. -/
theorem prod_id (h x : PTm n) : Γ ⊢[PRAAx] ap2 (prodF idB) h x ≐ fact h := by
  refine prod_congr_bounded idB (succ (var 0)) x zero h (.allI (.impI ?_))
  rw [inst2_idB, inst2_idB]
  exact .eqRefl _

/-- `(p − 1)^{N_p(a)} · (h! · a^h) ≡ h! (mod p)` for `p = 2h + 1`, `h ≥ 1`, `gcd(p, a) = gcd(p, a') = 1`,
`a a' ≡ 1 (mod p)`. -/
theorem gauss_product {p a a' : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one)
    (hh : Γ ⊢[PRAAx] half p ≐ succ (pred (half p)))
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (hc' : Γ ⊢[PRAAx] gcd p a' ≐ one)
    (hinv : Γ ⊢[PRAAx] rem (a * a') p ≐ rem one p) :
    Γ ⊢[PRAAx] rem (pw (pred p) (ap2 (sumF eB) (half p) (pairT p a)) * (fact (half p) * pw a (half p))) p ≐
      rem (fact (half p)) p := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * half p) (ep.eqTrans (by apply deriveNat; ipra_simps; ring))
  have sH : Syn.shift (half p) = half (Syn.shift p) := by simp [Syn.shift, subst_ap1]
  have sP : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  have ep' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ two * half (Syn.shift p) + one := by
    simpa [Fm.shift, Syn.shift, subst_ap1] using ep.shift
  have hp1' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hp1.shift
  have hcS := shift_cop hc
  -- `∏ (p − 1)^{e_i} r_i ≡ ∏ b_i`
  have P2 : Γ ⊢[PRAAx] rem (ap2 (prodF cB) (half p) (pairT p a)) p ≐
      rem (ap2 (prodF bB) (half p) (pairT p a)) p := by
    refine prod_congr_mod cB bB hp1 (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [sH]
    exact (congrAp2 remF (c_at _ _ _) (.eqRefl _)).eqTrans ((c_pt ep'.wk hcS.wk Prf.hyp0).eqTrans
      (congrAp2 remF (b_at _ _ _) (.eqRefl _)).eqSymm)
  have P3 := prod_mul (Γ := Γ) pwB rB (half p) (pairT p a)
  -- `∏ (p − 1)^{e_i} = (p − 1)^N`
  have t1 : Γ ⊢[PRAAx] ap2 (prodF pwB) (half p) (pairT p a) ≐
      ap2 (prodF (pw (fstT (var 1)) (sndB eB))) (half p) (pairT (pred p) (pairT p a)) := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [sP, inst2_pwB, inst2_pwfst, inst2_sndB]
    exact congrPw ((congrPred (fst_pair _ _)).eqTrans (fst_pair _ _).eqSymm)
      (congrInst2 eB (.eqRefl _) (snd_pair _ _)).eqSymm
  have t2 : Γ ⊢[PRAAx] ap2 (sumF (sndB eB)) (half p) (pairT (pred p) (pairT p a)) ≐
      ap2 (sumF eB) (half p) (pairT p a) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_sndB]
    exact congrInst2 eB (.eqRefl _) (snd_pair _ _)
  have P4 : Γ ⊢[PRAAx] ap2 (prodF pwB) (half p) (pairT p a) ≐
      pw (pred p) (ap2 (sumF eB) (half p) (pairT p a)) :=
    t1.eqTrans ((prod_pw (sndB eB) (half p) (pairT (pred p) (pairT p a))).eqTrans (congrPw (fst_pair _ _) t2))
  -- `∏ r_i ≡ ∏ (i + 1) a = h! a^h`
  have P5 : Γ ⊢[PRAAx] rem (ap2 (prodF rB) (half p) (pairT p a)) p ≐
      rem (ap2 (prodF mB) (half p) (pairT p a)) p := by
    refine prod_congr_mod rB mB hp1 (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_rB, inst2_mB]
    exact (congrAp2 remF (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _)).eqTrans
      (rem_small (rem_lt' hp1'.wk _))
  have f2 : Γ ⊢[PRAAx] ap2 (prodF aB) (half p) (pairT p a) ≐ pw a (half p) := by
    refine prod_const_of aB (half p) a (pairT p a) (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_aB]
    exact snd_pair _ _
  have P6 : Γ ⊢[PRAAx] ap2 (prodF mB) (half p) (pairT p a) ≐ fact (half p) * pw a (half p) :=
    (prod_mul idB aB (half p) (pairT p a)).eqTrans (congrMul (prod_id _ _) f2)
  -- `∏ b_i = h!`
  obtain ⟨hr, hi, ht⟩ := perm_data ep hh hc hc' hinv
  have pp := Permutation.prod_perm (F := idB) hr hi ht
  have l : Γ ⊢[PRAAx] ap2 (prodF bB) (half p) (pairT p a) ≐
      ap2 (prodF (Permutation.FS idB sB)) (half p) (pairT p (pairT a a')) := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [sH]
    exact b_eq_succ_s ep'.wk hcS.wk Prf.hyp0
  have P7 : Γ ⊢[PRAAx] ap2 (prodF bB) (half p) (pairT p a) ≐ fact (half p) :=
    l.eqTrans (pp.eqTrans (prod_id _ _))
  -- assembly
  have u1 : Γ ⊢[PRAAx] rem (pw (pred p) (ap2 (sumF eB) (half p) (pairT p a)) *
      ap2 (prodF rB) (half p) (pairT p a)) p ≐ rem (fact (half p)) p :=
    (congrAp2 remF ((congrMul P4 (.eqRefl _)).eqSymm.eqTrans P3.eqSymm) (.eqRefl _)).eqTrans
      (P2.eqTrans (congrAp2 remF P7 (.eqRefl _)))
  have u2 := rem_mul_congr2 hp1
    (.eqRefl (rem (pw (pred p) (ap2 (sumF eB) (half p) (pairT p a))) p))
    (P5.eqTrans (congrAp2 remF P6 (.eqRefl _)))
  exact u2.eqSymm.eqTrans u1

/-! ## The prime case -/

theorem half_lt {p h : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * h + one) : Γ ⊢[PRAAx] lt h p := by
  have x := natEq ep
  ipra_le 𝔞 h with x

theorem shuffle (A F Pw : PTm n) : Γ ⊢[PRAAx] A * (F * Pw) ≐ F * (A * Pw) := by
  apply deriveNat; ipra_simps; ring

theorem mul_one_r (F : PTm n) : Γ ⊢[PRAAx] F ≐ F * one := by apply deriveNat; ipra_simps; ring

/-- `(p − 1)^{N_p(a)} · a^h ≡ 1 (mod p)` for an odd prime `p = 2h + 1`, `a ≥ 1` and `gcd(p, a) = 1`:
`a^h ≡ (−1)^{N_p(a)}`. -/
theorem gauss_unit {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (ha1 : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hc : Γ ⊢[PRAAx] gcd p a ≐ one) :
    Γ ⊢[PRAAx] rem (pw (pred p) (ap2 (sumF eB) (half p) (pairT p a)) * pw a (half p)) p ≐ rem one p := by
  have ep := odd_of hodd
  have hq := prime_two hp
  have hp1 := p_pos hq
  have hh : Γ ⊢[PRAAx] half p ≐ succ (pred (half p)) := by
    refine .orE (zero_or_succ (half p)) ?_ Prf.hyp0
    have e1 : ((half p ≐ zero) :: Γ) ⊢[PRAAx] p ≐ one :=
      ep.wk.eqTrans ((congrAdd ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans
        (zero_add _))
    exact not_succ_le_self one _ (le_congr (.eqRefl _) e1 hq.wk)
  have hD : Γ ⊢[PRAAx] gcd a p ≐ one := gcd_comm_one ha1 hc
  have hc' : Γ ⊢[PRAAx] gcd p (inv a p) ≐ one := gcd_comm_one hp1 (inv_cop hq hD)
  have g := gauss_product ep hh hc hc' (inv_spec hq hD)
  have nd := Combinatorics.BellTouchard.not_dvd_fact hp (half p) (half_lt ep)
  have hu : Γ ⊢[PRAAx] gcd (fact (half p)) p ≐ one := gcd_comm_one (fact_pos _) (gcd_prime hp nd)
  refine cancel_unit hq hu ?_
  exact (congrAp2 remF (shuffle _ _ _) (.eqRefl _)).eqSymm.eqTrans
    (g.eqTrans (congrAp2 remF (mul_one_r _) (.eqRefl _)))

end LeanProofs.IPRA.DiophantineNumberTheory.GaussProduct
