import IPRADerivations.Foundations.InvolutionPairing
import IPRADerivations.Foundations.ProductPowers
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.DiophantineNumberTheory.UnitInvolution
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.AnalyticNumberTheory.DivisorSplit
import IPRADerivations.Core.ParityArith
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# The pair product modulo a prime

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"A square test from
an involution", `eq:pair` and the nonresidue half of "Euler's criterion":

  "`2c + f = 2h`, `F ≡ a^c ∏_{x ∈ U: T(x) = x} x (mod p)`. […] If [the root scan] fails, `eq:pair` gives `c = h`
  and `a^h ≡ F`."

For a prime `p`, `gcd(a, p) = 1`, the involution `σ` of `UnitInvolution` on the indices `i < p − 1` (`x = i + 1`,
`T(x) = a x⁻¹`), and `c = Σ_i [i < σ(i)]`:

* `pair_congr`: `(p − 1)! ≡ a^c · ∏_{i<p−1} (i + 1)^{[σ(i) = i]} (mod p)`
  (`Foundations/InvolutionPairing.pair_prod`, with `(i + 1)(σ(i) + 1) ≡ a`);
* `no_fixed`: if `σ` has no fixed point, then `(p − 1)! ≡ a^h (mod p)` for `p = 2h + 1`
  (`InvolutionPairing.pair_count` gives `2c = p − 1`);
* `euler_nonresidue`: if no `x < p` has `x² ≡ a (mod p)`, stated as `exB sqB p ⟨p, a⟩ = 0` for the bit of
  `Foundations/BoundedReflection`, then `(p − 1)! ≡ a^h (mod p)`: a fixed point of `σ` would be a square root of
  `a` (`UnitInvolution.fixed_sq`).

Wilson's product `(p − 1)! ≡ p − 1`, which turns the last statement into `a^h ≡ −1`, is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PairProduct

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two one_inst inst2_mulB congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (shift_cop)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_rem_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (res)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSplit (mul_cancel)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_mul_congr2 prod_congr_mod)
open LeanProofs.IPRA.DiophantineNumberTheory.UnitInvolution (sB s_at unit_perm pair_mul fixed_sq succ_lt_of)
open LeanProofs.IPRA.Foundations.InvolutionPairing (LB EB inst2_LB inst2_EB inst2_pw pair_count pair_prod)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB ex_none one_ne_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bodies, over `0 = i`, `1 = ⟨p, a⟩` -/

/-- The unit `i + 1`. -/
abbrev idB : PTm 2 := succ (var 0)
/-- `a`. -/
abbrev aB : PTm 2 := sndT (var 1)
/-- `[x² ≡ a (mod p)]` over `0 = x`, `1 = ⟨p, a⟩`. -/
abbrev sqB : PTm 2 := eqb (rem (var 0 * var 0) (fstT (var 1))) (rem (sndT (var 1)) (fstT (var 1)))

theorem inst2_idB (i y : PTm n) : inst2 idB i y = succ i := by simp [inst2]
theorem inst2_aB (i y : PTm n) : inst2 aB i y = sndT y := by simp [inst2]
theorem inst2_sqB (x y : PTm n) :
    inst2 sqB x y = eqb (rem (x * x) (fstT y)) (rem (sndT y) (fstT y)) := by simp [inst2]

theorem sq_at (x p a : PTm n) :
    Γ ⊢[PRAAx] inst2 sqB x (pairT p a) ≐ eqb (rem (x * x) p) (rem a p) := by
  rw [inst2_sqB]
  exact congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (congrAp2 remF (snd_pair _ _) (fst_pair _ _))

/-- `∏_{i<M} (i + 1) = M!`. -/
theorem prod_id (M y : PTm n) : Γ ⊢[PRAAx] ap2 (prodF idB) M y ≐ fact M := by
  refine prod_congr_bounded idB (succ (var 0)) y zero M (.allI (.impI ?_))
  rw [inst2_idB, inst2_idB]
  exact .eqRefl _

/-! ## The pair product -/

/-- `(p − 1)! ≡ a^c · ∏_{i<p−1} (i + 1)^{[σ(i) = i]} (mod p)` with `c = Σ_{i<p−1} [i < σ(i)]`. -/
theorem pair_congr {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (ha : Γ ⊢[PRAAx] gcd a p ≐ one) :
    Γ ⊢[PRAAx] rem (fact (pred p)) p ≐
      rem (pw a (ap2 (sumF (LB sB)) (pred p) (pairT p a)) *
        ap2 (prodF (pw idB (EB sB))) (pred p) (pairT p a)) p := by
  have hp1 := p_pos (prime_two hp)
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have hp1' := p_pos (prime_two hp')
  have hc' := shift_cop hc
  have ha' := shift_cop ha
  have sM : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  obtain ⟨hr, hi, ht⟩ := unit_perm hp hc ha
  have pp := pair_prod hr hi ht idB
  have q1 : Γ ⊢[PRAAx]
      rem (ap2 (prodF (pw (idB * Permutation.FS idB sB) (LB sB))) (pred p) (pairT p a)) p ≐
        rem (ap2 (prodF (pw aB (LB sB))) (pred p) (pairT p a)) p := by
    refine prod_congr_mod _ _ hp1 (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [sM, inst2_pw, inst2_pw, inst2_mulB, Permutation.inst2_FS, inst2_idB, inst2_idB, inst2_aB]
    refine pw_rem_congr hp1'.wk ?_ _
    exact (congrAp2 remF (congrMul (.eqRefl _) (congrSucc (s_at _ _ _))) (.eqRefl _)).eqTrans
      ((pair_mul hp'.wk hc'.wk Prf.hyp0).eqTrans (congrAp2 remF (snd_pair _ _).eqSymm (.eqRefl _)))
  have q2 : Γ ⊢[PRAAx] ap2 (prodF (pw aB (LB sB))) (pred p) (pairT p a) ≐
      pw a (ap2 (sumF (LB sB)) (pred p) (pairT p a)) := by
    refine prod_pw_of (pw aB (LB sB)) (LB sB) (c := a) (x := pairT p a) (y := pairT p a) (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_pw, inst2_aB]
    exact congrPw (snd_pair _ _) (.eqRefl _)
  exact (congrAp2 remF ((prod_id _ _).eqSymm.eqTrans pp) (.eqRefl _)).eqTrans
    (rem_mul_congr2 hp1 (q1.eqTrans (congrAp2 remF q2 (.eqRefl _)))
      (.eqRefl (rem (ap2 (prodF (pw idB (EB sB))) (pred p) (pairT p a)) p)))

/-! ## No fixed points -/

theorem count_alg {c e M p h : PTm n} (pc : Γ ⊢[PRAAx] c + c + e ≐ M) (se : Γ ⊢[PRAAx] e ≐ zero)
    (ep : Γ ⊢[PRAAx] p ≐ two * h + one) (hp1 : Γ ⊢[PRAAx] p ≐ succ M) : Γ ⊢[PRAAx] two * c ≐ two * h := by
  ipra_lc natEq pc - natEq se + natEq ep - natEq hp1

alias mul_one_r := Common.mul_one_right

/-- If `σ` has no fixed point below `p − 1`, then `(p − 1)! ≡ a^h (mod p)` for an odd prime `p = 2h + 1`. -/
theorem no_fixed {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (ha : Γ ⊢[PRAAx] gcd a p ≐ one)
    (hE : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (pred p)) ⟶
      (inst2 (EB sB) (var 0) (Syn.shift (pairT p a)) ≐ zero))) :
    Γ ⊢[PRAAx] rem (fact (pred p)) p ≐ rem (pw a (half p)) p := by
  have hp1 := p_pos (prime_two hp)
  obtain ⟨hr, hi, ht⟩ := unit_perm hp hc ha
  have pe : Γ ⊢[PRAAx] ap2 (prodF (pw idB (EB sB))) (pred p) (pairT p a) ≐ one := by
    refine (prod_congr_bounded _ (one : PTm 2) (pairT p a) (pairT p a) (pred p) (.allI (.impI ?_))).eqTrans
      (prod_one _ _)
    rw [inst2_pw, one_inst]
    exact (congrPw (.eqRefl _) (Prf.impE hE.allOpen.wk Prf.hyp0)).eqTrans (pw_zero _)
  have se : Γ ⊢[PRAAx] ap2 (sumF (EB sB)) (pred p) (pairT p a) ≐ zero := sum_zero_of_bounded _ _ _ hE
  have pc := pair_count hr hi ht
  have cnt : Γ ⊢[PRAAx] ap2 (sumF (LB sB)) (pred p) (pairT p a) ≐ half p :=
    mul_cancel (congrSucc (pred_succ _).eqSymm) (count_alg pc se (odd_of hodd) hp1)
  exact (pair_congr hp hc ha).eqTrans (congrAp2 remF
    ((congrMul (congrPw (.eqRefl _) cnt) pe).eqTrans (mul_one_r _)) (.eqRefl _))

/-- If no `x < p` has `x² ≡ a (mod p)`, then `(p − 1)! ≡ a^h (mod p)` for an odd prime `p = 2h + 1` and
`gcd(a, p) = 1`. -/
theorem euler_nonresidue {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (ha : Γ ⊢[PRAAx] gcd a p ≐ one)
    (hnr : Γ ⊢[PRAAx] exB sqB p (pairT p a) ≐ zero) :
    Γ ⊢[PRAAx] rem (fact (pred p)) p ≐ rem (pw a (half p)) p := by
  refine no_fixed hp hodd hc ha (.allI (.impI ?_))
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have hp1' := p_pos (prime_two hp')
  have hc' := shift_cop hc
  have ha' := shift_cop ha
  have hnr' : (Γ.map Fm.shift) ⊢[PRAAx] exB sqB (Syn.shift p) (pairT (Syn.shift p) (Syn.shift a)) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using hnr.shift
  have sM : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  simp only [shift_pairT]
  rw [sM, inst2_EB]
  refine .orE (eq_or_ne (var 0) (inst2 sB (var 0) (pairT (Syn.shift p) (Syn.shift a)))) ?_ (eqb_of_ne Prf.hyp0)
  let C : List (Fm PTm (n + 1)) :=
    ((var 0 : PTm (n + 1)) ≐ inst2 sB (var 0) (pairT (Syn.shift p) (Syn.shift a))) ::
      lt (var 0) (pred (Syn.shift p)) :: Γ.map Fm.shift
  have hi : C ⊢[PRAAx] lt (var 0) (pred (Syn.shift p)) := Prf.hyp1
  have e : C ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ pred (res (succ (var 0)) (Syn.shift p) (Syn.shift a)) :=
    (Prf.hyp0 : C ⊢[PRAAx] _).eqTrans (s_at _ _ _)
  have fs := fixed_sq hp'.wk.wk hc'.wk.wk hi e
  have z := ex_none sqB hnr'.wk.wk (succ_lt_of hp1'.wk.wk hi)
  exact one_ne_zero _ ((eqb_of_eq fs).eqSymm.eqTrans ((sq_at _ _ _).eqSymm.eqTrans z))

end LeanProofs.IPRA.DiophantineNumberTheory.PairProduct
