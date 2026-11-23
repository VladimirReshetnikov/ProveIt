import IPRADerivations.DiophantineNumberTheory.QuadraticReciprocity

/-!
# The first supplementary law and the square-root witnesses

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"Supplementary laws
and witnesses": `eq:minusone`, "Obtaining the promised root", and the shorter witness for `p = 4t + 3`.

With `signBit p a` the bit of "no `x < p` has `x² ≡ a (mod p)`" and `rb p a = 1 − signBit p a` the bit of the
bounded search (`QuadraticReciprocity.sign_eq`):

* `rb_of_sign_zero`, `rb_of_sign_one`: the two values of the sign bit in terms of the search bit;
* `root_of_sign`: if `signBit p a = 0`, the search returns `x = wit < p` with `x² ≡ a (mod p)` ("the term
  `x = root(p, q)` satisfies `x < p` and `x² ≡ q`");
* `no_root_of_sign`: if `signBit p a = 1`, no `x < p` has `x² ≡ a (mod p)`;
* `minus_one_law` (`eq:minusone`): `signBit p (p − 1) = par ⌊p/2⌋` for an odd prime `p`, that is
  `(−1/p) = (−1)^{(p−1)/2}`. It is read off Euler's criterion: `(p − 1)^h` is `1` or `p − 1` by the parity of `h`
  (`ResidueFacts.neg_pow`). (The paper obtains it from Gauss's lemma with `N_p(p − 1) = h`.)
* `short_root`: for `p = 4t + 3` (as `⌊p/2⌋ = 2t + 1`) and a square unit `a`, `x = a^{t+1} mod p` has
  `x² ≡ a (mod p)`: `x² ≡ a · a^h ≡ a`.

The second supplementary law `eq:two` is derived in `SecondSupplement`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.QuadraticSupplements

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_comm_one)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_mul_congr2)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal (signBit)
open LeanProofs.IPRA.DiophantineNumberTheory.UnitInvolution (unit_of_lt)
open LeanProofs.IPRA.DiophantineNumberTheory.PairProduct (sqB sq_at)
open LeanProofs.IPRA.DiophantineNumberTheory.WilsonProduct (pred_lt pred_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts (neg_pow)
open LeanProofs.IPRA.DiophantineNumberTheory.GaussLemma (rb euler_nr euler_res pred_ne_one)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocity (sign_eq)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim ex_none eqb_cases eq_of_eqb one_ne_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The sign bit and the search bit -/

/-- `signBit p a = 0` gives `rb p a = 1`. -/
theorem rb_of_sign_zero {p a : PTm n} (h : Γ ⊢[PRAAx] signBit p a ≐ zero) : Γ ⊢[PRAAx] rb p a ≐ one := by
  refine .orE (ex_cases sqB p (pairT p a)) ?_ Prf.hyp0
  have hnr : ((rb p a ≐ zero) :: Γ) ⊢[PRAAx] rb p a ≐ zero := Prf.hyp0
  have s1 : ((rb p a ≐ zero) :: Γ) ⊢[PRAAx] signBit p a ≐ one :=
    (sign_eq p a).eqTrans ((congrMonus (.eqRefl _) hnr).eqTrans (monus_zero _))
  exact one_ne_zero _ (s1.eqSymm.eqTrans h.wk)

/-- `signBit p a = 1` gives `rb p a = 0`. -/
theorem rb_of_sign_one {p a : PTm n} (h : Γ ⊢[PRAAx] signBit p a ≐ one) : Γ ⊢[PRAAx] rb p a ≐ zero := by
  refine .orE (ex_cases sqB p (pairT p a)) Prf.hyp0 ?_
  have hr : ((rb p a ≐ one) :: Γ) ⊢[PRAAx] rb p a ≐ one := Prf.hyp0
  have s0 : ((rb p a ≐ one) :: Γ) ⊢[PRAAx] signBit p a ≐ zero :=
    (sign_eq p a).eqTrans ((congrMonus (.eqRefl _) hr).eqTrans (monus_self _))
  exact one_ne_zero _ (h.wk.eqSymm.eqTrans s0)

/-- The witness of the search is a square root: `rb p a = 1` gives `wit < p` and `wit² ≡ a (mod p)`. -/
theorem wit_sq {p a : PTm n} (hr : Γ ⊢[PRAAx] rb p a ≐ one) :
    Γ ⊢[PRAAx] lt (wit sqB p (pairT p a)) p ⋏
      (rem (wit sqB p (pairT p a) * wit sqB p (pairT p a)) p ≐ rem a p) := by
  have ee := ex_elim sqB hr
  have ne : Γ ⊢[PRAAx] neg (eqb (rem (wit sqB p (pairT p a) * wit sqB p (pairT p a)) p) (rem a p) ≐ zero) :=
    .impI (.impE (Prf.andE₂ ee).wk ((sq_at _ _ _).eqTrans Prf.hyp0))
  refine .andI (Prf.andE₁ ee) ?_
  refine .orE (eqb_cases (rem (wit sqB p (pairT p a) * wit sqB p (pairT p a)) p) (rem a p)) ?_ ?_
  · exact .botE _ (.impE ne.wk Prf.hyp0)
  · exact eq_of_eqb Prf.hyp0

/-- "Obtaining the promised root": `signBit p a = 0` gives the root `x = wit < p`, `x² ≡ a (mod p)`. -/
theorem root_of_sign {p a : PTm n} (h : Γ ⊢[PRAAx] signBit p a ≐ zero) :
    Γ ⊢[PRAAx] lt (wit sqB p (pairT p a)) p ⋏
      (rem (wit sqB p (pairT p a) * wit sqB p (pairT p a)) p ≐ rem a p) :=
  wit_sq (rb_of_sign_zero h)

/-- `signBit p a = 1` excludes every root below `p`. -/
theorem no_root_of_sign {p a x : PTm n} (h : Γ ⊢[PRAAx] signBit p a ≐ one) (hx : Γ ⊢[PRAAx] lt x p) :
    Γ ⊢[PRAAx] neg (rem (x * x) p ≐ rem a p) := by
  have z := ex_none sqB (rb_of_sign_one h) hx
  exact .impI (one_ne_zero _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans ((sq_at _ _ _).eqSymm.eqTrans z.wk)))

/-! ## The first supplementary law -/

/-- `eq:minusone`: `signBit p (p − 1) = par ⌊p/2⌋` for an odd prime `p`. -/
theorem minus_one_law {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one) :
    Γ ⊢[PRAAx] signBit p (pred p) ≐ par (half p) := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have ha : Γ ⊢[PRAAx] gcd (pred p) p ≐ one := unit_of_lt hp (pred_pos hq) (pred_lt hp1)
  have hc : Γ ⊢[PRAAx] gcd p (pred p) ≐ one := gcd_comm_one hp1 ha
  have r1 : Γ ⊢[PRAAx] rem one p ≐ one := rem_small hq
  have rp : Γ ⊢[PRAAx] rem (pred p) p ≐ pred p := rem_small (pred_lt hp1)
  refine .orE (neg_pow hq (half p)) ?_ ?_
  · -- `h` even: `(p − 1)^h ≡ 1`, so `p − 1` is a residue
    let C : List (Fm PTm n) := ((par (half p) ≐ zero) ⋏ (rem (pw (pred p) (half p)) p ≐ rem one p)) :: Γ
    have hc0 : C ⊢[PRAAx] (par (half p) ≐ zero) ⋏ (rem (pw (pred p) (half p)) p ≐ rem one p) := Prf.hyp0
    have hr : C ⊢[PRAAx] rb p (pred p) ≐ one := by
      refine .orE (ex_cases sqB p (pairT p (pred p))) ?_ Prf.hyp0
      have en := euler_nr (Γ := (rb p (pred p) ≐ zero) :: C) hp.wk.wk hodd.wk.wk hc.wk.wk ha.wk.wk Prf.hyp0
      exact pred_ne_one hp1.wk.wk hodd.wk.wk _ (en.eqSymm.eqTrans ((Prf.andE₂ hc0).wk.eqTrans r1.wk.wk))
    exact (sign_eq p (pred p)).eqTrans (((congrMonus (.eqRefl _) hr).eqTrans (monus_self _)).eqTrans
      (Prf.andE₁ hc0).eqSymm)
  · -- `h` odd: `(p − 1)^h ≡ p − 1`, so `p − 1` is a nonresidue
    let C : List (Fm PTm n) := ((par (half p) ≐ one) ⋏ (rem (pw (pred p) (half p)) p ≐ rem (pred p) p)) :: Γ
    have hc1 : C ⊢[PRAAx] (par (half p) ≐ one) ⋏ (rem (pw (pred p) (half p)) p ≐ rem (pred p) p) := Prf.hyp0
    have hnr : C ⊢[PRAAx] rb p (pred p) ≐ zero := by
      refine .orE (ex_cases sqB p (pairT p (pred p))) Prf.hyp0 ?_
      have er := euler_res (Γ := (rb p (pred p) ≐ one) :: C) hp.wk.wk hodd.wk.wk ha.wk.wk Prf.hyp0
      exact pred_ne_one hp1.wk.wk hodd.wk.wk _
        (rp.wk.wk.eqSymm.eqTrans ((Prf.andE₂ hc1).wk.eqSymm.eqTrans (er.eqTrans r1.wk.wk)))
    exact (sign_eq p (pred p)).eqTrans (((congrMonus (.eqRefl _) hnr).eqTrans (monus_zero _)).eqTrans
      (Prf.andE₁ hc1).eqSymm)

/-! ## The short witness for `p = 4t + 3` -/

theorem exp_alg (t : PTm n) : Γ ⊢[PRAAx] succ t + succ t ≐ (two * t + one) + one := by
  apply deriveNat; ipra_simps; ring

theorem one_mul_r (a : PTm n) : Γ ⊢[PRAAx] one * a ≐ a := one_mul a

/-- For `⌊p/2⌋ = 2t + 1` (`p = 4t + 3`) and a square unit `a`: `x = a^{t+1} mod p` has `x² ≡ a (mod p)`. -/
theorem short_root {p a t : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (ht : Γ ⊢[PRAAx] half p ≐ two * t + one) (ha : Γ ⊢[PRAAx] gcd a p ≐ one)
    (hr : Γ ⊢[PRAAx] rb p a ≐ one) :
    Γ ⊢[PRAAx] rem (rem (pw a (succ t)) p * rem (pw a (succ t)) p) p ≐ rem a p := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have er := euler_res hp hodd ha hr
  have rr : Γ ⊢[PRAAx] rem (rem (pw a (succ t)) p) p ≐ rem (pw a (succ t)) p :=
    rem_small (AnalyticNumberTheory.Multiplicative.rem_lt' hp1 _)
  have s1 := rem_mul_congr2 hp1 rr rr
  have e : Γ ⊢[PRAAx] pw a (succ t) * pw a (succ t) ≐ pw a (half p) * a :=
    (pw_add a (succ t) (succ t)).eqSymm.eqTrans ((congrPw (.eqRefl _)
      ((exp_alg t).eqTrans (congrAdd ht.eqSymm (.eqRefl _)))).eqTrans
      ((pw_add a (half p) one).eqTrans (congrMul (.eqRefl _) (pw_one a))))
  have s2 := rem_mul_congr2 hp1 er (.eqRefl (rem a p))
  exact s1.eqTrans ((congrAp2 remF e (.eqRefl _)).eqTrans (s2.eqTrans (congrAp2 remF (one_mul a) (.eqRefl _))))

end LeanProofs.IPRA.DiophantineNumberTheory.QuadraticSupplements
