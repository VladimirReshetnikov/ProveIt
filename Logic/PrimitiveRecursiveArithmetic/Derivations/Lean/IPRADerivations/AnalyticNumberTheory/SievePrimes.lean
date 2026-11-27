import IPRADerivations.AnalyticNumberTheory.SieveMajorant

/-!
# From the sifted count to the count of primes in the progression

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the last step of the proof
of `thm:finite-sieve`: the primes `p ≤ x` of the progression that exceed `z` are counted by the sifted sum, and the
primes up to `z` contribute at most `z`; this is the summand `z` of `x/(q G) + z² + z`.

With `S = Σ_{m<X} [m ≡ a (mod q)] ρ(m)`, where `ρ(m) = rgh Z m` is the indicator of having no divisor in `[2, Z)`
(the body `SieveMajorant.S0`), and the prime indicator `isP`:

* `prime_ndvd`: a prime `p` is not divisible by any `d` with `2 ≤ d < p`;
* `rough_of_prime`: a prime `m ≥ Z` has no divisor in `[2, Z)`;
* `lowB`, `count_below`: `Σ_{m<X} [m < Z] ≤ Z`;
* `prime_pt`: `c · [m prime] ≤ c · ρ(m) + [m < Z]` for `c ≤ 1`;
* `primes_le`: `Σ_{m<X} [m ≡ a (mod q)] [m prime] ≤ S + Z`, i.e. `π(X; q, a) ≤ S + Z`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SievePrimes

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (cB inst2_cB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveRough (rB inst2_rB rgh)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveMajorant (S0 S0_at)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Primes have no small divisors -/

/-- A prime `p` is not divisible by any `d` with `2 ≤ d < p`. -/
theorem prime_ndvd {p d : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h2 : Γ ⊢[PRAAx] le two d)
    (hd : Γ ⊢[PRAAx] lt d p) : Γ ⊢[PRAAx] neg (dvd d p) := by
  have hp' := hp
  unfold prime at hp'
  have hall := Prf.allE d (Prf.andE₂ hp')
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hall
  exact .impE (.impE hall h2) hd

/-- For a prime `m ≥ Z` and `d < Z`: `[d ≥ 2][d ∣ m] = 0`. -/
theorem rB_zero {Z m d : PTm n} (hP : Γ ⊢[PRAAx] isP m ≐ one) (hZm : Γ ⊢[PRAAx] le Z m)
    (hd : Γ ⊢[PRAAx] lt d Z) : Γ ⊢[PRAAx] inst2 rB d m ≐ zero := by
  rw [inst2_rB]
  refine .orE (lt_or_le d two) ?_ ?_
  · have h1 : (lt d two :: Γ) ⊢[PRAAx] monus d one ≐ zero := (succ_monus_succ d one).eqSymm.eqTrans Prf.hyp0
    exact zero_mul_l ((congrSg h1).eqTrans sg_zero) _
  · have h2 : (le two d :: Γ) ⊢[PRAAx] le two d := Prf.hyp0
    have hp : (le two d :: Γ) ⊢[PRAAx] prime m := prime_of_isP (hP.wk (ψ := le two d))
    have nd := prime_ndvd hp h2 (lt_of_lt_of_le (hd.wk (ψ := le two d)) (hZm.wk (ψ := le two d)))
    exact (congrMul (.eqRefl _) (eqb_of_ne nd)).eqTrans (mul_zero _)

/-- A prime `m ≥ Z` has no divisor in `[2, Z)`. -/
theorem rough_of_prime {Z m : PTm n} (hP : Γ ⊢[PRAAx] isP m ≐ one) (hZm : Γ ⊢[PRAAx] le Z m) :
    Γ ⊢[PRAAx] ap2 (sumF rB) Z m ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  have hP' : (Γ.map Fm.shift) ⊢[PRAAx] isP (Syn.shift m) ≐ one := by
    have h := hP.shift
    simp only [Fm.shift, Fm.subst_eq, FactorVector.subst_isP, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] at h
    exact h
  have hZ' := LeanProofs.IPRA.Order.shift_le hZm
  exact rB_zero hP'.wk hZ'.wk Prf.hyp0

/-! ## At most `Z` numbers below `Z` -/

/-- `[m < Z]` over `0 = m`, `1 = Z`. -/
abbrev lowB : PTm 2 := sg (monus (var 1) (var 0))

theorem inst2_lowB (m Z : PTm n) : inst2 lowB m Z = sg (monus Z m) := by simp [inst2]

alias sg_le_one := Common.sg_le_one

/-- `Σ_{m<N} [m < Z] ≤ N`. -/
theorem low_le (N Z : PTm n) : Γ ⊢[PRAAx] le (ap2 (sumF lowB) N Z) N := by
  refine le_congr (.eqRefl _) (sum_ones N Z) (sum_le lowB one Z N (.allI (.impI ?_)))
  have e : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift Z) = one := by simp [inst2]
  rw [inst2_lowB, e]
  exact sg_le_one _

/-- `Σ_{m<X} [m < Z] ≤ Z`. -/
theorem count_below (X Z : PTm n) : Γ ⊢[PRAAx] le (ap2 (sumF lowB) X Z) Z := by
  refine .orE (le_total X Z) ?_ ?_
  · exact le_trans (low_le X Z) Prf.hyp0
  · have hX : (le Z X :: Γ) ⊢[PRAAx] X ≐ Z + monus X Z := eq_add_of_le Prf.hyp0
    have sp := sum_split (Γ := le Z X :: Γ) lowB Z (monus X Z) Z
    have tail : (le Z X :: Γ) ⊢[PRAAx] ap2 (sumF (offB lowB)) (monus X Z) (pairT Z Z) ≐ zero := by
      refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
      rw [inst2_offB, inst2_lowB, shift_pairT]
      have f1 := fst_pair (Γ := lt (var 0) (Syn.shift (monus X Z)) :: (le Z X :: Γ).map Fm.shift)
        (Syn.shift Z) (Syn.shift Z)
      have s1 := snd_pair (Γ := lt (var 0) (Syn.shift (monus X Z)) :: (le Z X :: Γ).map Fm.shift)
        (Syn.shift Z) (Syn.shift Z)
      have m0 : (lt (var 0) (Syn.shift (monus X Z)) :: (le Z X :: Γ).map Fm.shift) ⊢[PRAAx]
          monus (sndT (pairT (Syn.shift Z) (Syn.shift Z))) (fstT (pairT (Syn.shift Z) (Syn.shift Z)) + var 0) ≐
            zero :=
        (congrMonus s1 (congrAdd f1 (.eqRefl _))).eqTrans (le_add_right (Syn.shift Z) (var 0))
      exact (congrSg m0).eqTrans sg_zero
    have e : (le Z X :: Γ) ⊢[PRAAx] ap2 (sumF lowB) X Z ≐ ap2 (sumF lowB) Z Z :=
      (congrAp2 (sumF lowB) hX (.eqRefl _)).eqTrans (sp.eqTrans ((congrAdd (.eqRefl _) tail).eqTrans (add_zero _)))
    exact le_congr e.eqSymm (.eqRefl _) (low_le Z Z)

/-! ## The pointwise bound -/

alias eqb_le1 := Common.eqb_le_one

alias mul_one1 := Common.mul_one_right

/-- `c · [m prime] ≤ c · ρ(m) + [m < Z]` for `c ≤ 1`. -/
theorem prime_pt {m Z c : PTm n} (hc : Γ ⊢[PRAAx] le c one) :
    Γ ⊢[PRAAx] le (c * isP m) (c * rgh Z m + sg (monus Z m)) := by
  refine .orE (isP_01 m) ?_ ?_
  · exact le_congr ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero c)).eqSymm (.eqRefl _) (zero_le _)
  · have hP : ((isP m ≐ one) :: Γ) ⊢[PRAAx] isP m ≐ one := Prf.hyp0
    have cP : ((isP m ≐ one) :: Γ) ⊢[PRAAx] c * isP m ≐ c := (congrMul (.eqRefl _) hP).eqTrans (mul_one1 c)
    refine .orE (lt_or_le m Z) ?_ ?_
    · let C : List (Fm PTm n) := lt m Z :: (isP m ≐ one) :: Γ
      have hlt : C ⊢[PRAAx] lt m Z := Prf.hyp0
      have s1 : C ⊢[PRAAx] sg (monus Z m) ≐ one := by
        refine .orE (zero_or_succ (monus Z m)) ?_ (sg_pos Prf.hyp0)
        exact not_succ_le_self m _ (le_trans hlt.wk (Prf.hyp0 : ((monus Z m ≐ zero) :: C) ⊢[PRAAx] le Z m))
      have b : C ⊢[PRAAx] le c (c * rgh Z m + one) := le_trans hc.wk.wk (le_add_left one (c * rgh Z m))
      exact le_congr cP.wk.eqSymm (congrAdd (.eqRefl _) s1.eqSymm) b
    · let C : List (Fm PTm n) := le Z m :: (isP m ≐ one) :: Γ
      have hr : C ⊢[PRAAx] rgh Z m ≐ one := eqb_of_eq (rough_of_prime hP.wk Prf.hyp0)
      have e : C ⊢[PRAAx] c * rgh Z m ≐ c * isP m := congrMul (.eqRefl _) (hr.eqTrans hP.wk.eqSymm)
      exact le_congr e (.eqRefl _) (le_add_right (c * rgh Z m) (sg (monus Z m)))

/-! ## The count of primes -/

/-- `[m ≡ a (mod q)] · [m prime]` over `0 = m`, `1 = ⟨Z, ⟨Z, P⟩⟩`. -/
def piB : PTm 2 := Syn.subst ![var 0, sndT (sndT (var 1))] cB * isP (var 0)

theorem inst2_piB (m z : PTm n) : inst2 piB m z = inst2 cB m (sndT (sndT z)) * isP m := by
  simp [inst2, piB, Syn.subst_subst, FactorVector.subst_isP]

theorem piB_at (m Z P : PTm n) :
    Γ ⊢[PRAAx] inst2 piB m (pairT Z (pairT Z P)) ≐ inst2 cB m P * isP m := by
  rw [inst2_piB]
  have s1 := snd_pair (Γ := Γ) Z (pairT Z P)
  exact congrMul (congrInst2 cB (.eqRefl _) ((congrSnd s1).eqTrans (snd_pair Z P))) (.eqRefl _)

/-- `[m < Z]` over `0 = m`, `1 = ⟨Z, ⟨Z, P⟩⟩`. -/
abbrev lowZ : PTm 2 := sg (monus (fstT (var 1)) (var 0))

theorem inst2_lowZ (m z : PTm n) : inst2 lowZ m z = sg (monus (fstT z) m) := by simp [inst2]

theorem lowZ_at (m Z P : PTm n) :
    Γ ⊢[PRAAx] inst2 lowZ m (pairT Z (pairT Z P)) ≐ inst2 lowB m Z := by
  rw [inst2_lowZ, inst2_lowB]
  exact congrSg (congrMonus (fst_pair Z (pairT Z P)) (.eqRefl _))

theorem pi_pt (m Z P : PTm n) :
    Γ ⊢[PRAAx] le (inst2 piB m (pairT Z (pairT Z P)))
      (inst2 (addBody S0 lowZ) m (pairT Z (pairT Z P))) := by
  rw [inst2_addBody]
  have hc : Γ ⊢[PRAAx] le (inst2 cB m P) one := by rw [inst2_cB]; exact eqb_le1 _ _
  have b := prime_pt (m := m) (Z := Z) hc
  have l2 : Γ ⊢[PRAAx] inst2 lowZ m (pairT Z (pairT Z P)) ≐ sg (monus Z m) := by
    have h := lowZ_at (Γ := Γ) m Z P
    rw [inst2_lowB] at h
    exact h
  exact le_congr (piB_at m Z P).eqSymm (congrAdd (S0_at m Z P).eqSymm l2.eqSymm) b

/-- `π(X; q, a) ≤ S + Z`: the primes of the progression below `X` are at most the sifted count plus `Z`. -/
theorem primes_le (X Z P : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF piB) X (pairT Z (pairT Z P))) (ap2 (sumF S0) X (pairT Z (pairT Z P)) + Z) := by
  have m : Γ ⊢[PRAAx] le (ap2 (sumF piB) X (pairT Z (pairT Z P)))
      (ap2 (sumF (addBody S0 lowZ)) X (pairT Z (pairT Z P))) := by
    refine sum_le _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact pi_pt _ _ _
  have lz : Γ ⊢[PRAAx] ap2 (sumF lowZ) X (pairT Z (pairT Z P)) ≐ ap2 (sumF lowB) X Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact lowZ_at _ _ _
  have s := (sum_add S0 lowZ X (pairT Z (pairT Z P))).eqTrans (congrAdd (.eqRefl _) lz)
  have c := count_below (Γ := Γ) X Z
  exact le_trans (le_congr (.eqRefl _) s m) (add_le_add₂ (le_refl _) c)

end LeanProofs.IPRA.AnalyticNumberTheory.SievePrimes

export_ipra AnalyticNumberTheory.SievePrimes (eqb_le1 piB)
