import IPRADerivations.AnalyticNumberTheory.SievePrimeInequality
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# At most `Z − 1` primes below `Z`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:
"Every prime counted by `π(x; q, a)` and larger than `z` survives this sieve. At most `z` other primes occur."

`SievePrimes.primes_le` bounds the other primes by the number `Z` of numbers below `Z = z + 1`, which gives
`π ≤ S + z + 1`. Since `0` is not a prime, only the `m` with `1 ≤ m < Z` matter, and there are `Z − 1` of them:

  `π(X; q, a) ≤ S + (Z − 1)`                                                     (`primes_le_sharp`),

and the sieve inequality for the primes holds with `Z − 1` in place of `Z` (`prime_sieve_ineq_sharp`). With `Z = z + 1`
this is the paper's "at most `z` other primes".

* `lowP`: the indicator `[1 ≤ m < Z]`;
* `lowP_succ`: `[1 ≤ i + 1 < Z] ≤ [i < Z − 1]`;
* `count_pos`: `Σ_{m<X} [1 ≤ m < Z] ≤ Z − 1`, by splitting off `m = 0` and `SievePrimes.count_below`;
* `prime_pt'`: `c · [m prime] ≤ c · ρ(m) + [1 ≤ m < Z]` for `c ≤ 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SievePrimesSharp

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l congrIsP isP_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (cB inst2_cB lB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveRough (rgh)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveClosedForms (gU sgV)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveMajorant (S0 S0_at amgm)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveInequality (sieve_ineq)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Lb)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePrimes (lowB inst2_lowB count_below eqb_le1 prime_pt piB piB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePrimeInequality (combine)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open LeanProofs.IPRA.Probability.Independence (dsum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The count of the `m` with `1 ≤ m < Z` -/

/-- `[1 ≤ m < Z]` over `0 = m`, `1 = Z`. -/
abbrev lowP : PTm 2 := sg (var 0) * sg (monus (var 1) (var 0))

theorem inst2_lowP (m Z : PTm n) : inst2 lowP m Z = sg m * sg (monus Z m) := by simp [inst2]

alias zero_le_of := Common.le_of_eq_zero

/-- `[1 ≤ i + 1 < Z] ≤ [i < Z − 1]`. -/
theorem lowP_succ (i Z : PTm n) :
    Γ ⊢[PRAAx] le (sg (succ i) * sg (monus Z (succ i))) (sg (monus (pred Z) i)) := by
  refine .orE (zero_or_succ Z) ?_ ?_
  · have m0 : ((Z ≐ zero) :: Γ) ⊢[PRAAx] monus Z (succ i) ≐ zero :=
      (congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _)
    exact zero_le_of ((congrMul (.eqRefl _) ((congrSg m0).eqTrans sg_zero)).eqTrans (mul_zero _))
  · have m1 : ((Z ≐ succ (pred Z)) :: Γ) ⊢[PRAAx] monus Z (succ i) ≐ monus (pred Z) i :=
      (congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (succ_monus_succ _ _)
    have e : ((Z ≐ succ (pred Z)) :: Γ) ⊢[PRAAx] sg (succ i) * sg (monus Z (succ i)) ≐ sg (monus (pred Z) i) :=
      (congrMul (sg_succ _) (congrSg m1)).eqTrans (one_mul _)
    exact le_congr e.eqSymm (.eqRefl _) (le_refl _)

theorem pos_comb {S S1 T M : PTm n} (E : Γ ⊢[PRAAx] S ≐ S1 + T) (F : Γ ⊢[PRAAx] S1 ≐ zero)
    (hT : Γ ⊢[PRAAx] le T M) : Γ ⊢[PRAAx] le S M := by
  have a := natEq E; have b := natEq F
  ipra_le sl hT with -a - b

/-- `Σ_{m<X} [1 ≤ m < Z] ≤ Z − 1`. -/
theorem count_pos (X Z : PTm n) : Γ ⊢[PRAAx] le (ap2 (sumF lowP) X Z) (pred Z) := by
  refine .orE (zero_or_succ X) ?_ ?_
  · exact zero_le_of ((congrAp2 (sumF lowP) Prf.hyp0 (.eqRefl _)).eqTrans (sum_zero _ _))
  · let C : List (Fm PTm n) := (X ≐ succ (pred X)) :: Γ
    have e : C ⊢[PRAAx] X ≐ one + pred X :=
      Prf.hyp0.eqTrans (by ipra_ring)
    have E := (congrAp2 (sumF lowP) e (.eqRefl Z)).eqTrans (sum_split lowP one (pred X) Z)
    have F : C ⊢[PRAAx] ap2 (sumF lowP) one Z ≐ zero := by
      refine (sum_succ' lowP zero Z).eqTrans ((congrAdd (sum_zero lowP Z) ?_).eqTrans (add_zero _))
      rw [inst2_lowP]
      exact zero_mul_l sg_zero _
    have T : C ⊢[PRAAx] le (ap2 (sumF (offB lowP)) (pred X) (pairT one Z)) (ap2 (sumF lowB) (pred X) (pred Z)) := by
      refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
      have s1 : Syn.shift (pairT one Z) = pairT one (Syn.shift Z) := by simp [Syn.shift]
      have s2 : Syn.shift (pred Z) = pred (Syn.shift Z) := by simp [Syn.shift]
      rw [s1, s2, inst2_offB, inst2_lowB]
      have a1 : (lt (var 0) (Syn.shift (pred X)) :: C.map Fm.shift) ⊢[PRAAx]
          fstT (pairT one (Syn.shift Z)) + var 0 ≐ succ (var 0) :=
        (congrAdd (fst_pair _ _) (.eqRefl _)).eqTrans (by ipra_ring)
      have a2 := congrInst2 lowP a1 (snd_pair (Γ := lt (var 0) (Syn.shift (pred X)) :: C.map Fm.shift)
        one (Syn.shift Z))
      rw [inst2_lowP (succ (var 0)) (Syn.shift Z)] at a2
      exact le_congr a2.eqSymm (.eqRefl _) (lowP_succ _ _)
    exact pos_comb E F (le_trans T (count_below (pred X) (pred Z)))

/-! ## The pointwise bound -/

/-- `c · [m prime] ≤ c · ρ(m) + [1 ≤ m < Z]` for `c ≤ 1`. -/
theorem prime_pt' {m Z c : PTm n} (hc : Γ ⊢[PRAAx] le c one) :
    Γ ⊢[PRAAx] le (c * isP m) (c * rgh Z m + sg m * sg (monus Z m)) := by
  refine .orE (zero_or_succ m) ?_ ?_
  · have p0 : ((m ≐ zero) :: Γ) ⊢[PRAAx] isP m ≐ zero := (congrIsP Prf.hyp0).eqTrans isP_zero
    exact zero_le_of ((congrMul (.eqRefl _) p0).eqTrans (mul_zero _))
  · have s1 : ((m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] sg m * sg (monus Z m) ≐ sg (monus Z m) :=
      (congrMul (sg_pos Prf.hyp0) (.eqRefl _)).eqTrans (one_mul _)
    exact le_congr (.eqRefl _) (congrAdd (.eqRefl _) s1.eqSymm) (prime_pt (Z := Z) hc).wk

/-! ## The count of primes -/

/-- `[1 ≤ m < Z]` over `0 = m`, `1 = ⟨Z, ⟨Z, P⟩⟩`. -/
abbrev lowZP : PTm 2 := sg (var 0) * sg (monus (fstT (var 1)) (var 0))

theorem inst2_lowZP (m z : PTm n) : inst2 lowZP m z = sg m * sg (monus (fstT z) m) := by simp [inst2]

theorem lowZP_at (m Z P : PTm n) :
    Γ ⊢[PRAAx] inst2 lowZP m (pairT Z (pairT Z P)) ≐ inst2 lowP m Z := by
  rw [inst2_lowZP, inst2_lowP]
  exact congrMul (.eqRefl _) (congrSg (congrMonus (fst_pair Z (pairT Z P)) (.eqRefl _)))

theorem pi_pt' (m Z P : PTm n) :
    Γ ⊢[PRAAx] le (inst2 piB m (pairT Z (pairT Z P)))
      (inst2 (addBody S0 lowZP) m (pairT Z (pairT Z P))) := by
  rw [inst2_addBody]
  have hc : Γ ⊢[PRAAx] le (inst2 cB m P) one := by rw [inst2_cB]; exact eqb_le1 _ _
  have b := prime_pt' (m := m) (Z := Z) hc
  have l2 : Γ ⊢[PRAAx] inst2 lowZP m (pairT Z (pairT Z P)) ≐ sg m * sg (monus Z m) := by
    have h := lowZP_at (Γ := Γ) m Z P
    rw [inst2_lowP] at h
    exact h
  exact le_congr (piB_at m Z P).eqSymm (congrAdd (S0_at m Z P).eqSymm l2.eqSymm) b

/-- `π(X; q, a) ≤ S + (Z − 1)`. -/
theorem primes_le_sharp (X Z P : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF piB) X (pairT Z (pairT Z P)))
      (ap2 (sumF S0) X (pairT Z (pairT Z P)) + pred Z) := by
  have m : Γ ⊢[PRAAx] le (ap2 (sumF piB) X (pairT Z (pairT Z P)))
      (ap2 (sumF (addBody S0 lowZP)) X (pairT Z (pairT Z P))) := by
    refine sum_le _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact pi_pt' _ _ _
  have lz : Γ ⊢[PRAAx] ap2 (sumF lowZP) X (pairT Z (pairT Z P)) ≐ ap2 (sumF lowP) X Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact lowZP_at _ _ _
  have s := (sum_add S0 lowZP X (pairT Z (pairT Z P))).eqTrans (congrAdd (.eqRefl _) lz)
  exact le_trans (le_congr (.eqRefl _) s m) (add_le_add₂ (le_refl _) (count_pos X Z))

/-- The sieve inequality for the primes of a progression, for arbitrary signed weights, with `Z − 1` other
primes: `q (λ_1)² (π − (Z − 1)) ≤ X Σ λ_d λ_e / [d, e] + q (Σ |λ_d|)²`, cleared of signs. -/
theorem prime_sieve_ineq_sharp (UP UN : PTm 2) {X Z P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) (hZ : Γ ⊢[PRAAx] lt one Z) :
    Γ ⊢[PRAAx] le
      (fstT P * ((inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
          ap2 (sumF piB) X (pairT Z (pairT Z P))) +
        fstT P * ((two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) * pred Z) +
        X * (dsum (Lb (sndB (gU UP)) (sndB (sgV UN))) Z Z (pairT X P) +
          dsum (Lb (sndB (gU UN)) (sndB (sgV UP))) Z Z (pairT X P)))
      (X * (dsum (Lb (sndB (gU UP)) (sndB (sgV UP))) Z Z (pairT X P) +
          dsum (Lb (sndB (gU UN)) (sndB (sgV UN))) Z Z (pairT X P)) +
        fstT P * ((ap2 (sumF (sndB (lB UP))) Z (pairT X P) + ap2 (sumF (sndB (lB UN))) Z (pairT X P)) *
          (ap2 (sumF (sndB (lB UP))) Z (pairT X P) + ap2 (sumF (sndB (lB UN))) Z (pairT X P))) +
        fstT P * ((inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
          pred Z) +
        fstT P * ((two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) *
          ap2 (sumF piB) X (pairT Z (pairT Z P)))) :=
  combine (sieve_ineq UP UN (X := X) hq ha hZ) (primes_le_sharp X Z P) (amgm _ _)

end LeanProofs.IPRA.AnalyticNumberTheory.SievePrimesSharp
