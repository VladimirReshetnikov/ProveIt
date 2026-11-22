import IPRADerivations.DiophantineNumberTheory.KhinchinLattice
import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Topology.StaggeredGrids
import IPRADerivations.Core.EuclidLemma

/-!
# The coprimality sieve for (K3) (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, the proof of (K3):
"Every noncoprime pair counted by `A(Q)` is divisible by some integer `d ∈ {2, …, Q}`. Dividing both
coordinates by `d` and applying (K5) bounds the number of bad pairs by `Σ_{d=2}^Q A(⌊Q/d⌋)`."

This module proves the pointwise step and the scaling invariance:

* `sieve_point`: for `q ≥ 1` and any weight `w`, `w · [gcd(p, q) ≠ 1] ≤ Σ_{d ≤ q} [2 ≤ d][d ∣ q][d ∣ p] w`,
  witnessed by `d = gcd(p, q)` (`2 ≤ gcd ≤ q`, dividing both);
* `inJ_scale`: `[dq'α < dp'β] [dp'β < dq'γ] = [q'α < p'β] [p'β < q'γ]` for `d ≥ 1`, i.e.
  `dp'/dq' ∈ J* ⟺ p'/q' ∈ J*`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSieve

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_le')
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_pos_right)
open LeanProofs.IPRA.Topology.StaggeredGrids (eqb01')
open LeanProofs.IPRA.Foundations.LatticeCount (sg_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The pointwise sieve -/

/-- `[2 ≤ d][d ∣ q][d ∣ p] w` in `(d, ⟨p, ⟨q, w⟩⟩)`. -/
abbrev sieveB : PTm 2 :=
  monus one (monus two (var 0)) * eqb (rem (fstT (sndT (var 1))) (var 0)) zero *
    eqb (rem (fstT (var 1)) (var 0)) zero * sndT (sndT (var 1))

/-- `Σ_{d < q+1} [2 ≤ d][d ∣ q][d ∣ p] w`. -/
abbrev sieveS (p q w : PTm n) : PTm n := ap2 (sumF sieveB) (succ q) (pairT p (pairT q w))

theorem inst2_sieveB (d p q w : PTm n) :
    inst2 sieveB d (pairT p (pairT q w)) =
      monus one (monus two d) * eqb (rem (fstT (sndT (pairT p (pairT q w)))) d) zero *
        eqb (rem (fstT (pairT p (pairT q w))) d) zero * sndT (sndT (pairT p (pairT q w))) := by
  simp [inst2]

/-- A noncoprime pair is counted by the divisor `gcd(p, q) ∈ [2, q]`. -/
theorem sieve_point {p q w : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) :
    Γ ⊢[PRAAx] le (w * monus one (eqb (gcd p q) one)) (sieveS p q w) := by
  refine .orE (eqb01' (Γ := Γ) (gcd p q) one) ?_ ?_
  · -- `gcd ≠ 1`: the divisor `g = gcd(p, q)`
    let Δ : List (Fm PTm n) := (eqb (gcd p q) one ≐ zero) :: Γ
    have hL : Δ ⊢[PRAAx] w * monus one (eqb (gcd p q) one) ≐ w :=
      (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))).eqTrans
        ((mul_comm _ _).eqTrans (one_mul _))
    have hg : Δ ⊢[PRAAx] gcd p q ≐ succ (pred (gcd p q)) := gcd_pos_right hq.wk
    have hd := gcd_dvd_at hg
    have hgq : Δ ⊢[PRAAx] le (gcd p q) q := dvd_le' hg (Prf.andE₂ hd) hq.wk
    -- `g ≥ 2`, since `g ≥ 1` and `g ≠ 1`
    have h2 : Δ ⊢[PRAAx] monus one (monus two (gcd p q)) ≐ one := by
      refine .orE (zero_or_succ (pred (gcd p q))) ?_ ?_
      · refine .botE _ (succ_ne_zero (a := zero) ?_)
        have e1 : ((pred (gcd p q) ≐ zero) :: Δ) ⊢[PRAAx] gcd p q ≐ one :=
          hg.wk.eqTrans (congrSucc Prf.hyp0)
        exact (eqb_of_eq e1).eqSymm.eqTrans (Prf.hyp1 : ((pred (gcd p q) ≐ zero) :: Δ) ⊢[PRAAx] _)
      · have e2 : ((pred (gcd p q) ≐ succ (pred (pred (gcd p q)))) :: Δ) ⊢[PRAAx]
            gcd p q ≐ succ (succ (pred (pred (gcd p q)))) := hg.wk.eqTrans (congrSucc Prf.hyp0)
        refine (congrMonus (.eqRefl _) ?_).eqTrans (monus_zero _)
        exact (congrMonus (.eqRefl _) e2).eqTrans ((succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _)))
    have hterm : Δ ⊢[PRAAx] inst2 sieveB (gcd p q) (pairT p (pairT q w)) ≐ w := by
      rw [inst2_sieveB]
      have hq' : Δ ⊢[PRAAx] eqb (rem (fstT (sndT (pairT p (pairT q w)))) (gcd p q)) zero ≐ one :=
        eqb_of_eq ((congrAp2 remF ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _)).eqTrans
          (Prf.andE₂ hd))
      have hp' : Δ ⊢[PRAAx] eqb (rem (fstT (pairT p (pairT q w))) (gcd p q)) zero ≐ one :=
        eqb_of_eq ((congrAp2 remF (fst_pair _ _) (.eqRefl _)).eqTrans (Prf.andE₁ hd))
      have hw : Δ ⊢[PRAAx] sndT (sndT (pairT p (pairT q w))) ≐ w := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      refine (congrMul (congrMul (congrMul h2 hq') hp') hw).eqTrans ?_
      apply deriveNat; ipra_simps; ring
    have hlt : Δ ⊢[PRAAx] lt (gcd p q) (succ q) := (succ_monus_succ _ _).eqTrans hgq
    exact le_congr (hterm.eqTrans hL.eqSymm) (.eqRefl _) (term_le_sum sieveB hlt)
  · -- coprime: the left side is `0`
    have h0 : ((eqb (gcd p q) one ≐ one) :: Γ) ⊢[PRAAx] w * monus one (eqb (gcd p q) one) ≐ zero :=
      (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _))).eqTrans (mul_zero _)
    exact le_congr h0.eqSymm (.eqRefl _) (zero_le _)

/-! ## Scaling -/

/-- `sg(d x ∸ d y) = sg(x ∸ y)` for `d ≥ 1`. -/
theorem sg_scale {d x y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] sg (monus (d * x) (d * y)) ≐ sg (monus x y) := by
  refine .orE (le_total x y) ?_ ?_
  · -- `x ≤ y`: both `0`
    let Δ : List (Fm PTm n) := le x y :: Γ
    have e := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
    have h1 : Δ ⊢[PRAAx] le (d * x) (d * y) := by
      refine le_of_eq_add (d := d * monus y x) ?_
      apply deriveNat; ipra_simps; linear_combination 𝔞 d * e
    exact ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h1)).eqTrans sg_zero).eqTrans
      ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero).eqSymm
  · -- `y ≤ x`: `x = y + e`; both are `sg e` (`d e` and `e` vanish together)
    let Δ : List (Fm PTm n) := le y x :: Γ
    have ex := eq_add_of_le (Γ := Δ) Prf.hyp0
    have e := natEq ex
    have hdx : Δ ⊢[PRAAx] d * x ≐ d * y + d * monus x y := by
      apply deriveNat; ipra_simps; linear_combination 𝔞 d * e
    have m1 : Δ ⊢[PRAAx] monus (d * x) (d * y) ≐ d * monus x y :=
      (congrMonus hdx (.eqRefl _)).eqTrans (add_monus' _ _)
    refine (sg_congr m1).eqTrans ?_
    refine .orE (zero_or_succ (monus x y)) ?_ ?_
    · exact (sg_congr ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))).eqTrans
        (sg_congr Prf.hyp0).eqSymm
    · have e2 : ((monus x y ≐ succ (pred (monus x y))) :: Δ) ⊢[PRAAx] d * monus x y ≐
          succ (pred d + pred (monus x y) * succ (pred d)) := by
        have a := natEq (Γ := (monus x y ≐ succ (pred (monus x y))) :: Δ) hd.wk.wk
        have b := natEq (Prf.hyp0 : ((monus x y ≐ succ (pred (monus x y))) :: Δ) ⊢[PRAAx] _)
        apply deriveNat; ipra_simps; rw [a, b]; ring
      exact ((sg_congr e2).eqTrans (sg_succ _)).eqTrans ((sg_congr Prf.hyp0).eqTrans (sg_succ _)).eqSymm

/-- `dp'/dq' ∈ J* ⟺ p'/q' ∈ J*`: the two indicators agree for `d ≥ 1`. -/
theorem inJ_scale {d p q α γ β : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] sg (monus (d * p * β) (d * q * α)) * sg (monus (d * q * γ) (d * p * β)) ≐
      sg (monus (p * β) (q * α)) * sg (monus (q * γ) (p * β)) := by
  have a1 : Γ ⊢[PRAAx] monus (d * p * β) (d * q * α) ≐ monus (d * (p * β)) (d * (q * α)) :=
    congrMonus (by ipra_ring) (by ipra_ring)
  have a2 : Γ ⊢[PRAAx] monus (d * q * γ) (d * p * β) ≐ monus (d * (q * γ)) (d * (p * β)) :=
    congrMonus (by ipra_ring) (by ipra_ring)
  exact congrMul ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) a1)).eqTrans (sg_scale hd))
    ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) a2)).eqTrans (sg_scale hd))

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSieve
