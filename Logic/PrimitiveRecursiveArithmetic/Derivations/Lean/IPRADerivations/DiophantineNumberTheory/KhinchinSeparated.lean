import IPRADerivations.DiophantineNumberTheory.KhinchinReduced
import IPRADerivations.DiophantineNumberTheory.FractionSeparation
import IPRADerivations.Foundations.IntervalPacking

/-!
# The scale-`k` intervals of Khinchin's construction are separated (`hurwitz_khinchin_ipra`, (K8))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K8): "let `E_k(J)` be the union of
the intervals of radius `r_k` centered at the fractions in `𝓡_k(J)` … They are pairwise disjoint at each
fixed scale, by the separation just proved."

On the grid `T` (a common multiple of the denominators), the fraction `p/q` sits at `A = Tp/q`, i.e.
`qA = Tp`. For two reduced fractions in `J*` with denominators at most `Q` and a width `w` with
`Q²w ≤ T`:

* `act_facts`: an active pair (`[qα < pβ][pβ < qγ][gcd(p, q) = 1] = 1`) satisfies the three conditions;
* `sep_core`: `p/q < p'/q'` (`pq' < p'q`) gives `A + w ≤ A'` (since `qq'(A' − A) = T(p'q − pq') ≥ T ≥ Q²w ≥ qq'w`);
* `sep_pair`: two different reduced pairs are `w`-separated in one of the two directions — the separation
  hypothesis of `Foundations/IntervalPacking.packing` for the intervals `[A, A + w)` of `E_k(J)`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSeparated

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit)
open LeanProofs.IPRA.Topology.StaggeredGrids (eqb01' eq_of_eqb)
open LeanProofs.IPRA.DiophantineNumberTheory.FractionSeparation (frac_unique)
open LeanProofs.IPRA.Foundations.IntervalPacking (pos_of_sg_one lt_of_monus_pos absurd_one_zero')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `[qα < pβ][pβ < qγ][gcd(p, q) = 1]`. -/
abbrev actv (p q α γ β : PTm n) : PTm n := inJT p q α γ β * eqb (gcd p q) one

/-- An active pair satisfies its three conditions. -/
theorem act_facts {p q α γ β : PTm n} (h : Γ ⊢[PRAAx] sg (actv p q α γ β) ≐ one) :
    Γ ⊢[PRAAx] lt (q * α) (p * β) ⋏ (lt (p * β) (q * γ) ⋏ (gcd p q ≐ one)) := by
  have hp := pos_of_sg_one h
  refine .orE (sg_bit (Γ := Γ) (monus (p * β) (q * α))) ?_ ?_
  · refine absurd_one_zero' ((monus_zero _).eqSymm.eqTrans ((congrMonus (.eqRefl _) ?_).eqSymm.eqTrans hp.wk))
    exact (congrMul (congrMul Prf.hyp0 (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))
  · let Δ : List (Fm PTm n) := (sg (monus (p * β) (q * α)) ≐ one) :: Γ
    have s1 : Δ ⊢[PRAAx] sg (monus (p * β) (q * α)) ≐ one := Prf.hyp0
    refine .orE (sg_bit (Γ := Δ) (monus (q * γ) (p * β))) ?_ ?_
    · refine absurd_one_zero' ((monus_zero _).eqSymm.eqTrans ((congrMonus (.eqRefl _) ?_).eqSymm.eqTrans hp.wk.wk))
      exact (congrMul (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans
        ((congrMul (mul_zero _) (.eqRefl _)).eqTrans (zero_mul _))
    · let Δ' : List (Fm PTm n) := (sg (monus (q * γ) (p * β)) ≐ one) :: Δ
      have s2 : Δ' ⊢[PRAAx] sg (monus (q * γ) (p * β)) ≐ one := Prf.hyp0
      refine .orE (eqb01' (Γ := Δ') (gcd p q) one) ?_ ?_
      · refine absurd_one_zero' ((monus_zero _).eqSymm.eqTrans ((congrMonus (.eqRefl _) ?_).eqSymm.eqTrans hp.wk.wk.wk))
        exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)
      · have e3 : ((eqb (gcd p q) one ≐ one) :: Δ') ⊢[PRAAx] gcd p q ≐ one := eq_of_eqb Prf.hyp0
        exact .andI (lt_of_monus_pos (pos_of_sg_one s1.wk.wk)) (.andI (lt_of_monus_pos (pos_of_sg_one s2.wk)) e3)

/-- Separation on the grid: `qA = Tp`, `q'A' = Tp'`, `pq' < p'q`, `1 ≤ q, q' ≤ Q`, `Q²w ≤ T` give
`A + w ≤ A'`. -/
theorem sep_core {p q p' q' A A' T w Q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (hq' : Γ ⊢[PRAAx] q' ≐ succ (pred q')) (hQq : Γ ⊢[PRAAx] le q Q) (hQq' : Γ ⊢[PRAAx] le q' Q)
    (hA : Γ ⊢[PRAAx] q * A ≐ T * p) (hA' : Γ ⊢[PRAAx] q' * A' ≐ T * p') (hw : Γ ⊢[PRAAx] le (Q * Q * w) T)
    (hlt : Γ ⊢[PRAAx] lt (p * q') (p' * q)) : Γ ⊢[PRAAx] le (A + w) A' := by
  have eA := natEq hA
  have eA' := natEq hA'
  have hN : Γ ⊢[PRAAx] q * q' ≐ succ (pred (q * q')) := pos_mul' hq hq'
  refine cancel_le hN ?_
  ipra_le 𝔞 T * sl hlt + sl hw + 𝔞 w * (𝔞 Q * sl hQq' + 𝔞 q' * sl hQq) with 𝔞 q * eA' - 𝔞 q' * eA

/-- Two different active reduced pairs are `w`-separated: `A + w ≤ A'` or `A' + w ≤ A`. -/
theorem sep_pair {p q p' q' A A' T w Q α γ β : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (hq' : Γ ⊢[PRAAx] q' ≐ succ (pred q')) (hQq : Γ ⊢[PRAAx] le q Q) (hQq' : Γ ⊢[PRAAx] le q' Q)
    (hA : Γ ⊢[PRAAx] q * A ≐ T * p) (hA' : Γ ⊢[PRAAx] q' * A' ≐ T * p') (hw : Γ ⊢[PRAAx] le (Q * Q * w) T)
    (a1 : Γ ⊢[PRAAx] sg (actv p q α γ β) ≐ one) (a2 : Γ ⊢[PRAAx] sg (actv p' q' α γ β) ≐ one)
    (hne : Γ ⊢[PRAAx] neg ((q ≐ q') ⋏ (p ≐ p'))) :
    Γ ⊢[PRAAx] le (A + w) A' ⋎ le (A' + w) A := by
  have g1 := Prf.andE₂ (Prf.andE₂ (act_facts a1))
  have g2 := Prf.andE₂ (Prf.andE₂ (act_facts a2))
  refine .orE (lt_or_le (p * q') (p' * q)) ?_ ?_
  · exact .orI₁ (sep_core hq.wk hq'.wk hQq.wk hQq'.wk hA.wk hA'.wk hw.wk Prf.hyp0)
  · refine .orE (lt_or_le (p' * q) (p * q')) ?_ ?_
    · exact .orI₂ (sep_core hq'.wk.wk hq.wk.wk hQq'.wk.wk hQq.wk.wk hA'.wk.wk hA.wk.wk hw.wk.wk Prf.hyp0)
    · let Δ : List (Fm PTm n) := le (p * q') (p' * q) :: le (p' * q) (p * q') :: Γ
      have e : Δ ⊢[PRAAx] p * q' ≐ p' * q := le_antisymm Prf.hyp0 Prf.hyp1
      exact .botE _ (.impE hne.wk.wk (frac_unique hq.wk.wk hq'.wk.wk g1.wk.wk g2.wk.wk e))

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSeparated
