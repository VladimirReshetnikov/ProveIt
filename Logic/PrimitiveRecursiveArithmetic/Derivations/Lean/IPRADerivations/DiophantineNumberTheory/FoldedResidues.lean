import IPRADerivations.DiophantineNumberTheory.RectangleCount
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Core.LinearCombination

/-!
# Folded residues

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"From products to
floor sums", "The folded residues form a permutation":

  "Define `D(x) = min(rem_p(x), p − rem_p(x))` on units. It takes the same value on `x` and `−x`, equals one of
  these up to congruence, and fixes `j ∈ [1, h]`. Hence `D(u D(v)) = D(uv)` for units `u, v`. The map
  `i ↦ D(a i) = b_i` has explicit inverse `j ↦ D(a⁻¹ j)`, since both composites fix `[1, h]`."

For an odd `p = 2h + 1` the fold of a residue `r < p` is `fold p r = [r > h] (p − r) + (1 − [r > h]) r`, so that
`b_i = fold p ((i + 1) a mod p)` in the notation of `EisensteinParity` (`bV`). This module derives:

* `fold_small`, `fold_large`: the two branches;
* `fold_le`: `fold p r ≤ h` for `r < p`;
* `fold_spec`: for `1 ≤ r < p`, `1 ≤ fold p r ≤ h` and `fold p r = r` or `fold p r + r = p`;
* `fold_of_pm`: if `1 ≤ j ≤ h` and `r = j` or `r + j = p`, then `fold p r = j` (the fold fixes `[1, h]` and
  identifies `r` with `p − r`);
* `rem_pos`: `(i + 1) a mod p ≥ 1` for `i < h` and `gcd(p, a) = 1` (Gauss's lemma);
* `eq_of_dvd_lt_two`: a positive multiple of `p` below `2p` is `p`;
* `comp`: `fold p (b_i a' mod p) = i + 1` for `i < h` when `a a' ≡ 1 (mod p)`: multiplication by the inverse
  undoes the fold (`D(a' D(a i)) = D(a' a i) = i`).

The permutation of `[1, h]` and the sums and products over it (`eq:perm`) are not derived in this module.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.FoldedResidues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (rem_mul_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gauss dvd_le' eq_of_dvd')
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul rem_add_congr rem_mul_congr2)
open LeanProofs.IPRA.DiophantineNumberTheory.RectangleCount (no_small)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `fold p r = min(r, p − r)` for `r < p`, as `[r > ⌊p/2⌋] (p − r) + (1 − [r > ⌊p/2⌋]) r`. -/
abbrev fold (p r : PTm n) : PTm n :=
  sg (monus r (half p)) * monus p r + monus one (sg (monus r (half p))) * r

/-! ## The two branches -/

theorem f_zero {E ne M r : PTm n} (hE : Γ ⊢[PRAAx] E ≐ zero) (hn : Γ ⊢[PRAAx] ne ≐ one) :
    Γ ⊢[PRAAx] E * M + ne * r ≐ r := by
  ipra_lc 𝔞 M * natEq hE + 𝔞 r * natEq hn

theorem f_one {E ne M r : PTm n} (hE : Γ ⊢[PRAAx] E ≐ one) (hn : Γ ⊢[PRAAx] ne ≐ zero) :
    Γ ⊢[PRAAx] E * M + ne * r ≐ M := by
  ipra_lc 𝔞 M * natEq hE + 𝔞 r * natEq hn

/-- `fold p r = r` for `r ≤ ⌊p/2⌋`. -/
theorem fold_small {p r : PTm n} (h : Γ ⊢[PRAAx] le r (half p)) : Γ ⊢[PRAAx] fold p r ≐ r := by
  have hE : Γ ⊢[PRAAx] sg (monus r (half p)) ≐ zero := (congrSg h).eqTrans sg_zero
  exact f_zero hE ((congrMonus (.eqRefl _) hE).eqTrans (monus_zero _))

/-- `fold p r = p − r` for `r > ⌊p/2⌋`. -/
theorem fold_large {p r : PTm n} (h : Γ ⊢[PRAAx] lt (half p) r) : Γ ⊢[PRAAx] fold p r ≐ monus p r := by
  have hE : Γ ⊢[PRAAx] sg (monus r (half p)) ≐ one := by
    refine .orE (zero_or_succ (monus r (half p))) ?_ (sg_pos Prf.hyp0)
    exact not_succ_le_self (half p) _ (le_trans h.wk (Prf.hyp0 :
      ((monus r (half p) ≐ zero) :: Γ) ⊢[PRAAx] le r (half p)))
  exact f_one hE ((congrMonus (.eqRefl _) hE).eqTrans (monus_self _))

/-! ## Bounds -/

theorem large_le {p r M h : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * h + one) (hl : Γ ⊢[PRAAx] lt h r)
    (eM : Γ ⊢[PRAAx] p ≐ r + M) : Γ ⊢[PRAAx] le M h := by
  have x := natEq ep; have y := natEq eM
  ipra_le sl hl with y - x

/-- `fold p r ≤ ⌊p/2⌋` for `r < p`, `p = 2 ⌊p/2⌋ + 1`. -/
theorem fold_le {p r : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one) (hrp : Γ ⊢[PRAAx] lt r p) :
    Γ ⊢[PRAAx] le (fold p r) (half p) := by
  refine .orE (lt_or_le (half p) r) ?_ ?_
  · have hl : (lt (half p) r :: Γ) ⊢[PRAAx] lt (half p) r := Prf.hyp0
    have eM := eq_add_of_le (le_of_lt hrp.wk : (lt (half p) r :: Γ) ⊢[PRAAx] le r p)
    exact le_congr (fold_large hl).eqSymm (.eqRefl _) (large_le ep.wk hl eM)
  · have hs : (le r (half p) :: Γ) ⊢[PRAAx] le r (half p) := Prf.hyp0
    exact le_congr (fold_small hs).eqSymm (.eqRefl _) hs

/-- For `1 ≤ r < p`: `1 ≤ fold p r`, and `fold p r = r` or `fold p r + r = p`. -/
theorem fold_spec {p r : PTm n} (hr1 : Γ ⊢[PRAAx] r ≐ succ (pred r)) (hrp : Γ ⊢[PRAAx] lt r p) :
    Γ ⊢[PRAAx] (fold p r ≐ succ (pred (fold p r))) ⋏ ((fold p r ≐ r) ⋎ (fold p r + r ≐ p)) := by
  refine .orE (lt_or_le (half p) r) ?_ ?_
  · let C : List (Fm PTm n) := lt (half p) r :: Γ
    have hl : C ⊢[PRAAx] lt (half p) r := Prf.hyp0
    have eM : C ⊢[PRAAx] p ≐ r + monus p r := eq_add_of_le (le_of_lt hrp.wk)
    have fl := fold_large hl
    have hM : C ⊢[PRAAx] monus p r ≐ succ (pred (monus p r)) := by
      refine .orE (zero_or_succ (monus p r)) ?_ Prf.hyp0
      have e : ((monus p r ≐ zero) :: C) ⊢[PRAAx] p ≐ r :=
        eM.wk.eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))
      exact lt_irrefl r _ (lt_congr (.eqRefl _) e hrp.wk.wk)
    refine .andI (fl.eqTrans (hM.eqTrans (congrSucc (congrPred fl)).eqSymm)) (.orI₂ ?_)
    exact (congrAdd fl (.eqRefl _)).eqTrans ((add_comm _ _).eqTrans eM.eqSymm)
  · have hs : (le r (half p) :: Γ) ⊢[PRAAx] le r (half p) := Prf.hyp0
    have fs := fold_small hs
    exact .andI (fs.eqTrans (hr1.wk.eqTrans (congrSucc (congrPred fs)).eqSymm)) (.orI₁ fs)

theorem pm_large {p r j h : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * h + one) (hjh : Γ ⊢[PRAAx] le j h)
    (hc : Γ ⊢[PRAAx] r + j ≐ p) : Γ ⊢[PRAAx] lt h r := by
  have x := natEq ep; have y := natEq hc
  ipra_le sl hjh with y + x

theorem monus_of_add {p r j : PTm n} (hc : Γ ⊢[PRAAx] r + j ≐ p) : Γ ⊢[PRAAx] monus p r ≐ j :=
  (congrMonus hc.eqSymm (.eqRefl _)).eqTrans (add_monus' j r)

/-- The fold fixes `[1, h]` and identifies `r` with `p − r`: if `j ≤ h` and `r = j` or `r + j = p`, then
`fold p r = j`. -/
theorem fold_of_pm {p r j : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one)
    (hjh : Γ ⊢[PRAAx] le j (half p)) (hc : Γ ⊢[PRAAx] (r ≐ j) ⋎ (r + j ≐ p)) :
    Γ ⊢[PRAAx] fold p r ≐ j := by
  refine .orE hc ?_ ?_
  · have e : ((r ≐ j) :: Γ) ⊢[PRAAx] r ≐ j := Prf.hyp0
    exact (fold_small (le_congr e.eqSymm (.eqRefl _) hjh.wk)).eqTrans e
  · have e : ((r + j ≐ p) :: Γ) ⊢[PRAAx] r + j ≐ p := Prf.hyp0
    exact (fold_large (pm_large ep.wk hjh.wk e)).eqTrans (monus_of_add e)

/-! ## Residues of units -/

/-- `(i + 1) a mod p ≥ 1` for `i < P`, `p = 2P + 1` and `gcd(p, a) = 1`. -/
theorem rem_pos {p a P i : PTm n} (e2 : Γ ⊢[PRAAx] p ≐ two * P + one) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (hi : Γ ⊢[PRAAx] lt i P) :
    Γ ⊢[PRAAx] rem (succ i * a) p ≐ succ (pred (rem (succ i * a) p)) := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * P) (e2.eqTrans (by ipra_ring))
  refine .orE (zero_or_succ (rem (succ i * a) p)) ?_ Prf.hyp0
  have d1 : ((rem (succ i * a) p ≐ zero) :: Γ) ⊢[PRAAx] dvd p (a * succ i) :=
    (congrAp2 remF (mul_comm _ _) (.eqRefl _)).eqTrans Prf.hyp0
  have d2 := gauss hp1.wk hc.wk d1
  have l := dvd_le' hp1.wk d2 (congrSucc (pred_succ _).eqSymm)
  exact no_small _ e2.wk (le_trans l hi.wk)

/-- `i + 1 < p` for `i < P`, `p = 2P + 1`. -/
theorem succ_lt {p P i : PTm n} (e2 : Γ ⊢[PRAAx] p ≐ two * P + one) (hi : Γ ⊢[PRAAx] lt i P) :
    Γ ⊢[PRAAx] lt (succ i) p := by
  have x := natEq e2
  ipra_le sl hi + 𝔞 P with x

/-! ## A positive multiple of `p` below `2p` -/

theorem two_absurd {s p k : PTm n} (φ : Fm PTm n) (hs2 : Γ ⊢[PRAAx] lt s (two * p))
    (e : Γ ⊢[PRAAx] s ≐ p * succ (succ k)) : Γ ⊢[PRAAx] φ := by
  have x := natEq e
  refine not_succ_le_self (two * p) φ ?_
  ipra_le sl hs2 + 𝔞 p * 𝔞 k with x

/-- A positive multiple of `p` below `2p` is `p`. -/
theorem eq_of_dvd_lt_two {s p : PTm n} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hd : Γ ⊢[PRAAx] rem s p ≐ zero)
    (hs1 : Γ ⊢[PRAAx] s ≐ succ (pred s)) (hs2 : Γ ⊢[PRAAx] lt s (two * p)) : Γ ⊢[PRAAx] s ≐ p := by
  have e : Γ ⊢[PRAAx] s ≐ p * quo s p := eq_of_dvd' hp1 hd
  refine .orE (zero_or_succ (quo s p)) ?_ ?_
  · have z : ((quo s p ≐ zero) :: Γ) ⊢[PRAAx] s ≐ zero :=
      e.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
    exact succ_ne_zero' _ (hs1.wk.eqSymm.eqTrans z)
  · refine .orE (zero_or_succ (pred (quo s p))) ?_ ?_
    · have k1 : ((pred (quo s p) ≐ zero) :: (quo s p ≐ succ (pred (quo s p))) :: Γ) ⊢[PRAAx] quo s p ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact e.wk.wk.eqTrans ((congrMul (.eqRefl _) k1).eqTrans (by ipra_ring))
    · have k2 : ((pred (quo s p) ≐ succ (pred (pred (quo s p)))) :: (quo s p ≐ succ (pred (quo s p))) :: Γ)
          ⊢[PRAAx] quo s p ≐ succ (succ (pred (pred (quo s p)))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact two_absurd _ hs2.wk.wk (e.wk.wk.eqTrans (congrMul (.eqRefl _) k2))

/-! ## Multiplication by the inverse undoes the fold -/

theorem sum_lt_two {rx c p h : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * h + one) (hrx : Γ ⊢[PRAAx] lt rx p)
    (hc : Γ ⊢[PRAAx] le c h) : Γ ⊢[PRAAx] lt (rx + c) (two * p) := by
  have x := natEq ep
  ipra_le sl hrx + sl hc + 𝔞 h + 1 with x

theorem add_alg {b R a' p : PTm n} (h : Γ ⊢[PRAAx] b + R ≐ p) :
    Γ ⊢[PRAAx] b * a' + R * a' ≐ p * a' + zero := by
  ipra_lc 𝔞 a' * natEq h

/-- `rem (R a') p = i + 1` for `R = (i + 1) a mod p` when `a a' ≡ 1 (mod p)`. -/
theorem back {p a a' i : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one)
    (hinv : Γ ⊢[PRAAx] rem (a * a') p ≐ rem one p) (hi : Γ ⊢[PRAAx] lt i (half p)) :
    Γ ⊢[PRAAx] rem (rem (succ i * a) p * a') p ≐ succ i := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * half p) (ep.eqTrans (by ipra_ring))
  have h1 : Γ ⊢[PRAAx] rem (rem (succ i * a) p) p ≐ rem (succ i * a) p := rem_small (rem_lt' hp1 _)
  have s1 := rem_mul_congr a' hp1 h1
  have s2 : Γ ⊢[PRAAx] rem (succ i * a * a') p ≐ rem (succ i * (a * a')) p :=
    congrAp2 remF (mul_assoc _ _ _) (.eqRefl _)
  have s3 := rem_mul_congr2 hp1 (.eqRefl (rem (succ i) p)) hinv
  have s4 : Γ ⊢[PRAAx] rem (succ i * one) p ≐ succ i :=
    (congrAp2 remF (by ipra_ring) (.eqRefl _)).eqTrans (rem_small (succ_lt ep hi))
  exact s1.eqTrans (s2.eqTrans (s3.eqTrans s4))

/-- `fold p (b_i a' mod p) = i + 1` for `b_i = fold p ((i + 1) a mod p)`, `i < h`, `gcd(p, a) = 1` and
`a a' ≡ 1 (mod p)`. -/
theorem comp {p a a' i : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (hinv : Γ ⊢[PRAAx] rem (a * a') p ≐ rem one p) (hi : Γ ⊢[PRAAx] lt i (half p)) :
    Γ ⊢[PRAAx] fold p (rem (fold p (rem (succ i * a) p) * a') p) ≐ succ i := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * half p) (ep.eqTrans (by ipra_ring))
  have hR1 := rem_pos ep hc hi
  have hRp : Γ ⊢[PRAAx] lt (rem (succ i * a) p) p := rem_lt' hp1 _
  have sp := fold_spec hR1 hRp
  have bk := back ep hinv hi
  refine fold_of_pm ep hi (.orE (Prf.andE₂ sp) ?_ ?_)
  · -- `b = R`
    have e : ((fold p (rem (succ i * a) p) ≐ rem (succ i * a) p) :: Γ) ⊢[PRAAx]
        fold p (rem (succ i * a) p) ≐ rem (succ i * a) p := Prf.hyp0
    exact .orI₁ ((congrAp2 remF (congrMul e (.eqRefl _)) (.eqRefl _)).eqTrans bk.wk)
  · -- `b + R = p`
    let C : List (Fm PTm n) := (fold p (rem (succ i * a) p) + rem (succ i * a) p ≐ p) :: Γ
    have e : C ⊢[PRAAx] fold p (rem (succ i * a) p) + rem (succ i * a) p ≐ p := Prf.hyp0
    have hp1' : C ⊢[PRAAx] p ≐ succ (pred p) := hp1.wk
    have hrx : C ⊢[PRAAx] lt (rem (fold p (rem (succ i * a) p) * a') p) p := rem_lt' hp1' _
    have z : C ⊢[PRAAx] rem (fold p (rem (succ i * a) p) * a' + rem (succ i * a) p * a') p ≐ zero :=
      (congrAp2 remF (add_alg e) (.eqRefl _)).eqTrans ((rem_add_mul hp1' a' zero).eqTrans (rem_zero _))
    have c1 : C ⊢[PRAAx] rem (rem (fold p (rem (succ i * a) p) * a') p + succ i) p ≐
        rem (fold p (rem (succ i * a) p) * a' + rem (succ i * a) p * a') p :=
      rem_add_congr hp1' (rem_small hrx)
        ((congrAp2 remF bk.wk.eqSymm (.eqRefl _)).eqTrans (rem_small (rem_lt' hp1' _)))
    have s1 : C ⊢[PRAAx] rem (fold p (rem (succ i * a) p) * a') p + succ i ≐
        succ (pred (rem (fold p (rem (succ i * a) p) * a') p + succ i)) :=
      pos_of_eq_succ (c := rem (fold p (rem (succ i * a) p) * a') p + i) (by ipra_ring)
    exact .orI₂ (eq_of_dvd_lt_two hp1' (c1.eqTrans z) s1 (sum_lt_two ep.wk hrx hi.wk))

end LeanProofs.IPRA.DiophantineNumberTheory.FoldedResidues
