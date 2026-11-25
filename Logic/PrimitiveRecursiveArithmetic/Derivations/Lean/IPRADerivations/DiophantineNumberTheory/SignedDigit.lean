import IPRADerivations.DiophantineNumberTheory.SignedVector
import IPRADerivations.Combinatorics.FiniteBijection
import IPRADerivations.Core.CommonLemmas

/-!
# Signed digits in base `2B + 1`

The visit counter of `diophantine_geometry_ipra`, Theorem `thm:northcott`, for signed boxes: "a visit counter
with base `(2B + 1)` digits ... subtract `B` from each digit". Here a digit `d < 2B + 1` encodes the signed entry
with sign `[d > B]` and magnitude `d ∸ [d > B] B`, i.e. `d ≤ B` is `+d` and `d = B + m` is `−m`.

* `sgnOf`, `magOf`: the decoding of a digit;
* `enc_dec`: a sign bit `s` and a magnitude `m ≤ B` with `s ≤ m` (zero has sign `0`) are recovered from the digit
  `s B + m`, and `enc_lt`: that digit is below `2B + 1`;
* `dec_bit`, `dec_zero`, `dec_le`: a decoded entry has a sign bit, the zero-sign convention and magnitude `≤ B`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SignedDigit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

alias congrSg := Common.congrSg

/-- The sign bit `[d > B]` of a digit. -/
abbrev sgnOf (B d : PTm k) : PTm k := sg (monus d B)
/-- The magnitude `d ∸ [d > B] B` of a digit. -/
abbrev magOf (B d : PTm k) : PTm k := monus d (sgnOf B d * B)

/-- Encoding then decoding: the digit `s B + m` has sign `s` and magnitude `m`. -/
theorem enc_dec {s m B : PTm k} (hs : Γ ⊢[PRAAx] (s ≐ zero) ⋎ (s ≐ one)) (hz : Γ ⊢[PRAAx] le s m)
    (hm : Γ ⊢[PRAAx] le m B) : Γ ⊢[PRAAx] (sgnOf B (s * B + m) ≐ s) ⋏ (magOf B (s * B + m) ≐ m) := by
  refine .orE hs ?_ ?_
  · have h0 : ((s ≐ zero) :: Γ) ⊢[PRAAx] s ≐ zero := Prf.hyp0
    have ed : ((s ≐ zero) :: Γ) ⊢[PRAAx] s * B + m ≐ m := by
      have e := natEq h0; apply deriveNat; ipra_simps; linear_combination 𝔞 B * e
    have sg0 : ((s ≐ zero) :: Γ) ⊢[PRAAx] sgnOf B (s * B + m) ≐ zero :=
      (congrSg (congrMonus ed (.eqRefl _))).eqTrans (sg_le hm.wk)
    refine .andI (sg0.eqTrans h0.eqSymm) ?_
    refine (congrMonus ed ((congrMul sg0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (monus_zero _)
  · have h1 : ((s ≐ one) :: Γ) ⊢[PRAAx] s ≐ one := Prf.hyp0
    have ed : ((s ≐ one) :: Γ) ⊢[PRAAx] s * B + m ≐ m + B := by
      have e := natEq h1; apply deriveNat; ipra_simps; linear_combination 𝔞 B * e
    have pm : ((s ≐ one) :: Γ) ⊢[PRAAx] le one m := le_congr h1 (.eqRefl _) hz.wk
    have lt1 : ((s ≐ one) :: Γ) ⊢[PRAAx] lt B (m + B) := by ipra_le sl pm
    have sg1 : ((s ≐ one) :: Γ) ⊢[PRAAx] sgnOf B (s * B + m) ≐ one :=
      (congrSg (congrMonus ed (.eqRefl _))).eqTrans (sg_lt lt1)
    refine .andI (sg1.eqTrans h1.eqSymm) ?_
    exact (congrMonus ed ((congrMul sg1 (.eqRefl _)).eqTrans (one_mul _))).eqTrans (add_monus _ _)

/-- The digit `s B + m` is below `2B + 1`. -/
theorem enc_lt {s m B : PTm k} (hs : Γ ⊢[PRAAx] (s ≐ zero) ⋎ (s ≐ one)) (hm : Γ ⊢[PRAAx] le m B) :
    Γ ⊢[PRAAx] lt (s * B + m) (succ (two * B)) := by
  refine .orE hs ?_ ?_
  · have e := natEq (Prf.hyp0 : ((s ≐ zero) :: Γ) ⊢[PRAAx] s ≐ zero)
    have hm' : ((s ≐ zero) :: Γ) ⊢[PRAAx] le m B := hm.wk
    show _ ⊢[PRAAx] le (succ (s * B + m)) (succ (two * B))
    ipra_le sl hm' + 𝔞 B using linear_combination -𝔞 B * e
  · have e := natEq (Prf.hyp0 : ((s ≐ one) :: Γ) ⊢[PRAAx] s ≐ one)
    have hm' : ((s ≐ one) :: Γ) ⊢[PRAAx] le m B := hm.wk
    show _ ⊢[PRAAx] le (succ (s * B + m)) (succ (two * B))
    ipra_le sl hm' using linear_combination -𝔞 B * e

/-- A decoded sign is a bit. -/
theorem dec_bit (B d : PTm k) : Γ ⊢[PRAAx] (sgnOf B d ≐ zero) ⋎ (sgnOf B d ≐ one) := sg_bit _

/-- A decoded entry obeys the zero-sign convention `sgn ≤ mag`. -/
theorem dec_zero (B d : PTm k) : Γ ⊢[PRAAx] le (sgnOf B d) (magOf B d) := by
  refine .orE (lt_or_le B d) ?_ ?_
  · have hl : (lt B d :: Γ) ⊢[PRAAx] le (succ B) d := Prf.hyp0
    have s1 : (lt B d :: Γ) ⊢[PRAAx] sgnOf B d ≐ one := sg_lt Prf.hyp0
    have em : (lt B d :: Γ) ⊢[PRAAx] magOf B d ≐ monus d B :=
      congrMonus (.eqRefl _) ((congrMul s1 (.eqRefl _)).eqTrans (one_mul _))
    have ed := natEq (eq_add_of_le hl)
    have mm : (lt B d :: Γ) ⊢[PRAAx] monus d B ≐ succ (monus d (succ B)) := by
      refine (congrMonus (eq_add_of_le hl) (.eqRefl _)).eqTrans ?_
      have q : (lt B d :: Γ) ⊢[PRAAx] succ B + monus d (succ B) ≐ succ (monus d (succ B)) + B := by ipra_ring
      exact (congrMonus q (.eqRefl _)).eqTrans (add_monus _ _)
    exact le_congr s1.eqSymm (em.eqTrans mm).eqSymm (by ipra_le 𝔞 (monus d (succ B)))
  · have s0 : (le d B :: Γ) ⊢[PRAAx] sgnOf B d ≐ zero := sg_le Prf.hyp0
    exact le_congr s0.eqSymm (.eqRefl _) (zero_le _)

/-- A decoded magnitude is at most `B` when `d < 2B + 1`. -/
theorem dec_le {B d : PTm k} (hd : Γ ⊢[PRAAx] lt d (succ (two * B))) : Γ ⊢[PRAAx] le (magOf B d) B := by
  refine .orE (lt_or_le B d) ?_ ?_
  · have s1 : (lt B d :: Γ) ⊢[PRAAx] sgnOf B d ≐ one := sg_lt Prf.hyp0
    have em : (lt B d :: Γ) ⊢[PRAAx] magOf B d ≐ monus d B :=
      congrMonus (.eqRefl _) ((congrMul s1 (.eqRefl _)).eqTrans (one_mul _))
    have hl : (lt B d :: Γ) ⊢[PRAAx] le (succ B) d := Prf.hyp0
    have ed := natEq (eq_add_of_le hl)
    have hd' : (lt B d :: Γ) ⊢[PRAAx] le (succ d) (succ (two * B)) := hd.wk
    have q : (lt B d :: Γ) ⊢[PRAAx] monus d B ≐ succ (monus d (succ B)) := by
      refine (congrMonus (eq_add_of_le hl) (.eqRefl _)).eqTrans ?_
      have q : (lt B d :: Γ) ⊢[PRAAx] succ B + monus d (succ B) ≐ succ (monus d (succ B)) + B := by ipra_ring
      exact (congrMonus q (.eqRefl _)).eqTrans (add_monus _ _)
    refine le_congr (em.eqTrans q).eqSymm (.eqRefl _) ?_
    ipra_le sl hd' using linear_combination ed
  · have s0 : (le d B :: Γ) ⊢[PRAAx] sgnOf B d ≐ zero := sg_le Prf.hyp0
    have em : (le d B :: Γ) ⊢[PRAAx] magOf B d ≐ d :=
      (congrMonus (.eqRefl _) ((congrMul s0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (monus_zero _)
    exact le_congr em.eqSymm (.eqRefl _) Prf.hyp0

end LeanProofs.IPRA.DiophantineNumberTheory.SignedDigit
