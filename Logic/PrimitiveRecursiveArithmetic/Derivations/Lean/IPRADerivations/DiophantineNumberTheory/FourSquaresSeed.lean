import IPRADerivations.DiophantineNumberTheory.ThueGrid
import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.Totatives

/-!
# Four squares: a small multiple of an odd prime of the form `a² + b² + 1`

Packet: `diophantine-number-theory/lagrange_four_squares_ipra_2026-11-22`, `sections/02_seed.tex`
("Two short lists of square residues", "Small positive multiple of a prime"): for an odd prime
`p = 2h + 1` there are `a, b ≤ h` with `p ∣ a² + b² + 1`.

The `p + 1 = 2 (h + 1)` indices `i ≤ p` are labelled by `p` residues: `i² mod p` for `i ≤ h` and
`(p − 1)(j² + 1) mod p` (that is `−1 − j²`) for `i = h + 1 + j`. The pigeonhole principle with search
witnesses (`Core/Pigeonhole`) returns `I < J ≤ p` with equal labels.

* `sq_inj`: two indices `i < j ≤ h` have different squares modulo `p` (Euclid's lemma on
  `j² − i² = (j − i)(j + i)`);
* `neg_cancel`: `(p − 1) A ≡ (p − 1) B` gives `A ≡ B`, by adding `A + B` to both sides;
* so a collision inside either list is impossible, and a collision between the lists is
  `I² ≡ (p − 1)(j² + 1)`, hence `p ∣ I² + j² + 1`;
* `sa`, `sb`, `seed`: the two terms and the statement.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresSeed

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul rem_add_congr shift_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.ThueGrid (rem_cancel)
open LeanProofs.IPRA.Pigeonhole (phpI phpJ pigeonhole)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Squares below `p/2` are distinct modulo `p` -/

theorem not_dvd_small {p x : PTm k} (hx1 : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hxp : Γ ⊢[PRAAx] lt x p)
    (h : Γ ⊢[PRAAx] dvd p x) : Γ ⊢[PRAAx] Fm.bot :=
  succ_ne_zero' _ (hx1.eqSymm.eqTrans ((rem_small hxp).eqSymm.eqTrans h))

theorem diff_alg {i j d : PTm k} (e : Γ ⊢[PRAAx] j ≐ i + d) : Γ ⊢[PRAAx] j * j ≐ i * i + d * (j + i) := by
  have a := natEq e
  apply deriveNat; ipra_simps; linear_combination (𝔞 j + 𝔞 i) * a

/-- For a prime `p = 2h + 1`: `i < j ≤ h` and `i² ≡ j² (mod p)` are contradictory. -/
theorem sq_inj {p i j : PTm k} (hp : Γ ⊢[PRAAx] prime p) (ep : Γ ⊢[PRAAx] p ≐ two * half p + one)
    (hij : Γ ⊢[PRAAx] lt i j) (hj : Γ ⊢[PRAAx] le j (half p))
    (e : Γ ⊢[PRAAx] rem (i * i) p ≐ rem (j * j) p) : Γ ⊢[PRAAx] Fm.bot := by
  have hp1 := p_pos (prime_two hp)
  have ed := eq_add_of_le (le_of_lt hij)
  have edn := natEq ed; have epn := natEq ep
  have e' : Γ ⊢[PRAAx] rem (i * i + zero) p ≐ rem (i * i + monus j i * (j + i)) p :=
    (congrAp2 remF (add_zero _) (.eqRefl _)).eqTrans (e.eqTrans (congrAp2 remF (diff_alg ed) (.eqRefl _)))
  have hd : Γ ⊢[PRAAx] dvd p (monus j i * (j + i)) := (rem_cancel hp1 e').eqSymm.eqTrans (rem_zero p)
  have d1 : Γ ⊢[PRAAx] le one (monus j i) := by ipra_le sl hij with edn
  have dp : Γ ⊢[PRAAx] lt (monus j i) p := by ipra_le sl hj + 𝔞 (half p) + 𝔞 i with epn + edn
  have s1 : Γ ⊢[PRAAx] le one (j + i) := by ipra_le sl hij + 2 * 𝔞 i
  have sp : Γ ⊢[PRAAx] lt (j + i) p := by ipra_le sl hj + sl hj + sl hij + 1 with epn
  refine .orE (euclid_lemma_at hp hd) ?_ ?_
  · exact not_dvd_small (AnalyticNumberTheory.BinomialThree.pos_of_one_le d1).wk dp.wk Prf.hyp0
  · exact not_dvd_small (AnalyticNumberTheory.BinomialThree.pos_of_one_le s1).wk sp.wk Prf.hyp0

theorem neg_alg {p A B : PTm k} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] pred p * A + (A + B) ≐ p * A + B := by
  have a := natEq hp1
  apply deriveNat; ipra_simps; linear_combination (-𝔞 A) * a

/-- `(p − 1) A ≡ (p − 1) B (mod p)` gives `A ≡ B`. -/
theorem neg_cancel {p A B : PTm k} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (e : Γ ⊢[PRAAx] rem (pred p * A) p ≐ rem (pred p * B) p) : Γ ⊢[PRAAx] rem A p ≐ rem B p := by
  have s := rem_add_congr hp1 e (.eqRefl (rem (A + B) p))
  have l : Γ ⊢[PRAAx] rem (pred p * A + (A + B)) p ≐ rem B p :=
    (congrAp2 remF (neg_alg hp1) (.eqRefl _)).eqTrans (rem_add_mul hp1 A B)
  have eBA : Γ ⊢[PRAAx] pred p * B + (A + B) ≐ pred p * B + (B + A) := congrAdd (.eqRefl _) (add_comm A B)
  have r : Γ ⊢[PRAAx] rem (pred p * B + (A + B)) p ≐ rem A p :=
    (congrAp2 remF (eBA.eqTrans (neg_alg hp1)) (.eqRefl _)).eqTrans (rem_add_mul hp1 B A)
  exact r.eqSymm.eqTrans (s.eqSymm.eqTrans l)

/-! ## The labels -/

/-- `[i > ⌊p/2⌋]`, over `0 = i`, `1 = p`. -/
abbrev hiB : PTm 2 := sg (monus (var 0) (half (var 1)))

/-- The label of the index `i`. -/
abbrev seedB : PTm 2 :=
  monus one hiB * rem (var 0 * var 0) (var 1) +
    hiB * rem (pred (var 1) * (monus (var 0) (succ (half (var 1))) * monus (var 0) (succ (half (var 1))) + one))
      (var 1)

/-- The second index of a point of the second list. -/
abbrev jv (i p : PTm k) : PTm k := monus i (succ (half p))

theorem seed_at (i p : PTm k) : inst2 seedB i p =
    monus one (sg (monus i (half p))) * rem (i * i) p +
      sg (monus i (half p)) * rem (pred p * (jv i p * jv i p + one)) p := by
  simp [inst2, subst_ap1]

theorem lab0 {S M1 a b : PTm k} (s0 : Γ ⊢[PRAAx] S ≐ zero) (m1 : Γ ⊢[PRAAx] M1 ≐ one) :
    Γ ⊢[PRAAx] M1 * a + S * b ≐ a := by
  have x := natEq s0; have y := natEq m1
  apply deriveNat; ipra_simps; linear_combination 𝔞 a * y + 𝔞 b * x

theorem lab1 {S M1 a b : PTm k} (s1 : Γ ⊢[PRAAx] S ≐ one) (m0 : Γ ⊢[PRAAx] M1 ≐ zero) :
    Γ ⊢[PRAAx] M1 * a + S * b ≐ b := by
  have x := natEq s1; have y := natEq m0
  apply deriveNat; ipra_simps; linear_combination 𝔞 a * y + 𝔞 b * x

/-- An index of the first list: the label is `i² mod p`. -/
theorem seed_low {i p : PTm k} (h : Γ ⊢[PRAAx] le i (half p)) :
    Γ ⊢[PRAAx] inst2 seedB i p ≐ rem (i * i) p := by
  rw [seed_at]
  have s0 : Γ ⊢[PRAAx] sg (monus i (half p)) ≐ zero := sg_le h
  exact lab0 s0 ((congrMonus (.eqRefl (one : PTm k)) s0).eqTrans (monus_zero one))

/-- An index of the second list: the label is `(p − 1)(j² + 1) mod p`. -/
theorem seed_high {i p : PTm k} (h : Γ ⊢[PRAAx] lt (half p) i) :
    Γ ⊢[PRAAx] inst2 seedB i p ≐ rem (pred p * (jv i p * jv i p + one)) p := by
  rw [seed_at]
  have s1 : Γ ⊢[PRAAx] sg (monus i (half p)) ≐ one := sg_lt h
  exact lab1 s1 ((congrMonus (.eqRefl (one : PTm k)) s1).eqTrans (monus_self one))

theorem seed_range {p : PTm k} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] Permutation.rangeAll seedB p p := by
  refine .allI ?_
  have hp' := shift_pos hp1
  refine .orE (lt_or_le (half (Syn.shift p)) (var 0)) ?_ ?_
  · exact lt_congr (seed_high Prf.hyp0).eqSymm (.eqRefl _) (rem_lt' hp'.wk _)
  · exact lt_congr (seed_low Prf.hyp0).eqSymm (.eqRefl _) (rem_lt' hp'.wk _)

/-! ## The seed -/

/-- The two colliding indices. -/
abbrev sI (p : PTm k) : PTm k := phpI seedB p p
abbrev sJ (p : PTm k) : PTm k := phpJ seedB p p

/-- The two entries of the seed. -/
abbrev sa (p : PTm k) : PTm k := sI p
abbrev sb (p : PTm k) : PTm k := jv (sJ p) p

theorem cross_alg {p B : PTm k} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] pred p * B + B ≐ p * B + zero := by
  have a := natEq hp1
  apply deriveNat; ipra_simps; linear_combination (-𝔞 B) * a

/-- "Small positive multiple of a prime": for an odd prime `p = 2h + 1`, the terms `a = sa p`, `b = sb p`
satisfy `p ∣ a² + b² + 1` and `a, b ≤ h`. -/
theorem seed {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) (ep : Γ ⊢[PRAAx] p ≐ two * half p + one) :
    Γ ⊢[PRAAx] dvd p (sa p * sa p + (sb p * sb p + one)) ⋏ (le (sa p) (half p) ⋏ le (sb p) (half p)) := by
  have hp1 := p_pos (prime_two hp)
  have ph := pigeonhole (S := seedB) (seed_range hp1)
  have hIJ := Prf.andE₁ ph
  have hJ := Prf.andE₁ (Prf.andE₂ ph)
  have hc := Prf.andE₂ (Prf.andE₂ ph)
  refine .orE (lt_or_le (half p) (sJ p)) ?_ ?_
  · -- `J` is in the second list
    have hJh : (lt (half p) (sJ p) :: Γ) ⊢[PRAAx] lt (half p) (sJ p) := Prf.hyp0
    have eJ := natEq (eq_add_of_le hJh)
    have epn' := natEq (ep.wk (ψ := lt (half p) (sJ p)))
    have hJ' : (lt (half p) (sJ p) :: Γ) ⊢[PRAAx] le (sJ p) p := hJ.wk
    have hb : (lt (half p) (sJ p) :: Γ) ⊢[PRAAx] le (sb p) (half p) := by
      ipra_le sl hJ' with epn' - eJ
    refine .orE (lt_or_le (half p) (sI p)) ?_ ?_
    · -- both in the second list: impossible
      refine .botE _ ?_
      have hIh : (lt (half p) (sI p) :: lt (half p) (sJ p) :: Γ) ⊢[PRAAx] lt (half p) (sI p) := Prf.hyp0
      have e1 := (seed_high hIh).eqSymm.eqTrans (hc.wk.wk.eqTrans (seed_high hJh.wk))
      have e2 := neg_cancel hp1.wk.wk e1
      have e3 : (lt (half p) (sI p) :: lt (half p) (sJ p) :: Γ) ⊢[PRAAx]
          rem (jv (sI p) p * jv (sI p) p) p ≐ rem (jv (sJ p) p * jv (sJ p) p) p :=
        rem_cancel hp1.wk.wk ((congrAp2 remF (add_comm _ _) (.eqRefl _)).eqTrans
          (e2.eqTrans (congrAp2 remF (add_comm _ _) (.eqRefl _))))
      have eI := natEq (eq_add_of_le hIh)
      have eJ' := natEq (eq_add_of_le (hJh.wk (ψ := lt (half p) (sI p))))
      have hIJ' : (lt (half p) (sI p) :: lt (half p) (sJ p) :: Γ) ⊢[PRAAx] lt (sI p) (sJ p) := hIJ.wk.wk
      have hlt : (lt (half p) (sI p) :: lt (half p) (sJ p) :: Γ) ⊢[PRAAx] lt (jv (sI p) p) (jv (sJ p) p) := by
        ipra_le sl hIJ' with eJ' - eI
      exact sq_inj hp.wk.wk ep.wk.wk hlt hb.wk e3
    · -- `I` in the first list, `J` in the second: the seed
      have hIh : (le (sI p) (half p) :: lt (half p) (sJ p) :: Γ) ⊢[PRAAx] le (sI p) (half p) := Prf.hyp0
      have e1 := (seed_low hIh).eqSymm.eqTrans (hc.wk.wk.eqTrans (seed_high hJh.wk))
      have a := rem_add_congr hp1.wk.wk e1 (.eqRefl (rem (sb p * sb p + one) p))
      have d : (le (sI p) (half p) :: lt (half p) (sJ p) :: Γ) ⊢[PRAAx]
          dvd p (sa p * sa p + (sb p * sb p + one)) :=
        a.eqTrans ((congrAp2 remF (cross_alg hp1.wk.wk) (.eqRefl _)).eqTrans
          ((rem_add_mul hp1.wk.wk _ zero).eqTrans (rem_zero p)))
      exact .andI d (.andI hIh hb.wk)
  · -- both in the first list: impossible
    refine .botE _ ?_
    have hJh : (le (sJ p) (half p) :: Γ) ⊢[PRAAx] le (sJ p) (half p) := Prf.hyp0
    have hIh := le_trans (le_of_lt hIJ.wk) hJh
    have e1 := (seed_low hIh).eqSymm.eqTrans (hc.wk.eqTrans (seed_low hJh))
    exact sq_inj hp.wk ep.wk hIJ.wk hJh e1

end LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresSeed
