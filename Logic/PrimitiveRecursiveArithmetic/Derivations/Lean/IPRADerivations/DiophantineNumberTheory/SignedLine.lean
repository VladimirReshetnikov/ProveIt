import IPRADerivations.DiophantineNumberTheory.ProjectiveNormalize
import IPRADerivations.DiophantineNumberTheory.GcdNormalize
import IPRADerivations.Core.LinearCombination

/-!
# Signed primitive representatives on the projective line

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemma `lem:normalize`: "Every nonzero integral
vector `v` has a primitive representative `norm(v)`, obtained by dividing by `g = gcd(|v_0|, …, |v_n|)` and
choosing the sign so the first nonzero coordinate is positive. Two such representatives of the same rational
projective point are equal." Here on `P^1` with signed coordinates.

A signed integer is a sign bit `s ∈ {0, 1}` and a magnitude `m`, with value `(−1)^s m` (`sv`, an integer term
`ZT`), and the convention `s ≤ m` (zero has sign `0`). A pair `(a, b)` is normalized when
`gcd(|a|, |b|) = 1`, `s_a = 0` and `s_b ≤ |a|` (if `a = 0` the first nonzero coordinate is `b`, which is then
positive).

* `one_of_gcd_zero`: `gcd(0, b) = 1` forces `b = 1`;
* `mag_unique`: primitive natural pairs with `a d = b c` are equal, zero coordinates included;
* `signed_unique`: two normalized signed pairs with `a d = b c` (as integers) are equal.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SignedLine

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.ProjectiveNormalize (norm_unique)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize (gcd_zero_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_one_of_dvd_one)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The signed integer `(−1)^s m`. -/
def sv (s m : PTm k) : ZT k := ⟨monus one s * m, s * m⟩

/-- The cross equation `a d = b c` of two signed pairs. -/
def crossF (sa ma sb mb sc mc sd md : PTm k) : Fm PTm k :=
  ZT.eq (sv sa ma * sv sd md) (sv sb mb * sv sc mc)

/-- `gcd(0, b) = 1` forces `b = 1`. -/
theorem one_of_gcd_zero {b : PTm k} (h : Γ ⊢[PRAAx] gcd zero b ≐ one) : Γ ⊢[PRAAx] b ≐ one := by
  refine .orE (zero_or_succ b) ?_ ?_
  · have hb : ((b ≐ zero) :: Γ) ⊢[PRAAx] b ≐ zero := Prf.hyp0
    have g0 : ((b ≐ zero) :: Γ) ⊢[PRAAx] gcd zero b ≐ zero :=
      (LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize.congrGcd (.eqRefl _) hb).eqTrans gcd_zero_zero
    exact succ_ne_zero' _ (h.wk.eqSymm.eqTrans g0)
  · have hb : ((b ≐ succ (pred b)) :: Γ) ⊢[PRAAx] b ≐ succ (pred b) := Prf.hyp0
    have d0 : ((b ≐ succ (pred b)) :: Γ) ⊢[PRAAx] dvd (succ (pred b)) zero := dvd_zero _
    have d1 : ((b ≐ succ (pred b)) :: Γ) ⊢[PRAAx] dvd (succ (pred b)) b := dvd_congr hb.eqSymm (dvd_self _)
    have g := gcd_greatest_at d0 d1
    exact eq_one_of_dvd_one hb (dvd_congr_left hb.eqSymm (dvd_congr h.wk g))

theorem mag_zero {a b c d : PTm k} (g1 : Γ ⊢[PRAAx] gcd a b ≐ one) (g2 : Γ ⊢[PRAAx] gcd c d ≐ one)
    (h : Γ ⊢[PRAAx] a * d ≐ b * c) (ha : Γ ⊢[PRAAx] a ≐ zero) : Γ ⊢[PRAAx] (a ≐ c) ⋏ (b ≐ d) := by
  have hb : Γ ⊢[PRAAx] b ≐ one :=
    one_of_gcd_zero ((LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize.congrGcd ha.eqSymm (.eqRefl _)).eqTrans g1)
  have e := natEq h; have za := natEq ha; have ob := natEq hb
  have hc : Γ ⊢[PRAAx] c ≐ zero := by
    ipra_lc -e + 𝔞 d * za - 𝔞 c * ob
  have hd : Γ ⊢[PRAAx] d ≐ one :=
    one_of_gcd_zero ((LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize.congrGcd hc.eqSymm (.eqRefl _)).eqTrans g2)
  exact .andI (ha.eqTrans hc.eqSymm) (hb.eqTrans hd.eqSymm)

theorem mag_pos_zero {a b c d : PTm k} (g2 : Γ ⊢[PRAAx] gcd c d ≐ one)
    (h : Γ ⊢[PRAAx] a * d ≐ b * c) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hc : Γ ⊢[PRAAx] c ≐ zero) :
    Γ ⊢[PRAAx] Fm.bot := by
  have e := natEq h; have zc := natEq hc
  have hd : Γ ⊢[PRAAx] d ≐ zero := by
    refine mul_cancel ha ?_
    ipra_lc e + 𝔞 b * zc
  have g0 := (LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize.congrGcd hc hd).eqTrans gcd_zero_zero
  exact succ_ne_zero' _ (g2.eqSymm.eqTrans g0)

/-- Primitive natural pairs with `a d = b c` are equal, zero coordinates included. -/
theorem mag_unique {a b c d : PTm k} (g1 : Γ ⊢[PRAAx] gcd a b ≐ one) (g2 : Γ ⊢[PRAAx] gcd c d ≐ one)
    (h : Γ ⊢[PRAAx] a * d ≐ b * c) : Γ ⊢[PRAAx] (a ≐ c) ⋏ (b ≐ d) := by
  refine .orE (zero_or_succ a) (mag_zero g1.wk g2.wk h.wk Prf.hyp0) ?_
  refine .orE (zero_or_succ c) ?_ ?_
  · exact .botE _ (mag_pos_zero g2.wk.wk h.wk.wk Prf.hyp1 Prf.hyp0)
  · exact norm_unique Prf.hyp1 Prf.hyp0 g1.wk.wk g2.wk.wk h.wk.wk

theorem cross_nat {sa ma sb mb sc mc sd md : PTm k} (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) :
    Γ ⊢[PRAAx] (monus one sa * ma) * (monus one sd * md) + (sa * ma) * (sd * md) +
        ((monus one sb * mb) * (sc * mc) + (sb * mb) * (monus one sc * mc)) ≐
      (monus one sb * mb) * (monus one sc * mc) + (sb * mb) * (sc * mc) +
        ((monus one sa * ma) * (sd * md) + (sa * ma) * (monus one sd * md)) := h

theorem le_zero_eq {x : PTm k} (hx : Γ ⊢[PRAAx] le x zero) : Γ ⊢[PRAAx] x ≐ zero :=
  (monus_zero x).eqSymm.eqTrans hx

section Cases
variable {sa ma sb mb sc mc sd md : PTm k}

/-- Equal signs `s_b = s_d = 0`: the magnitudes satisfy `a d = b c`. -/
theorem case_00 (ha : Γ ⊢[PRAAx] sa ≐ zero) (hc : Γ ⊢[PRAAx] sc ≐ zero)
    (hb : Γ ⊢[PRAAx] sb ≐ zero) (hd : Γ ⊢[PRAAx] sd ≐ zero)
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) : Γ ⊢[PRAAx] ma * md ≐ mb * mc := by
  ipra_lc natEq (cross_nat h) + 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ha -
    𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq hc -
    𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ((congrMonus (.eqRefl one) ha).eqTrans (monus_zero (Γ := Γ) one)) +
    𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq ((congrMonus (.eqRefl one) hc).eqTrans (monus_zero (Γ := Γ) one)) -
    𝔞 mb * 𝔞 mc * natEq hb + 𝔞 ma * 𝔞 md * natEq hd +
    𝔞 mb * 𝔞 mc * natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_zero (Γ := Γ) one)) -
    𝔞 ma * 𝔞 md * natEq ((congrMonus (.eqRefl one) hd).eqTrans (monus_zero (Γ := Γ) one))

/-- Equal signs `s_b = s_d = 1`: the magnitudes satisfy `a d = b c`. -/
theorem case_11 (ha : Γ ⊢[PRAAx] sa ≐ zero) (hc : Γ ⊢[PRAAx] sc ≐ zero)
    (hb : Γ ⊢[PRAAx] sb ≐ one) (hd : Γ ⊢[PRAAx] sd ≐ one)
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) : Γ ⊢[PRAAx] ma * md ≐ mb * mc := by
  ipra_lc -natEq (cross_nat h) - 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ha +
    𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq hc +
    𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ((congrMonus (.eqRefl one) ha).eqTrans (monus_zero (Γ := Γ) one)) -
    𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq ((congrMonus (.eqRefl one) hc).eqTrans (monus_zero (Γ := Γ) one)) +
    𝔞 mb * 𝔞 mc * natEq hb - 𝔞 ma * 𝔞 md * natEq hd -
    𝔞 mb * 𝔞 mc * natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_self (Γ := Γ) one)) +
    𝔞 ma * 𝔞 md * natEq ((congrMonus (.eqRefl one) hd).eqTrans (monus_self (Γ := Γ) one))

/-- `s_b = 0`, `s_d = 1` is impossible. -/
theorem case_01 (ha : Γ ⊢[PRAAx] sa ≐ zero) (hc : Γ ⊢[PRAAx] sc ≐ zero)
    (hb : Γ ⊢[PRAAx] sb ≐ zero) (hd : Γ ⊢[PRAAx] sd ≐ one)
    (ld : Γ ⊢[PRAAx] le sd mc) (ldd : Γ ⊢[PRAAx] le sd md) (g1 : Γ ⊢[PRAAx] gcd ma mb ≐ one)
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) : Γ ⊢[PRAAx] Fm.bot := by
  have za := natEq ha; have zc := natEq hc
  have zb := natEq hb; have zd := natEq hd
  have sm : Γ ⊢[PRAAx] ma * md + mb * mc ≐ zero := by
    ipra_lc -natEq (cross_nat h) - 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * za +
      𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * zc +
      𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ((congrMonus (.eqRefl one) ha).eqTrans (monus_zero (Γ := Γ) one)) -
      𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq ((congrMonus (.eqRefl one) hc).eqTrans (monus_zero (Γ := Γ) one)) +
      𝔞 mb * 𝔞 mc * zb - 𝔞 ma * 𝔞 md * zd -
      𝔞 mb * 𝔞 mc * natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_zero (Γ := Γ) one)) +
      𝔞 ma * 𝔞 md * natEq ((congrMonus (.eqRefl one) hd).eqTrans (monus_self (Γ := Γ) one))
  have s := natEq sm
  have pc : Γ ⊢[PRAAx] le one mc := le_congr hd (.eqRefl _) ld
  have pd : Γ ⊢[PRAAx] le one md := le_congr hd (.eqRefl _) ldd
  have a0 : Γ ⊢[PRAAx] le ma zero := by ipra_le 𝔞 ma * sl pd + 𝔞 mb * 𝔞 mc using linear_combination -s
  have b0 : Γ ⊢[PRAAx] le mb zero := by ipra_le 𝔞 mb * sl pc + 𝔞 ma * 𝔞 md using linear_combination -s
  have g0 := (LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize.congrGcd (le_zero_eq a0) (le_zero_eq b0)).eqTrans
    gcd_zero_zero
  exact succ_ne_zero' _ (g1.eqSymm.eqTrans g0)

/-- `s_b = 1`, `s_d = 0` is impossible. -/
theorem case_10 (ha : Γ ⊢[PRAAx] sa ≐ zero) (hc : Γ ⊢[PRAAx] sc ≐ zero)
    (hb : Γ ⊢[PRAAx] sb ≐ one) (hd : Γ ⊢[PRAAx] sd ≐ zero)
    (lb : Γ ⊢[PRAAx] le sb ma) (lbb : Γ ⊢[PRAAx] le sb mb) (g2 : Γ ⊢[PRAAx] gcd mc md ≐ one)
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) : Γ ⊢[PRAAx] Fm.bot := by
  have za := natEq ha; have zc := natEq hc
  have zb := natEq hb; have zd := natEq hd
  have sm : Γ ⊢[PRAAx] ma * md + mb * mc ≐ zero := by
    ipra_lc natEq (cross_nat h) + 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * za -
      𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * zc -
      𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ((congrMonus (.eqRefl one) ha).eqTrans (monus_zero (Γ := Γ) one)) +
      𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq ((congrMonus (.eqRefl one) hc).eqTrans (monus_zero (Γ := Γ) one)) -
      𝔞 mb * 𝔞 mc * zb + 𝔞 ma * 𝔞 md * zd +
      𝔞 mb * 𝔞 mc * natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_self (Γ := Γ) one)) -
      𝔞 ma * 𝔞 md * natEq ((congrMonus (.eqRefl one) hd).eqTrans (monus_zero (Γ := Γ) one))
  have s := natEq sm
  have pa : Γ ⊢[PRAAx] le one ma := le_congr hb (.eqRefl _) lb
  have pb : Γ ⊢[PRAAx] le one mb := le_congr hb (.eqRefl _) lbb
  have d0 : Γ ⊢[PRAAx] le md zero := by ipra_le 𝔞 md * sl pa + 𝔞 mb * 𝔞 mc using linear_combination -s
  have c0 : Γ ⊢[PRAAx] le mc zero := by ipra_le 𝔞 mc * sl pb + 𝔞 ma * 𝔞 md using linear_combination -s
  have g0 := (LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize.congrGcd (le_zero_eq c0) (le_zero_eq d0)).eqTrans
    gcd_zero_zero
  exact succ_ne_zero' _ (g2.eqSymm.eqTrans g0)

end Cases

/-- `lem:normalize` on `P^1` with signs: two normalized signed pairs on the same point are equal. -/
theorem signed_unique {sa ma sb mb sc mc sd md : PTm k}
    (ha : Γ ⊢[PRAAx] sa ≐ zero) (hc : Γ ⊢[PRAAx] sc ≐ zero)
    (bb : Γ ⊢[PRAAx] (sb ≐ zero) ⋎ (sb ≐ one)) (bd : Γ ⊢[PRAAx] (sd ≐ zero) ⋎ (sd ≐ one))
    (lb : Γ ⊢[PRAAx] le sb ma) (ld : Γ ⊢[PRAAx] le sd mc)
    (lbb : Γ ⊢[PRAAx] le sb mb) (ldd : Γ ⊢[PRAAx] le sd md)
    (g1 : Γ ⊢[PRAAx] gcd ma mb ≐ one) (g2 : Γ ⊢[PRAAx] gcd mc md ≐ one)
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) :
    Γ ⊢[PRAAx] ((ma ≐ mc) ⋏ (mb ≐ md)) ⋏ (sb ≐ sd) := by
  refine .orE bb ?_ ?_
  · refine .orE bd.wk ?_ ?_
    · exact .andI (mag_unique g1.wk.wk g2.wk.wk (case_00 ha.wk.wk hc.wk.wk Prf.hyp1 Prf.hyp0 h.wk.wk))
        (Prf.hyp1.eqTrans Prf.hyp0.eqSymm)
    · exact .botE _ (case_01 ha.wk.wk hc.wk.wk Prf.hyp1 Prf.hyp0 ld.wk.wk ldd.wk.wk g1.wk.wk h.wk.wk)
  · refine .orE bd.wk ?_ ?_
    · exact .botE _ (case_10 ha.wk.wk hc.wk.wk Prf.hyp1 Prf.hyp0 lb.wk.wk lbb.wk.wk g2.wk.wk h.wk.wk)
    · exact .andI (mag_unique g1.wk.wk g2.wk.wk (case_11 ha.wk.wk hc.wk.wk Prf.hyp1 Prf.hyp0 h.wk.wk))
        (Prf.hyp1.eqTrans Prf.hyp0.eqSymm)

end LeanProofs.IPRA.DiophantineNumberTheory.SignedLine
