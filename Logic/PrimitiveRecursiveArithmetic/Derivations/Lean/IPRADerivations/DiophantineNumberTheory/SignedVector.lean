import IPRADerivations.DiophantineNumberTheory.SignedLine
import IPRADerivations.DiophantineNumberTheory.NorthcottLocus
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Signed primitive representatives in every dimension

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemma `lem:normalize`: "obtained by dividing by
`g = gcd(|v_0|, …, |v_n|)` and choosing the sign so the first nonzero coordinate is positive. Two such
representatives of the same rational projective point are equal", for signed vectors of any length.

A signed vector is a sign body `S` (bits) and a magnitude body `M` (`SignedLine.sv`). It is normalized when
`gcd(M) = 1`, zero entries have sign `0` (`S_i ≤ M_i`), and a sign can be `1` only after a nonzero entry
(`S_i ≤ gcd(M_0, …, M_{i−1})`), i.e. the first nonzero entry is positive.

The first nonzero index `i_0 = wit M N x` is the bounded least witness of `Foundations/BoundedReflection`. Both
vectors vanish below `i_0` and are positive at `i_0`; the cross equations with `i_0` then give, entry by entry,
`|v_{i_0}| |w_i| = |v_i| |w_{i_0}|` and equal signs (`index_rel`), and `GcdUnique.index_eq` gives
`|v_{i_0}| = |w_{i_0}|`.

* `sum_01`, `sum_10`, `index_rel`, `d_zero_b`, `d_zero_c`: the two-entry arguments;
* `signed_vector_unique`: two normalized signed vectors on the same projective point are equal.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SignedVector

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.SignedLine (sv crossF cross_nat case_00 case_11 le_zero_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gv)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize (gv_all_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdUnique (index_eq sh_inst)
open LeanProofs.IPRA.DiophantineNumberTheory.ProjectiveVectorUnique (propJ)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim ex_least ex_none)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Pairs
variable {sa ma sb mb sc mc sd md : PTm k}

theorem sum_01 (ha : Γ ⊢[PRAAx] sa ≐ zero) (hc : Γ ⊢[PRAAx] sc ≐ zero)
    (hb : Γ ⊢[PRAAx] sb ≐ zero) (hd : Γ ⊢[PRAAx] sd ≐ one)
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) : Γ ⊢[PRAAx] ma * md + mb * mc ≐ zero := by
  ipra_lc -natEq (cross_nat h) - 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ha +
    𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq hc +
    𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ((congrMonus (.eqRefl one) ha).eqTrans (monus_zero (Γ := Γ) one)) -
    𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq ((congrMonus (.eqRefl one) hc).eqTrans (monus_zero (Γ := Γ) one)) +
    𝔞 mb * 𝔞 mc * natEq hb - 𝔞 ma * 𝔞 md * natEq hd -
    𝔞 mb * 𝔞 mc * natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_zero (Γ := Γ) one)) +
    𝔞 ma * 𝔞 md * natEq ((congrMonus (.eqRefl one) hd).eqTrans (monus_self (Γ := Γ) one))

theorem sum_10 (ha : Γ ⊢[PRAAx] sa ≐ zero) (hc : Γ ⊢[PRAAx] sc ≐ zero)
    (hb : Γ ⊢[PRAAx] sb ≐ one) (hd : Γ ⊢[PRAAx] sd ≐ zero)
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) : Γ ⊢[PRAAx] ma * md + mb * mc ≐ zero := by
  ipra_lc natEq (cross_nat h) + 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ha -
    𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq hc -
    𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * natEq ((congrMonus (.eqRefl one) ha).eqTrans (monus_zero (Γ := Γ) one)) +
    𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * natEq ((congrMonus (.eqRefl one) hc).eqTrans (monus_zero (Γ := Γ) one)) -
    𝔞 mb * 𝔞 mc * natEq hb + 𝔞 ma * 𝔞 md * natEq hd +
    𝔞 mb * 𝔞 mc * natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_self (Γ := Γ) one)) -
    𝔞 ma * 𝔞 md * natEq ((congrMonus (.eqRefl one) hd).eqTrans (monus_zero (Γ := Γ) one))

alias left_zero := Common.add_eq_zero_left

alias right_zero := Common.add_eq_zero_right

/-- `p ≥ 1` and `p q = 0` give `q = 0`. -/
theorem zero_of_mul {p q : PTm k} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (h : Γ ⊢[PRAAx] p * q ≐ zero) :
    Γ ⊢[PRAAx] q ≐ zero := by
  have e := natEq h
  exact mul_cancel hp (by apply deriveNat; ipra_simps; linear_combination e)

theorem not_one_le_zero {x : PTm k} (h1 : Γ ⊢[PRAAx] le one x) (h0 : Γ ⊢[PRAAx] x ≐ zero) {φ : Fm PTm k} :
    Γ ⊢[PRAAx] φ :=
  .botE _ (not_succ_le_self zero _ (le_congr (.eqRefl _) h0 h1))

/-- With first signs `0` and first magnitudes positive: `|a| |d| = |b| |c|` and equal second signs. -/
theorem index_rel (ha : Γ ⊢[PRAAx] sa ≐ zero) (hc : Γ ⊢[PRAAx] sc ≐ zero)
    (pa : Γ ⊢[PRAAx] ma ≐ succ (pred ma)) (pc : Γ ⊢[PRAAx] mc ≐ succ (pred mc))
    (bb : Γ ⊢[PRAAx] (sb ≐ zero) ⋎ (sb ≐ one)) (bd : Γ ⊢[PRAAx] (sd ≐ zero) ⋎ (sd ≐ one))
    (lbb : Γ ⊢[PRAAx] le sb mb) (ldd : Γ ⊢[PRAAx] le sd md)
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) :
    Γ ⊢[PRAAx] (ma * md ≐ mb * mc) ⋏ (sb ≐ sd) := by
  refine .orE bb ?_ ?_
  · refine .orE bd.wk ?_ ?_
    · exact .andI (case_00 ha.wk.wk hc.wk.wk Prf.hyp1 Prf.hyp0 h.wk.wk) (Prf.hyp1.eqTrans Prf.hyp0.eqSymm)
    · have s := sum_01 ha.wk.wk hc.wk.wk Prf.hyp1 Prf.hyp0 h.wk.wk
      have d0 := zero_of_mul pa.wk.wk (left_zero s)
      exact not_one_le_zero (le_congr Prf.hyp0 (.eqRefl _) ldd.wk.wk) d0
  · refine .orE bd.wk ?_ ?_
    · have s := sum_10 ha.wk.wk hc.wk.wk Prf.hyp1 Prf.hyp0 h.wk.wk
      have e := natEq (right_zero s)
      have b0 := zero_of_mul (q := mb) pc.wk.wk (by apply deriveNat; ipra_simps; linear_combination e)
      exact not_one_le_zero (le_congr Prf.hyp1 (.eqRefl _) lbb.wk.wk) b0
    · exact .andI (case_11 ha.wk.wk hc.wk.wk Prf.hyp1 Prf.hyp0 h.wk.wk) (Prf.hyp1.eqTrans Prf.hyp0.eqSymm)

/-- With `a` positive of sign `0` and `b = 0`: `d = 0`. -/
theorem d_zero_b (ha : Γ ⊢[PRAAx] sa ≐ zero) (pa : Γ ⊢[PRAAx] ma ≐ succ (pred ma))
    (hb : Γ ⊢[PRAAx] sb ≐ zero) (mb0 : Γ ⊢[PRAAx] mb ≐ zero) (bd : Γ ⊢[PRAAx] (sd ≐ zero) ⋎ (sd ≐ one))
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) : Γ ⊢[PRAAx] md ≐ zero := by
  have e := natEq (cross_nat h)
  have za := natEq ha; have zb := natEq hb; have m0 := natEq mb0
  have ua := natEq ((congrMonus (.eqRefl one) ha).eqTrans (monus_zero (Γ := Γ) one))
  have ub := natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_zero (Γ := Γ) one))
  refine zero_of_mul pa (.orE bd ?_ ?_)
  · have zd := natEq (Prf.hyp0 : ((sd ≐ zero) :: Γ) ⊢[PRAAx] sd ≐ zero)
    have ud := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((sd ≐ zero) :: Γ) ⊢[PRAAx] sd ≐ zero)).eqTrans
      (monus_zero one))
    have e' := natEq ((cross_nat h).wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _)
    have za' := natEq (ha.wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _); have zb' := natEq (hb.wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _)
    have m0' := natEq (mb0.wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _)
    have ua' := natEq (((congrMonus (.eqRefl one) ha).eqTrans (monus_zero one)).wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _)
    apply deriveNat; ipra_simps
    linear_combination e' + 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * za' -
      𝔞 mb * 𝔞 mc * (𝔞 (monus one sc) - 𝔞 sc) * zb' + 𝔞 (monus one sb) * 𝔞 mc * (𝔞 (monus one sc) - 𝔞 sc) * m0' +
      𝔞 (monus one sa) * 𝔞 ma * 𝔞 md * zd - 𝔞 (monus one sd) * 𝔞 ma * 𝔞 md * ua' - 𝔞 ma * 𝔞 md * ud
  · have zd := natEq (Prf.hyp0 : ((sd ≐ one) :: Γ) ⊢[PRAAx] sd ≐ one)
    have ud := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((sd ≐ one) :: Γ) ⊢[PRAAx] sd ≐ one)).eqTrans
      (monus_self one))
    have e' := natEq ((cross_nat h).wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _)
    have za' := natEq (ha.wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _); have zb' := natEq (hb.wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _)
    have m0' := natEq (mb0.wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _)
    have ua' := natEq (((congrMonus (.eqRefl one) ha).eqTrans (monus_zero one)).wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _)
    apply deriveNat; ipra_simps
    linear_combination -e' - 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * za' +
      𝔞 mb * 𝔞 mc * (𝔞 (monus one sc) - 𝔞 sc) * zb' - 𝔞 (monus one sb) * 𝔞 mc * (𝔞 (monus one sc) - 𝔞 sc) * m0' -
      𝔞 (monus one sa) * 𝔞 ma * 𝔞 md * zd + 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 1) * ua' + 𝔞 ma * 𝔞 md * ud

/-- With `a` positive of sign `0` and `c = 0` of sign `0`: `d = 0`. -/
theorem d_zero_c (ha : Γ ⊢[PRAAx] sa ≐ zero) (pa : Γ ⊢[PRAAx] ma ≐ succ (pred ma))
    (hc : Γ ⊢[PRAAx] sc ≐ zero) (mc0 : Γ ⊢[PRAAx] mc ≐ zero) (bd : Γ ⊢[PRAAx] (sd ≐ zero) ⋎ (sd ≐ one))
    (h : Γ ⊢[PRAAx] crossF sa ma sb mb sc mc sd md) : Γ ⊢[PRAAx] md ≐ zero := by
  refine zero_of_mul pa (.orE bd ?_ ?_)
  · have zd := natEq (Prf.hyp0 : ((sd ≐ zero) :: Γ) ⊢[PRAAx] sd ≐ zero)
    have ud := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((sd ≐ zero) :: Γ) ⊢[PRAAx] sd ≐ zero)).eqTrans
      (monus_zero one))
    have e' := natEq ((cross_nat h).wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _)
    have za' := natEq (ha.wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _); have zc' := natEq (hc.wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _)
    have m0' := natEq (mc0.wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _)
    have ua' := natEq (((congrMonus (.eqRefl one) ha).eqTrans (monus_zero one)).wk : ((sd ≐ zero) :: Γ) ⊢[PRAAx] _)
    apply deriveNat; ipra_simps
    linear_combination e' + 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * za' -
      𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * zc' + 𝔞 (monus one sc) * 𝔞 mb * (𝔞 (monus one sb) - 𝔞 sb) * m0' +
      𝔞 (monus one sa) * 𝔞 ma * 𝔞 md * zd - 𝔞 (monus one sd) * 𝔞 ma * 𝔞 md * ua' - 𝔞 ma * 𝔞 md * ud
  · have zd := natEq (Prf.hyp0 : ((sd ≐ one) :: Γ) ⊢[PRAAx] sd ≐ one)
    have ud := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((sd ≐ one) :: Γ) ⊢[PRAAx] sd ≐ one)).eqTrans
      (monus_self one))
    have e' := natEq ((cross_nat h).wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _)
    have za' := natEq (ha.wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _); have zc' := natEq (hc.wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _)
    have m0' := natEq (mc0.wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _)
    have ua' := natEq (((congrMonus (.eqRefl one) ha).eqTrans (monus_zero one)).wk : ((sd ≐ one) :: Γ) ⊢[PRAAx] _)
    apply deriveNat; ipra_simps
    linear_combination -e' - 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 𝔞 sd) * za' +
      𝔞 mb * 𝔞 mc * (𝔞 (monus one sb) - 𝔞 sb) * zc' - 𝔞 (monus one sc) * 𝔞 mb * (𝔞 (monus one sb) - 𝔞 sb) * m0' -
      𝔞 (monus one sa) * 𝔞 ma * 𝔞 md * zd + 𝔞 ma * 𝔞 md * (𝔞 (monus one sd) - 1) * ua' + 𝔞 ma * 𝔞 md * ud

end Pairs

/-! ## The main theorem -/

section Main

open LeanProofs.IPRA.DiophantineNumberTheory.GcdUnique (sh shift_succ' shift_pred' shift_zero' shift_one')

variable (SV MV SW MW : PTm 2) {N x : PTm k}

theorem shift_wit : Syn.shift (wit MV N x) = wit MV (Syn.shift N) (Syn.shift x) := by simp [Syn.shift]

/-- Moving `t ≐ zero` for an entry under the binder. -/
theorem sh_zero {V : PTm 2} {j : PTm k} (h : Γ ⊢[PRAAx] inst2 V j x ≐ zero) :
    Γ.map Fm.shift ⊢[PRAAx] inst2 V (Syn.shift j) (Syn.shift x) ≐ zero := by
  have e := sh h; rw [sh_inst, shift_zero'] at e; exact e

theorem sh_pos {V : PTm 2} {j : PTm k} (h : Γ ⊢[PRAAx] inst2 V j x ≐ succ (pred (inst2 V j x))) :
    Γ.map Fm.shift ⊢[PRAAx] inst2 V (Syn.shift j) (Syn.shift x) ≐ succ (pred (inst2 V (Syn.shift j) (Syn.shift x))) := by
  have e := sh h; rw [shift_succ', shift_pred', sh_inst] at e; exact e

theorem sh_eq {V W : PTm 2} {j : PTm k} (h : Γ ⊢[PRAAx] inst2 V j x ≐ inst2 W j x) :
    Γ.map Fm.shift ⊢[PRAAx] inst2 V (Syn.shift j) (Syn.shift x) ≐ inst2 W (Syn.shift j) (Syn.shift x) := by
  have e := sh h; rw [sh_inst, sh_inst] at e; exact e

theorem pos_of_ne {t : PTm k} (h : Γ ⊢[PRAAx] neg (t ≐ zero)) : Γ ⊢[PRAAx] t ≐ succ (pred t) :=
  .orE (zero_or_succ t) (.botE _ (Prf.impE h.wk Prf.hyp0)) Prf.hyp0

/-- `lem:normalize` with signs in every dimension: two normalized signed vectors whose cross equations with
the first nonzero index `i_0 = wit M_v N x` of `v` hold are equal, magnitudes and signs. -/
theorem signed_vector_unique
    (hv1 : Γ ⊢[PRAAx] gv MV N x ≐ one) (hw1 : Γ ⊢[PRAAx] gv MW N x ≐ one)
    (bV : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 SV (var 0) (Syn.shift x) ≐ zero) ⋎ (inst2 SV (var 0) (Syn.shift x) ≐ one)))
    (bW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 SW (var 0) (Syn.shift x) ≐ zero) ⋎ (inst2 SW (var 0) (Syn.shift x) ≐ one)))
    (zV : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 SV (var 0) (Syn.shift x)) (inst2 MV (var 0) (Syn.shift x))))
    (zW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 SW (var 0) (Syn.shift x)) (inst2 MW (var 0) (Syn.shift x))))
    (fV : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 SV (var 0) (Syn.shift x)) (gv MV (var 0) (Syn.shift x))))
    (fW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 SW (var 0) (Syn.shift x)) (gv MW (var 0) (Syn.shift x))))
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      crossF (inst2 SV (Syn.shift (wit MV N x)) (Syn.shift x)) (inst2 MV (Syn.shift (wit MV N x)) (Syn.shift x))
        (inst2 SV (var 0) (Syn.shift x)) (inst2 MV (var 0) (Syn.shift x))
        (inst2 SW (Syn.shift (wit MV N x)) (Syn.shift x)) (inst2 MW (Syn.shift (wit MV N x)) (Syn.shift x))
        (inst2 SW (var 0) (Syn.shift x)) (inst2 MW (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 MW (var 0) (Syn.shift x) ≐ inst2 MV (var 0) (Syn.shift x)) ⋏
        (inst2 SW (var 0) (Syn.shift x) ≐ inst2 SV (var 0) (Syn.shift x))) := by
  -- (A) some entry of `v` is nonzero
  have hex : Γ ⊢[PRAAx] exB MV N x ≐ one := by
    refine .orE (ex_cases MV N x) ?_ Prf.hyp0
    have hz : ((exB MV N x ≐ zero) :: Γ) ⊢[PRAAx] exB MV N x ≐ zero := Prf.hyp0
    have hzs : ((exB MV N x ≐ zero) :: Γ).map Fm.shift ⊢[PRAAx] exB MV (Syn.shift N) (Syn.shift x) ≐ zero := by
      have e := hz.shift; simpa [Fm.shift, Syn.shift] using e
    have gz := gv_all_zero MV (.allI (.impI (ex_none MV hzs.wk Prf.hyp0)))
    exact succ_ne_zero' _ (hv1.wk.eqSymm.eqTrans gz)
  have el := ex_elim MV hex
  have hi0 : Γ ⊢[PRAAx] lt (wit MV N x) N := Prf.andE₁ el
  have pA := pos_of_ne (Prf.andE₂ el)
  -- (C) `v` vanishes below `i_0`, so `s_{v, i_0} = 0`
  have pzv : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (wit MV N x)) ⟶ inst2 MV (var 0) (Syn.shift x) ≐ zero) := by
    refine .allI (.impI ?_)
    have eqw : (lt (var 0) (Syn.shift (wit MV N x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        Syn.shift (wit MV N x) ≐ wit MV (Syn.shift N) (Syn.shift x) := by
      rw [shift_wit]; exact .eqRefl _
    have hj := lt_congr (.eqRefl _) eqw (Prf.hyp0 : (lt (var 0) (Syn.shift (wit MV N x)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    exact ex_least MV hj
  have gvz : Γ ⊢[PRAAx] gv MV (wit MV N x) x ≐ zero := gv_all_zero MV pzv
  have atv : Γ ⊢[PRAAx] le (inst2 SV (wit MV N x) x) (gv MV (wit MV N x) x) := by
    have h2 := Prf.allE (wit MV N x) fV
    simp only [Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift] at h2
    exact Prf.impE h2 hi0
  have sv0 : Γ ⊢[PRAAx] inst2 SV (wit MV N x) x ≐ zero := le_zero_eq (le_congr (.eqRefl _) gvz atv)
  -- shifted facts about `i_0`
  have sv0s := sh_zero (Γ := Γ) sv0
  have pAs := sh_pos (Γ := Γ) pA
  have hi0s : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift (wit MV N x)) (Syn.shift N) := by
    have e := hi0.shift; simpa [Fm.shift, Syn.shift] using e
  -- (D) `w` vanishes below `i_0`, so `s_{w, i_0} = 0`
  have pzw : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (wit MV N x)) ⟶ inst2 MW (var 0) (Syn.shift x) ≐ zero) := by
    refine .allI (.impI ?_)
    have hj : (lt (var 0) (Syn.shift (wit MV N x)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift (wit MV N x)) :=
      Prf.hyp0
    have hjN : (lt (var 0) (Syn.shift (wit MV N x)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift N) :=
      le_trans hj (le_trans (le_succ_self _) hi0s.wk)
    have mvj := Prf.impE pzv.allOpen.wk hj
    have svj := le_zero_eq (le_congr (.eqRefl _) mvj (Prf.impE zV.allOpen.wk hjN))
    exact d_zero_b sv0s.wk pAs.wk svj mvj (Prf.impE bW.allOpen.wk hjN) (Prf.impE hp.allOpen.wk hjN)
  have gwz : Γ ⊢[PRAAx] gv MW (wit MV N x) x ≐ zero := gv_all_zero MW pzw
  have atw : Γ ⊢[PRAAx] le (inst2 SW (wit MV N x) x) (gv MW (wit MV N x) x) := by
    have h2 := Prf.allE (wit MV N x) fW
    simp only [Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift] at h2
    exact Prf.impE h2 hi0
  have sw0 : Γ ⊢[PRAAx] inst2 SW (wit MV N x) x ≐ zero := le_zero_eq (le_congr (.eqRefl _) gwz atw)
  have sw0s := sh_zero (Γ := Γ) sw0
  -- (E) `w_{i_0} ≠ 0`
  have pB : Γ ⊢[PRAAx] inst2 MW (wit MV N x) x ≐ succ (pred (inst2 MW (wit MV N x) x)) := by
    refine .orE (zero_or_succ (inst2 MW (wit MV N x) x)) ?_ Prf.hyp0
    let E := (inst2 MW (wit MV N x) x ≐ zero) :: Γ
    have m0 : E ⊢[PRAAx] inst2 MW (wit MV N x) x ≐ zero := Prf.hyp0
    have m0s := sh_zero (Γ := E) m0
    have az : E ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 MW (var 0) (Syn.shift x) ≐ zero) := by
      refine .allI (.impI ?_)
      have hiN : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
      exact d_zero_c (sv0s.wk.wk : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] _)
        (pAs.wk.wk : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] _)
        (sw0s.wk.wk : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] _) m0s.wk
        (Prf.impE (bW.wk : E ⊢[PRAAx] _).allOpen.wk hiN) (Prf.impE (hp.wk : E ⊢[PRAAx] _).allOpen.wk hiN)
    exact succ_ne_zero' _ (hw1.wk.eqSymm.eqTrans (gv_all_zero MW az))
  have pBs := sh_pos (Γ := Γ) pB
  -- (F) the per-entry relations
  have rel : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 MV (Syn.shift (wit MV N x)) (Syn.shift x) * inst2 MW (var 0) (Syn.shift x) ≐
        inst2 MV (var 0) (Syn.shift x) * inst2 MW (Syn.shift (wit MV N x)) (Syn.shift x)) ⋏
      (inst2 SV (var 0) (Syn.shift x) ≐ inst2 SW (var 0) (Syn.shift x))) := by
    refine .allI (.impI ?_)
    exact index_rel sv0s.wk sw0s.wk pAs.wk pBs.wk (Prf.impE bV.allOpen.wk Prf.hyp0) (Prf.impE bW.allOpen.wk Prf.hyp0)
      (Prf.impE zV.allOpen.wk Prf.hyp0) (Prf.impE zW.allOpen.wk Prf.hyp0) (Prf.impE hp.allOpen.wk Prf.hyp0)
  -- (G) `|v_{i_0}| = |w_{i_0}|`
  have pj : Γ ⊢[PRAAx] propJ MV MW (wit MV N x) N x :=
    .allI (.impI (Prf.andE₁ (Prf.impE rel.allOpen.wk Prf.hyp0)))
  have ab : Γ ⊢[PRAAx] inst2 MW (wit MV N x) x ≐ inst2 MV (wit MV N x) x := index_eq pj hv1 hw1
  have abs := sh_eq (Γ := Γ) ab
  -- (H) conclusion
  refine .allI (.impI ?_)
  have r := Prf.impE rel.allOpen.wk Prf.hyp0
  refine .andI (mul_cancel pAs.wk ?_) (Prf.andE₂ r).eqSymm
  ipra_lc natEq (Prf.andE₁ r) +
    𝔞 (inst2 MV (var 0) (Syn.shift x)) * natEq (abs.wk : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] _)

end Main

end LeanProofs.IPRA.DiophantineNumberTheory.SignedVector
