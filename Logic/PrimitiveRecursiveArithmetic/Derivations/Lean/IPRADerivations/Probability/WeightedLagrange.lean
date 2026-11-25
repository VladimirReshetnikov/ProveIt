import IPRADerivations.Probability.ExpectationCorollaries
import IPRADerivations.Core.LinearCombination

/-!
# The weighted Lagrange identity and equality in Cauchy–Schwarz

Packet: `probability/expected_value_ipra_2026-11-16`, Lemma `lem:lagrange` and Corollary
`cor:cs-equality`. For natural lists `u_i, v_i` and weights `w_i` on `i < M`, put
`A = ∑ w_i u_i²`, `B = ∑ w_i v_i²`, `C = ∑ w_i u_i v_i`. With `|a − b| = (a ∸ b) + (b ∸ a)`:

* `row_identity`: `∑_{i<M} w_i |U v_i − V u_i|² + 2 U V C = U² B + V² A` (pointwise `ad_sq`);
* `lagrange` (`lem:lagrange`): `A B = C² + ∑_{j<M} w_j ∑_{i<j} w_i |u_j v_i − v_j u_i|²`, by induction
  on `M` using `row_identity` for the new row;
* `cs_equality` (`cor:cs-equality`): `A B = C²` exactly when every term
  `w_j w_i |u_j v_i − v_j u_i|²` (`i < j < M`) vanishes.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.WeightedLagrange

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Probability.ExpectationCorollaries (zml)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Lagrange

variable (w u v : PTm 2)

abbrev Ab : PTm 2 := w * (u * u)
abbrev Bb : PTm 2 := w * (v * v)
abbrev Cb : PTm 2 := w * (u * v)

/-- `f(i, snd z)`. -/
abbrev sb (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

/-- `w_i |U v_i − V u_i|²`, over `0 = i`, `1 = ⟨⟨U, V⟩, x⟩`. -/
abbrev eB : PTm 2 := sb w * (ad (fstT (fstT (var 1)) * sb v) (sndT (fstT (var 1)) * sb u) *
  ad (fstT (fstT (var 1)) * sb v) (sndT (fstT (var 1)) * sb u))

/-- `w_j ∑_{i<j} w_i |u_j v_i − v_j u_i|²`, over `0 = j`, `1 = x`. -/
abbrev DB : PTm 2 := w * ap2 (sumF (eB w u v)) (var 0) (pairT (pairT u v) (var 1))

theorem inst2_sb (f : PTm 2) (i z : PTm n) : Syn.subst ![i, z] (sb f) = inst2 f i (sndT z) := by
  simp only [inst2, sb, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem inst2_eB (i z : PTm n) : inst2 (eB w u v) i z = inst2 w i (sndT z) *
    (ad (fstT (fstT z) * inst2 v i (sndT z)) (sndT (fstT z) * inst2 u i (sndT z)) *
      ad (fstT (fstT z) * inst2 v i (sndT z)) (sndT (fstT z) * inst2 u i (sndT z))) := by
  simp only [inst2, eB, ad, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, inst2_sb, subst_fstT, subst_sndT]
  simp

theorem eB_at (i U V x : PTm n) : Γ ⊢[PRAAx] inst2 (eB w u v) i (pairT (pairT U V) x) ≐
    inst2 w i x * (ad (U * inst2 v i x) (V * inst2 u i x) * ad (U * inst2 v i x) (V * inst2 u i x)) := by
  rw [inst2_eB]
  have hx : Γ ⊢[PRAAx] sndT (pairT (pairT U V) x) ≐ x := snd_pair _ _
  have hU : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT U V) x)) ≐ U := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have hV : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT U V) x)) ≐ V := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  have ha := congrMul hU (congrInst2 v (.eqRefl i) hx)
  have hb := congrMul hV (congrInst2 u (.eqRefl i) hx)
  have hd := congrAdd (congrMonus ha hb) (congrMonus hb ha)
  exact congrMul (congrInst2 w (.eqRefl i) hx) (congrMul hd hd)

theorem inst2_DB (j x : PTm n) :
    inst2 (DB w u v) j x = inst2 w j x * ap2 (sumF (eB w u v)) j (pairT (pairT (inst2 u j x) (inst2 v j x)) x) := by
  simp [inst2]

/-- One new row: `∑_{i<M} w_i |U v_i − V u_i|² + 2 U V C = U² B + V² A`. -/
theorem row_identity (U V x M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (eB w u v)) M (pairT (pairT U V) x) + two * (U * V) * ap2 (sumF (Cb w u v)) M x ≐
      U * U * ap2 (sumF (Bb w v)) M x + V * V * ap2 (sumF (Ab w u)) M x := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF (eB w u v)) (var 0) (pairT (pairT (Syn.shift U) (Syn.shift V)) (Syn.shift x)) +
      two * (Syn.shift U * Syn.shift V) * ap2 (sumF (Cb w u v)) (var 0) (Syn.shift x) ≐
      Syn.shift U * Syn.shift U * ap2 (sumF (Bb w v)) (var 0) (Syn.shift x) +
        Syn.shift V * Syn.shift V * ap2 (sumF (Ab w u)) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · ipra_lc [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] natEq (sum_zero (Γ := Γ) (eB w u v) (pairT (pairT U V) x)) +
        2 * 𝔞 U * 𝔞 V * natEq (sum_zero (Γ := Γ) (Cb w u v) x) - 𝔞 U * 𝔞 U * natEq (sum_zero (Γ := Γ) (Bb w v) x) -
        𝔞 V * 𝔞 V * natEq (sum_zero (Γ := Γ) (Ab w u) x)
    · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let D : List (Fm PTm (n + 1)) := (ap2 (sumF (eB w u v)) (var 0) (pairT (pairT (Syn.shift U) (Syn.shift V)) (Syn.shift x)) +
        two * (Syn.shift U * Syn.shift V) * ap2 (sumF (Cb w u v)) (var 0) (Syn.shift x) ≐
        Syn.shift U * Syn.shift U * ap2 (sumF (Bb w v)) (var 0) (Syn.shift x) +
          Syn.shift V * Syn.shift V * ap2 (sumF (Ab w u)) (var 0) (Syn.shift x)) :: Γ.map Fm.shift
      have s1 := sum_succ' (Γ := D) (eB w u v) (var 0) (pairT (pairT (Syn.shift U) (Syn.shift V)) (Syn.shift x))
      have s2 := sum_succ' (Γ := D) (Cb w u v) (var 0) (Syn.shift x)
      have s3 := sum_succ' (Γ := D) (Bb w v) (var 0) (Syn.shift x)
      have s4 := sum_succ' (Γ := D) (Ab w u) (var 0) (Syn.shift x)
      rw [inst2_mul', inst2_mul'] at s2 s3 s4
      ipra_lc natEq (Prf.hyp0 : D ⊢[PRAAx] _) + natEq (s1.eqTrans (congrAdd (.eqRefl _) (eB_at w u v _ _ _ _))) +
        2 * 𝔞 (Syn.shift U) * 𝔞 (Syn.shift V) * natEq s2 - 𝔞 (Syn.shift U) * 𝔞 (Syn.shift U) * natEq s3 -
        𝔞 (Syn.shift V) * 𝔞 (Syn.shift V) * natEq s4 +
        𝔞 (inst2 w (var 0) (Syn.shift x)) * natEq (ad_sq (Γ := D) (Syn.shift U * inst2 v (var 0) (Syn.shift x)) (Syn.shift V * inst2 u (var 0) (Syn.shift x)))
  have h := Prf.allE M hall
  simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact h

/-- `lem:lagrange`: `A B = C² + ∑_{j<M} w_j ∑_{i<j} w_i |u_j v_i − v_j u_i|²`. -/
theorem lagrange (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (Ab w u)) M x * ap2 (sumF (Bb w v)) M x ≐
      ap2 (sumF (Cb w u v)) M x * ap2 (sumF (Cb w u v)) M x + ap2 (sumF (DB w u v)) M x := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF (Ab w u)) (var 0) (Syn.shift x) * ap2 (sumF (Bb w v)) (var 0) (Syn.shift x) ≐
      ap2 (sumF (Cb w u v)) (var 0) (Syn.shift x) * ap2 (sumF (Cb w u v)) (var 0) (Syn.shift x) +
        ap2 (sumF (DB w u v)) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · ipra_lc [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] 𝔞 (ap2 (sumF (Bb w v)) zero x) * natEq (sum_zero (Γ := Γ) (Ab w u) x) -
        natEq (sum_zero (Γ := Γ) (DB w u v) x) -
        (𝔞 (ap2 (sumF (Cb w u v)) zero x)) * natEq (sum_zero (Γ := Γ) (Cb w u v) x)
    · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let D : List (Fm PTm (n + 1)) := (ap2 (sumF (Ab w u)) (var 0) (Syn.shift x) * ap2 (sumF (Bb w v)) (var 0) (Syn.shift x) ≐
        ap2 (sumF (Cb w u v)) (var 0) (Syn.shift x) * ap2 (sumF (Cb w u v)) (var 0) (Syn.shift x) +
          ap2 (sumF (DB w u v)) (var 0) (Syn.shift x)) :: Γ.map Fm.shift
      have sA := sum_succ' (Γ := D) (Ab w u) (var 0) (Syn.shift x)
      have sB := sum_succ' (Γ := D) (Bb w v) (var 0) (Syn.shift x)
      have sC := sum_succ' (Γ := D) (Cb w u v) (var 0) (Syn.shift x)
      have sD := sum_succ' (Γ := D) (DB w u v) (var 0) (Syn.shift x)
      rw [inst2_mul', inst2_mul'] at sA sB sC
      rw [inst2_DB] at sD
      ipra_lc natEq (Prf.hyp0 : D ⊢[PRAAx] _) -
        𝔞 (inst2 w (var 0) (Syn.shift x)) * natEq (row_identity (Γ := D) w u v (inst2 u (var 0) (Syn.shift x)) (inst2 v (var 0) (Syn.shift x)) (Syn.shift x) (var 0)) +
        𝔞 (ap2 (sumF (Bb w v)) (succ (var 0)) (Syn.shift x)) * natEq sA +
        (𝔞 (ap2 (sumF (Ab w u)) (var 0) (Syn.shift x)) + 𝔞 (inst2 w (var 0) (Syn.shift x)) * (𝔞 (inst2 u (var 0) (Syn.shift x)) * 𝔞 (inst2 u (var 0) (Syn.shift x)))) * natEq sB -
        (𝔞 (ap2 (sumF (Cb w u v)) (succ (var 0)) (Syn.shift x)) + 𝔞 (ap2 (sumF (Cb w u v)) (var 0) (Syn.shift x)) + 𝔞 (inst2 w (var 0) (Syn.shift x)) * (𝔞 (inst2 u (var 0) (Syn.shift x)) * 𝔞 (inst2 v (var 0) (Syn.shift x)))) * natEq sC -
        natEq sD
  have h := Prf.allE M hall
  simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h
  exact h

/-- `cor:cs-equality`, necessity: if `A B = C²` then `w_j w_i |u_j v_i − v_j u_i|² = 0` for `i < j < M`. -/
theorem cs_equality {M x i j : PTm n}
    (h : Γ ⊢[PRAAx] ap2 (sumF (Ab w u)) M x * ap2 (sumF (Bb w v)) M x ≐
      ap2 (sumF (Cb w u v)) M x * ap2 (sumF (Cb w u v)) M x)
    (hj : Γ ⊢[PRAAx] lt j M) (hi : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] inst2 w j x * (inst2 w i x * (ad (inst2 u j x * inst2 v i x) (inst2 v j x * inst2 u i x) *
      ad (inst2 u j x * inst2 v i x) (inst2 v j x * inst2 u i x))) ≐ zero := by
  have h' := natEq h
  have d0 : Γ ⊢[PRAAx] ap2 (sumF (DB w u v)) M x ≐ zero := by
    ipra_lc h' - natEq (lagrange (Γ := Γ) w u v M x)
  have r := sum_zero_elim (DB w u v) d0 hj
  rw [inst2_DB] at r
  refine .orE (zero_or_zero_of_mul r) (zml Prf.hyp0 _) ?_
  have t := (eB_at (Γ := (ap2 (sumF (eB w u v)) j (pairT (pairT (inst2 u j x) (inst2 v j x)) x) ≐ zero) :: Γ)
    w u v i (inst2 u j x) (inst2 v j x) x).eqSymm.eqTrans (sum_zero_elim (eB w u v) Prf.hyp0 hi.wk)
  exact (congrMul (.eqRefl _) t).eqTrans (mul_zero _)

/-- `cor:cs-equality`, sufficiency: if every row `w_j ∑_{i<j} w_i |u_j v_i − v_j u_i|²` vanishes,
then `A B = C²`. -/
theorem cs_equality_rev {M x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ (inst2 (DB w u v) (var 0) (Syn.shift x) ≐ zero))) :
    Γ ⊢[PRAAx] ap2 (sumF (Ab w u)) M x * ap2 (sumF (Bb w v)) M x ≐
      ap2 (sumF (Cb w u v)) M x * ap2 (sumF (Cb w u v)) M x :=
  (lagrange w u v M x).eqTrans ((congrAdd (.eqRefl _) (sum_zero_of_bounded _ _ _ h)).eqTrans (add_zero _))

end Lagrange

end LeanProofs.IPRA.Probability.WeightedLagrange
