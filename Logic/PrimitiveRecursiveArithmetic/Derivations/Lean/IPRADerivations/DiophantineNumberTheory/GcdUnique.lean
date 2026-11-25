import IPRADerivations.DiophantineNumberTheory.GcdNormalize
import IPRADerivations.DiophantineNumberTheory.ProjectiveVectorUnique
import IPRADerivations.Core.LinearCombination

/-!
# Uniqueness of gcd-primitive representatives in every dimension

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemma `lem:normalize`: "Two such representatives
of the same rational projective point are equal", for natural vectors of any length whose gcd
(`GcdList.gv`) is `1`, without Bézout certificates.

For each index `j`, with `v_i w_j = v_j w_i` for all `i < N`:
* if `v_j = 0` and `w_j ≥ 1`, then every `v_i = 0`, so `gcd(v) = 0`;
* if `v_j ≥ 1` and `w_j = 0`, then every `w_i = 0`, so `gcd(w) = 0`;
* if both are positive, with `h = gcd(v_j, w_j)`, `v_j = h a`, `w_j = h b`, `gcd(a, b) = 1`: `a w_i = b v_i`, so `a`
  divides every `v_i` (`Coprime.gauss`), hence `gcd(v) = 1`, so `a = 1`; symmetrically `b = 1`.

* `index_eq`: the per-index argument; `vector_unique_gcd`: `v = w`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.GcdUnique

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gv gv_greatest)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize (gv_all_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.ProjectiveVectorUnique (propJ propAll propJ_symm shift_mul2)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' dvd_of_eq' gauss coprime_quotients
  eq_one_of_dvd_one gcd_comm_one pos_of_eq_mul gcd_dvd')
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem sh {a b : PTm k} (h : Γ ⊢[PRAAx] a ≐ b) : Γ.map Fm.shift ⊢[PRAAx] Syn.shift a ≐ Syn.shift b := h.shift

theorem sh_inst {V : PTm 2} {j x : PTm k} : Syn.shift (inst2 V j x) = inst2 V (Syn.shift j) (Syn.shift x) :=
  subst_inst2 _ _ _ _

theorem shift_succ' (t : PTm k) : Syn.shift (succ t) = succ (Syn.shift t) := by simp [Syn.shift]
theorem shift_pred' (t : PTm k) : Syn.shift (pred t) = pred (Syn.shift t) := by simp [Syn.shift]
theorem shift_gcd' (a b : PTm k) : Syn.shift (gcd a b) = gcd (Syn.shift a) (Syn.shift b) := by
  unfold Syn.shift; rw [subst_ex2, ConciseIPRA.PTm.subst_succ]
theorem shift_one' : Syn.shift (one : PTm k) = one := by simp [Syn.shift]
theorem shift_zero' : Syn.shift (zero : PTm k) = zero := by simp [Syn.shift]

theorem sh_pos {V : PTm 2} {j x : PTm k} (h : Γ ⊢[PRAAx] inst2 V j x ≐ succ (pred (inst2 V j x))) :
    Γ.map Fm.shift ⊢[PRAAx] inst2 V (Syn.shift j) (Syn.shift x) ≐ succ (pred (inst2 V (Syn.shift j) (Syn.shift x))) := by
  have e := sh h
  rw [shift_succ', shift_pred', sh_inst] at e
  exact e

/-- If `w_j ≥ 1` and `v_j = 0`, every `v_i` vanishes. -/
theorem all_zero_of {V W : PTm 2} {j N x : PTm k} (hp : Γ ⊢[PRAAx] propJ V W j N x)
    (hv0 : Γ ⊢[PRAAx] inst2 V j x ≐ zero) (hw : Γ ⊢[PRAAx] inst2 W j x ≐ succ (pred (inst2 W j x))) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 V (var 0) (Syn.shift x) ≐ zero) := by
  refine .allI (.impI ?_)
  have e := natEq (Prf.impE hp.allOpen.wk Prf.hyp0)
  have z : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] inst2 V (Syn.shift j) (Syn.shift x) ≐ zero := by
    have e := sh hv0; rw [sh_inst, shift_zero'] at e; exact e.wk
  have hw' := (sh_pos hw).wk (ψ := lt (var 0) (Syn.shift N))
  have z' := natEq z
  refine mul_cancel hw' ?_
  ipra_lc -e + 𝔞 (inst2 W (var 0) (Syn.shift x)) * z'

/-- The per-index argument: `w_j = v_j`. -/
theorem index_eq {V W : PTm 2} {j N x : PTm k} (hp : Γ ⊢[PRAAx] propJ V W j N x)
    (hv1 : Γ ⊢[PRAAx] gv V N x ≐ one) (hw1 : Γ ⊢[PRAAx] gv W N x ≐ one) :
    Γ ⊢[PRAAx] inst2 W j x ≐ inst2 V j x := by
  refine .orE (zero_or_succ (inst2 V j x)) ?_ ?_
  · -- `v_j = 0`
    let Δ := (inst2 V j x ≐ zero) :: Γ
    have hv0 : Δ ⊢[PRAAx] inst2 V j x ≐ zero := Prf.hyp0
    refine .orE (zero_or_succ (inst2 W j x)) (Prf.hyp0.eqTrans hv0.wk.eqSymm) ?_
    have hw : ((inst2 W j x ≐ succ (pred (inst2 W j x))) :: Δ) ⊢[PRAAx] inst2 W j x ≐ succ (pred (inst2 W j x)) :=
      Prf.hyp0
    have hz := gv_all_zero V (all_zero_of hp.wk.wk hv0.wk hw)
    exact succ_ne_zero' _ ((hv1.wk.wk.eqSymm.eqTrans hz))
  · let Δ := (inst2 V j x ≐ succ (pred (inst2 V j x))) :: Γ
    have hv : Δ ⊢[PRAAx] inst2 V j x ≐ succ (pred (inst2 V j x)) := Prf.hyp0
    refine .orE (zero_or_succ (inst2 W j x)) ?_ ?_
    · -- `w_j = 0` forces `w = 0`
      have hw0 : ((inst2 W j x ≐ zero) :: Δ) ⊢[PRAAx] inst2 W j x ≐ zero := Prf.hyp0
      have hz := gv_all_zero W (all_zero_of (propJ_symm hp.wk.wk) hw0 hv.wk)
      exact succ_ne_zero' _ ((hw1.wk.wk.eqSymm.eqTrans hz))
    · let E := (inst2 W j x ≐ succ (pred (inst2 W j x))) :: Δ
      have hw : E ⊢[PRAAx] inst2 W j x ≐ succ (pred (inst2 W j x)) := Prf.hyp0
      have hv' : E ⊢[PRAAx] inst2 V j x ≐ succ (pred (inst2 V j x)) := hv.wk
      have hh := gcd_pos (B := inst2 W j x) hv'
      have hd := gcd_dvd' (b := inst2 W j x) hv'
      have eA := eq_of_dvd' hh (Prf.andE₁ hd)
      have eB := eq_of_dvd' hh (Prf.andE₂ hd)
      have pa := pos_of_eq_mul hv' eA
      have pb := pos_of_eq_mul hw eB
      have cab := coprime_quotients (c := inst2 W j x) hv'
      have cba := gcd_comm_one pb cab
      -- the quotients divide every entry
      have dv (A B : PTm k) (U U' : PTm 2) (hA : E ⊢[PRAAx] A ≐ succ (pred A)) (hAB : E ⊢[PRAAx] gcd A B ≐ one)
          (hc : E ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
            Syn.shift A * inst2 U' (var 0) (Syn.shift x) ≐ Syn.shift B * inst2 U (var 0) (Syn.shift x))) :
          E ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ dvd (succ (Syn.shift (pred A))) (inst2 U (var 0) (Syn.shift x))) := by
        refine .allI (.impI ?_)
        have c := Prf.impE hc.allOpen.wk Prf.hyp0
        have hA' : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] Syn.shift A ≐ succ (Syn.shift (pred A)) := by
          have e := sh hA; rw [shift_succ'] at e; exact e.wk
        have hAB' : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] gcd (Syn.shift A) (Syn.shift B) ≐ one := by
          have e := sh hAB; rw [shift_gcd', shift_one'] at e; exact e.wk
        have hApos : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] Syn.shift A ≐ succ (pred (Syn.shift A)) := by
          have e := sh hA; rw [shift_succ', shift_pred'] at e; exact e.wk
        have g := gauss hApos hAB' (dvd_of_eq' hApos (w := inst2 U' (var 0) (Syn.shift x)) c.eqSymm)
        exact dvd_congr_left hA' g
      -- `a w_i = b v_i` and `b v_i = a w_i`
      have cross : E ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
          Syn.shift (quo (inst2 V j x) (gcd (inst2 V j x) (inst2 W j x))) * inst2 W (var 0) (Syn.shift x) ≐
            Syn.shift (quo (inst2 W j x) (gcd (inst2 V j x) (inst2 W j x))) * inst2 V (var 0) (Syn.shift x)) := by
        refine .allI (.impI ?_)
        have e := natEq (Prf.impE (hp.wk.wk : E ⊢[PRAAx] _).allOpen.wk Prf.hyp0)
        have a1 := sh eA; have b1 := sh eB
        rw [shift_mul2, sh_inst] at a1 b1
        have hh' : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx]
            Syn.shift (gcd (inst2 V j x) (inst2 W j x)) ≐ succ (pred (Syn.shift (gcd (inst2 V j x) (inst2 W j x)))) := by
          have e := sh hh; rw [shift_succ', shift_pred'] at e; exact e.wk
        refine mul_cancel hh' ?_
        ipra_lc e -
          𝔞 (inst2 W (var 0) (Syn.shift x)) * natEq (a1.wk : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] _) +
          𝔞 (inst2 V (var 0) (Syn.shift x)) * natEq (b1.wk : (lt (var 0) (Syn.shift N) :: E.map Fm.shift) ⊢[PRAAx] _)
      have cross' : E ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
          Syn.shift (quo (inst2 W j x) (gcd (inst2 V j x) (inst2 W j x))) * inst2 V (var 0) (Syn.shift x) ≐
            Syn.shift (quo (inst2 V j x) (gcd (inst2 V j x) (inst2 W j x))) * inst2 W (var 0) (Syn.shift x)) :=
        .allI (.impI (Prf.impE cross.allOpen.wk Prf.hyp0).eqSymm)
      have da := gv_greatest V (dv _ _ V W pa cab cross)
      have db := gv_greatest W (dv _ _ W V pb cba cross')
      have a1 := eq_one_of_dvd_one pa (dvd_congr_left pa.eqSymm (dvd_congr (hv1.wk.wk : E ⊢[PRAAx] _) da))
      have b1 := eq_one_of_dvd_one pb (dvd_congr_left pb.eqSymm (dvd_congr (hw1.wk.wk : E ⊢[PRAAx] _) db))
      ipra_lc natEq eB - natEq eA + 𝔞 (gcd (inst2 V j x) (inst2 W j x)) * (natEq b1 - natEq a1)

/-- `lem:normalize`, uniqueness: two natural vectors with gcd `1` on the same projective point are equal. -/
theorem vector_unique_gcd {V W : PTm 2} {N x : PTm k} (hp : Γ ⊢[PRAAx] propAll V W N x)
    (hv1 : Γ ⊢[PRAAx] gv V N x ≐ one) (hw1 : Γ ⊢[PRAAx] gv W N x ≐ one) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 W (var 0) (Syn.shift x) ≐ inst2 V (var 0) (Syn.shift x)) := by
  have hv1s : Γ.map Fm.shift ⊢[PRAAx] gv V (Syn.shift N) (Syn.shift x) ≐ one := by
    have e := hv1.shift; simpa [Fm.shift, Syn.shift] using e
  have hw1s : Γ.map Fm.shift ⊢[PRAAx] gv W (Syn.shift N) (Syn.shift x) ≐ one := by
    have e := hw1.shift; simpa [Fm.shift, Syn.shift] using e
  exact .allI (.impI (index_eq (Prf.impE hp.allOpen.wk Prf.hyp0) hv1s.wk hw1s.wk))

end LeanProofs.IPRA.DiophantineNumberTheory.GcdUnique
