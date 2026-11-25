import IPRADerivations.Topology.DimensionSchema
import IPRADerivations.Core.CertificateTactics

/-!
# The identity presentation (`dimension_invariance_ipra`, `cor:dimension`, the converse)

Packet: `topology/dimension_invariance_ipra`, `cor:dimension`: "When `n = m`, the identity has
exact rational evaluations, modulus `μ(k) = k`, and an immediate inverse modulus; it gives the
constructive converse." And: "If one dimension is zero, the positive-dimensional direction already
excludes a map with the stated inverse data into a singleton."

With the coding of `Topology/DimensionSchema` (points of `C_D` as lists of numerators over a common
denominator), the identity of `C_D` is the presentation `A_j(x, p) = x_j / den x`, that is
`P_j = x_j`, `Q_j = 0`, `R_j = den x − 1` (`idP`, `idQ`, `idR`), with `μ(k) = k` (`idMu`):

* `identity_U`: iPRA proves `eq:U` for it;
* `identity_I`: iPRA proves `eq:I` for it at the scale `a = 1`
  (`dist + 2^{1−p} < 1/2` gives `‖q − q'‖ ≤ 1/2`);
* `dimension_zero`: for `D ≥ 1` and the target `ℝ^0`, `eq:U ∧ eq:I` is refuted (the schema with
  `m = 0`).

With `DimensionSchema.dimension_invariance` this is `cor:dimension` in the arithmetic reading:
presentations in both directions exist for `n = m` (the identity), and for positive `n ≠ m` they are
refuted. The real-variable reading (homeomorphisms of `ℝ^n` given by such presentations) is not
formalized.
-/

namespace LeanProofs.IPRA.Topology.DimensionIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.TermSums
open LeanProofs.IPRA.Foundations.RationalFloors
open LeanProofs.IPRA.Topology.StaggeredCells (dist)
open LeanProofs.IPRA.Topology.DimensionOccupancy (fsum_zero_elim)
open LeanProofs.IPRA.Topology.DimensionObstruction (congrDist)
open LeanProofs.IPRA.Topology.DimensionSchema

set_option autoImplicit false

variable {n : ℕ}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Arithmetic -/

section Arith

variable {Γ : List (Fm PTm n)}

/-- `2^k G ≤ RR` gives `2^{k+p} G ≤ (2^p + 2^{k+1}) RR`. -/
theorem idU_arith {G RR K Pp Pk1 Pkp : PTm n} (h : Γ ⊢[PRAAx] le (K * G) RR) (hkp : Γ ⊢[PRAAx] Pkp ≐ K * Pp) :
    Γ ⊢[PRAAx] le (Pkp * G) ((Pp + Pk1) * RR) := by
  refine le_of_eq_add (d := Pp * monus RR (K * G) + Pk1 * RR) ?_
  ipra_lc 𝔞 Pp * natEq (eq_add_of_le h) - 𝔞 G * natEq hkp

/-- `2^{1+p} G + 4 RR < 2^p RR` gives `2 G ≤ RR`. -/
theorem idI_arith {G RR Pp P1p P2 : PTm n} (h : Γ ⊢[PRAAx] lt (P1p * G + P2 * RR) (Pp * RR))
    (h1p : Γ ⊢[PRAAx] P1p ≐ two * Pp) (h2 : Γ ⊢[PRAAx] P2 ≐ two * two) : Γ ⊢[PRAAx] le (two * G) RR := by
  refine .orE (lt_or_le RR (two * G)) ?_ Prf.hyp0
  let Δ : List (Fm PTm n) := lt RR (two * G) :: Γ
  refine .botE _ (succ_ne_zero (a := Pp + Pp * monus (two * G) (succ RR) + two * two * RR +
    monus (Pp * RR) (succ (P1p * G + P2 * RR))) ?_)
  ipra_lc -natEq (eq_add_of_le (Γ := Δ) h.wk) - 𝔞 G * natEq (Γ := Δ) h1p.wk -
    𝔞 Pp * natEq (eq_add_of_le (Γ := Δ) Prf.hyp0) - 𝔞 RR * natEq (Γ := Δ) h2.wk

end Arith

/-! ## The identity presentation -/

section Identity

variable (d' : ℕ)

def idP (j : Fin (d' + 1)) : PTm 2 := proj j.val (Syn.var 0)
def idQ (_j : Fin (d' + 1)) : PTm 2 := zero
def idR (_j : Fin (d' + 1)) : PTm 2 := pred (den d' (Syn.var 0))
def idMu : PTm 1 := Syn.var 0

variable {Γ : List (Fm PTm n)}

theorem oP_id (j : Fin (d' + 1)) (x p : PTm n) : oP (d' + 1) (idP d') j x p = proj j.val x := by
  simp [oP, idP]
theorem oQ_id (j : Fin (d' + 1)) (x p : PTm n) : oQ (d' + 1) (idQ d') j x p = zero := by
  simp [oQ, idQ]
theorem oR_id (j : Fin (d' + 1)) (x p : PTm n) : oR (d' + 1) (idR d') j x p = pred (den d' x) := by
  simp [oR, idR]

theorem pos_den {x : PTm n} (hx : Γ ⊢[PRAAx] valid d' x) : Γ ⊢[PRAAx] den d' x ≐ succ (pred (den d' x)) := by
  refine .orE (zero_or_succ (den d' x)) ?_ Prf.hyp0
  refine .botE _ (succ_ne_zero (a := zero) ?_)
  exact (monus_zero _).eqSymm.eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqSymm.eqTrans (Prf.andE₁ hx).wk)

theorem gap_id (j : Fin (d' + 1)) {x x' : PTm n} (p : PTm n) (hx : Γ ⊢[PRAAx] valid d' x)
    (hx' : Γ ⊢[PRAAx] valid d' x') :
    Γ ⊢[PRAAx] oGap (d' + 1) (idP d') (idQ d') (idR d') j x x' p ≐
      dist (proj j.val x * den d' x') (proj j.val x' * den d' x) := by
  have ex := natEq (pos_den d' hx)
  have ex' := natEq (pos_den d' hx')
  simp only [oGap, oP_id, oQ_id, oR_id]
  refine congrDist ?_ ?_
  · ipra_lc [crossX] -(𝔞 (proj j.val x)) * ex'
  · ipra_lc [crossY] -(𝔞 (proj j.val x')) * ex

theorem den_id (j : Fin (d' + 1)) {x x' : PTm n} (p : PTm n) (hx : Γ ⊢[PRAAx] valid d' x)
    (hx' : Γ ⊢[PRAAx] valid d' x') :
    Γ ⊢[PRAAx] oDen (d' + 1) (idR d') j x x' p ≐ den d' x * den d' x' := by
  simp only [oDen, oR_id]
  exact congrMul (pos_den d' hx).eqSymm (pos_den d' hx').eqSymm

theorem U_body {x x' k p : PTm n} (hx : Γ ⊢[PRAAx] valid d' x) (hx' : Γ ⊢[PRAAx] valid d' x')
    (hs : Γ ⊢[PRAAx] srcSum d' x x' k ≐ zero) :
    Γ ⊢[PRAAx] outU (d' + 1) (idP d') (idQ d') (idR d') x x' k p ≐ zero := by
  refine fsum_eq_zero (fun j => ?_)
  have hj : Γ ⊢[PRAAx] le (pw two k * dist (proj j.val x * den d' x') (proj j.val x' * den d' x))
      (den d' x * den d' x') := fsum_zero_elim (d' + 1) _ hs j
  have r := idU_arith (Pk1 := pw two (succ k)) hj (pw_add two k p)
  exact le_congr (congrMul (.eqRefl _) (gap_id d' j p hx hx').eqSymm)
    (congrMul (.eqRefl _) (den_id d' j p hx hx').eqSymm) r

theorem I_body {x x' p a : PTm n} (ha : Γ ⊢[PRAAx] a ≐ one) (hx : Γ ⊢[PRAAx] valid d' x)
    (hx' : Γ ⊢[PRAAx] valid d' x') (ho : Γ ⊢[PRAAx] outI (d' + 1) (idP d') (idQ d') (idR d') x x' p a ≐ zero) :
    Γ ⊢[PRAAx] srcSum d' x x' one ≐ zero := by
  refine fsum_eq_zero (fun j => ?_)
  have hj : Γ ⊢[PRAAx] lt (pw two (a + p) * oGap (d' + 1) (idP d') (idQ d') (idR d') j x x' p +
      pw two (succ a) * oDen (d' + 1) (idR d') j x x' p) (pw two p * oDen (d' + 1) (idR d') j x x' p) :=
    fsum_zero_elim (d' + 1) _ ho j
  have hj' := lt_congr (congrAdd (congrMul (.eqRefl _) (gap_id d' j p hx hx')) (congrMul (.eqRefl _) (den_id d' j p hx hx')))
    (congrMul (.eqRefl _) (den_id d' j p hx hx')) hj
  have h1p : Γ ⊢[PRAAx] pw two (a + p) ≐ two * pw two p :=
    (congrAp2 powF (congrAdd ha (.eqRefl _)) (.eqRefl _)).eqTrans ((pw_add two one p).eqTrans
      (congrMul (pw_one two) (.eqRefl _)))
  have h2 : Γ ⊢[PRAAx] pw two (succ a) ≐ two * two :=
    (congrAp2 powF (congrSucc ha) (.eqRefl _)).eqTrans ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _)))
  exact le_congr (congrMul (pw_one two).eqSymm (.eqRefl _)) (.eqRefl _) (idI_arith hj' h1p h2)

/-- `eq:U` for the identity of `C_D` with `μ(k) = k`. -/
theorem identity_U : Γ ⊢[PRAAx] Uhyp d' (d' + 1) (idP d') (idQ d') (idR d') idMu := by
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI ?_))))))
  exact U_body d' hyp2 Prf.hyp1 Prf.hyp0

/-- `eq:I` for the identity of `C_D` at the scale `a = 1`. -/
theorem identity_I : ([] : List (Fm PTm 0)) ⊢[PRAAx] Ihyp d' (d' + 1) (idP d') (idQ d') (idR d') one := by
  refine .allI (.allI (.allI (.impI (.impI (.impI ?_)))))
  have e : Syn.shift (Syn.shift (Syn.shift (one : PTm 0))) = (one : PTm 3) := by simp [Syn.shift]
  exact I_body d' (by rw [e]; exact .eqRefl _) hyp2 Prf.hyp1 Prf.hyp0

end Identity

/-- Dimension zero: for `D ≥ 1` a presentation of a map `C_D → ℝ^0` with `eq:U` and `eq:I` is
refuted (`DimensionSchema.dimension_schema` with `m = 0`). -/
theorem dimension_zero (d' : ℕ) (AP AQ AR : Fin 0 → PTm 2) (μ : PTm 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (schemaFormula d' 0 AP AQ AR μ) :=
  dimension_schema d' 0 AP AQ AR μ (by omega)

end LeanProofs.IPRA.Topology.DimensionIdentity
