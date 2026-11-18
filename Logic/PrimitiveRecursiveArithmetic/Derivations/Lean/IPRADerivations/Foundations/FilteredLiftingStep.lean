import IPRADerivations.Foundations.NullVectorDeterminant

/-!
# The step identities of filtered lifting (`ipra_coherent_methods_2026-11-15`, `thm:filtered-lifting`, `cor:modular-hensel`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, theorem `thm:filtered-lifting`: with
`b_{r+1} = b_r − U P(b_r)` (L), "put `x = b_r`, `v = P(x)`, and `h = −U v` ... Lemma
`lem:filtered-taylor` gives `P(x + h) = (I − J(a) U) v − (J(x) − J(a)) U v + R`, `R ∈ (F^{2k} B)^m`
(1). The first term belongs to `F^{k+1}` by (H). The second belongs to `F^{k+1}` because
`J(x) − J(a) ∈ F^1`. ... Thus one iteration raises the certified residual precision by at least
one level." Uniqueness: "`0 = P(x) − P(y) = J(y) d + R` ... Multiplying by `U` and rearranging
gives `d = (I − U J(a)) d − U (J(y) − J(a)) d − U R` (2)." And corollary `cor:modular-hensel`
(`B = ℤ/q^N`, `F^k = q^k B`), with the example `q = 4`, `P(X) = X³ − X − 2`, `a = 2`, `U = 3`,
`N = 3`: "Modulo `64` the two updates are `2 ↦ 54 ↦ 22`. Directly,
`22³ − 22 − 2 = 10624 = 166 · 64`."

Derived for integer terms:

* `lift_step_ring`, `unique_step_ring`, `lift_step`, `unique_step`: the identities (1) and (2)
  for systems of every size `m` (vectors and matrices of `Core/LinearAlgebra`), from the Taylor
  identity `P(x − U v) + J(x) U v = v + R`, respectively `J(y) d + R = 0`, as hypotheses;
* `hensel_gain_ring`, `hensel_gain`: the precision gain of `cor:modular-hensel` for one
  equation, with an explicit witness. If `P(x − U v) + J(x) U v = v + (U v)² T`,
  `1 − J(a) U = q e`, `J(x) − J(a) = q g` and `v = q^k ω` with `q^k = q · q^{k−1}`, then
  `P(x − U v) = q^{k+1} (e ω − g U ω + U² q^{k−1} ω² T)`;
* `hensel_unique_ring`, `hensel_unique`: the uniqueness step. If
  `J(y) d + d² T = q^N s`, `1 − U J(a) = q e`, `J(y) − J(a) = q g`, `d = q^k ω` and
  `q^N = q^{k+1} q_r`, then `d = q^{k+1} (e ω − U g ω − U q^{k−1} ω² T + U q_r s)`;
* `example_first`, `example_second`, `example_root`: the three numerical facts of the example,
  `2 − 3 · P(2) = 54 − 64`, `54 − 3 · P(54) = 22 − 64 · 7378`, `P(22) = 166 · 64`.

No primality of `q` is used. Not derived: the Taylor identity `lem:filtered-taylor` for a coded
polynomial system, the iteration (L) as a primitive recursive sequence with the invariant (I)
by quantifier-free induction on `r`, and the compatibility under reduction.
-/

namespace LeanProofs.IPRA.Foundations.FilteredLiftingStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R] {m : ℕ}

/-- (1): `P(x + h) = (I − J(a) U) v − (J(x) − J(a)) U v + R` for `h = −U v`. -/
theorem lift_step_ring (Ja Jx U : Matrix (Fin m) (Fin m) R) (v w r : Fin m → R)
    (hT : w + Jx *ᵥ (U *ᵥ v) = v + r) :
    w = (1 - Ja * U) *ᵥ v - ((Jx - Ja) * U) *ᵥ v + r := by
  have h' : w = v + r - Jx *ᵥ (U *ᵥ v) := eq_sub_of_add_eq hT
  rw [h']
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mul, ← Matrix.mulVec_mulVec]
  abel

/-- (2): `d = (I − U J(a)) d − U (J(y) − J(a)) d − U R` when `J(y) d + R = 0`. -/
theorem unique_step_ring (Ja Jy U : Matrix (Fin m) (Fin m) R) (d r : Fin m → R)
    (h : Jy *ᵥ d + r = 0) :
    d = (1 - U * Ja) *ᵥ d - (U * (Jy - Ja)) *ᵥ d - U *ᵥ r := by
  have h2 : U *ᵥ (Jy *ᵥ d) + U *ᵥ r = 0 := by
    rw [← Matrix.mulVec_add, h, Matrix.mulVec_zero]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mul_sub, ← Matrix.mulVec_mulVec]
  rw [eq_neg_of_add_eq_zero_right h2]
  abel

/-- The precision gain for one equation, with its witness. -/
theorem hensel_gain_ring {q qk qk1 e g U T v w ω Ja Jx : R}
    (hT : w + Jx * (U * v) = v + U * v * (U * v) * T) (hH : 1 - Ja * U = q * e)
    (hJ : Jx - Ja = q * g) (hv : v = qk * ω) (hq : qk = q * qk1) :
    w = q * qk * (e * ω - g * U * ω + U * U * qk1 * ω * ω * T) := by
  linear_combination hT + v * hH - U * v * hJ +
    (q * e - q * g * U + U * U * T * (v + qk * ω)) * hv + U * U * T * qk * ω * ω * hq

/-- The uniqueness step for one equation, with its witness. -/
theorem hensel_unique_ring {q qk qk1 qr qN e g U T d s ω Ja Jy : R}
    (hT : Jy * d + d * d * T = qN * s) (hH : 1 - U * Ja = q * e) (hJ : Jy - Ja = q * g)
    (hd : d = qk * ω) (hq : qk = q * qk1) (hN : qN = q * qk * qr) :
    d = q * qk * (e * ω - U * g * ω - U * qk1 * ω * ω * T + U * qr * s) := by
  linear_combination d * hH + U * hT - U * d * hJ +
    (q * e - U * q * g - U * T * (d + qk * ω)) * hd - U * T * qk * ω * ω * hq + U * s * hN

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {m : ℕ}

/-- `thm:filtered-lifting`, identity (1), for a system of any size. -/
theorem lift_step {Ja Jx U : Mat m n} {v w r : Vec m n}
    (hT : Γ ⊢[PRAAx] Vec.eqFm (Vec.add w (Mat.mulVec Jx (Mat.mulVec U v))) (Vec.add v r)) :
    Γ ⊢[PRAAx] Vec.eqFm w
      (Vec.add (Vec.sub (Mat.mulVec (Mat.sub Mat.one (Mat.mul Ja U)) v)
        (Mat.mulVec (Mat.mul (Mat.sub Jx Ja) U) v)) r) := by
  have e := Vec.toZ_eq hT
  simp only [Vec.toZ_add, Mat.toZ_mulVec] at e
  refine Vec.derive ?_
  simp only [Vec.toZ_add, Vec.toZ_sub, Mat.toZ_mulVec, Mat.toZ_mul, Mat.toZ_sub, Mat.toZ_one]
  exact lift_step_ring _ _ _ _ _ _ e

/-- `thm:filtered-lifting`, identity (2), for a system of any size. -/
theorem unique_step {Ja Jy U : Mat m n} {d r : Vec m n}
    (h : Γ ⊢[PRAAx] Vec.eqFm (Vec.add (Mat.mulVec Jy d) r) (fun _ => ZT.natLit 0)) :
    Γ ⊢[PRAAx] Vec.eqFm d
      (Vec.sub (Vec.sub (Mat.mulVec (Mat.sub Mat.one (Mat.mul U Ja)) d)
        (Mat.mulVec (Mat.mul U (Mat.sub Jy Ja)) d)) (Mat.mulVec U r)) := by
  have e := Vec.toZ_eq h
  have z : Vec.toZ Γ (fun _ : Fin m => (ZT.natLit 0 : ZT n)) = 0 := by
    funext i
    simp [Vec.toZ]
  rw [z] at e
  simp only [Vec.toZ_add, Mat.toZ_mulVec] at e
  refine Vec.derive ?_
  simp only [Vec.toZ_sub, Mat.toZ_mulVec, Mat.toZ_mul, Mat.toZ_sub, Mat.toZ_one]
  exact unique_step_ring _ _ _ _ _ e

variable {q qk qk1 qr qN e g U T v w ω Ja Jx Jy d s : ZT n}

/-- `cor:modular-hensel`, one update: the residual gains a factor `q`, with its witness. -/
theorem hensel_gain
    (hT : Γ ⊢[PRAAx] ZT.eq (w + Jx * (U * v)) (v + U * v * (U * v) * T))
    (hH : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 - Ja * U) (q * e))
    (hJ : Γ ⊢[PRAAx] ZT.eq (Jx - Ja) (q * g))
    (hv : Γ ⊢[PRAAx] ZT.eq v (qk * ω)) (hq : Γ ⊢[PRAAx] ZT.eq qk (q * qk1)) :
    Γ ⊢[PRAAx] ZT.eq w (q * qk * (e * ω - g * U * ω + U * U * qk1 * ω * ω * T)) := by
  have eT := ZT.toZ_eq hT
  have eH := ZT.toZ_eq hH
  have eJ := ZT.toZ_eq hJ
  have ev := ZT.toZ_eq hv
  have eq := ZT.toZ_eq hq
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
    at eT eH eJ ev eq ⊢
  exact hensel_gain_ring eT eH eJ ev eq

/-- `cor:modular-hensel`, uniqueness: the difference of two roots in the residue class gains a
factor `q`, with its witness. -/
theorem hensel_unique
    (hT : Γ ⊢[PRAAx] ZT.eq (Jy * d + d * d * T) (qN * s))
    (hH : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 - U * Ja) (q * e))
    (hJ : Γ ⊢[PRAAx] ZT.eq (Jy - Ja) (q * g))
    (hd : Γ ⊢[PRAAx] ZT.eq d (qk * ω)) (hq : Γ ⊢[PRAAx] ZT.eq qk (q * qk1))
    (hN : Γ ⊢[PRAAx] ZT.eq qN (q * qk * qr)) :
    Γ ⊢[PRAAx] ZT.eq d (q * qk * (e * ω - U * g * ω - U * qk1 * ω * ω * T + U * qr * s)) := by
  have eT := ZT.toZ_eq hT
  have eH := ZT.toZ_eq hH
  have eJ := ZT.toZ_eq hJ
  have ed := ZT.toZ_eq hd
  have eq := ZT.toZ_eq hq
  have eN := ZT.toZ_eq hN
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
    at eT eH eJ ed eq eN ⊢
  exact hensel_unique_ring eT eH eJ ed eq eN

/-! ## The example `q = 4`, `P(X) = X³ − X − 2`, `a = 2`, `U = 3`, `N = 3` -/

/-- `P(X) = X³ − X − 2` on an integer term. -/
def cubic (x : ZT 0) : ZT 0 := x * x * x - x - ZT.natLit 2

/-- The first update: `2 − 3 · P(2) = 54 − 64`. -/
theorem example_first : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    ZT.eq (ZT.natLit 2 - ZT.natLit 3 * cubic (ZT.natLit 2)) (ZT.natLit 54 - ZT.natLit 64) :=
  ZT.derive (by
    simp only [cubic, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
    norm_num)

/-- The second update: `54 − 3 · P(54) = 22 − 64 · 7378`. -/
theorem example_second : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    ZT.eq (ZT.natLit 54 - ZT.natLit 3 * cubic (ZT.natLit 54))
      (ZT.natLit 22 - ZT.natLit 64 * ZT.natLit 7378) :=
  ZT.derive (by
    simp only [cubic, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
    norm_num)

/-- "Directly, `22³ − 22 − 2 = 10624 = 166 · 64`." -/
theorem example_root : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    ZT.eq (cubic (ZT.natLit 22)) (ZT.natLit 166 * ZT.natLit 64) :=
  ZT.derive (by
    simp only [cubic, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
    norm_num)

end LeanProofs.IPRA.Foundations.FilteredLiftingStep
