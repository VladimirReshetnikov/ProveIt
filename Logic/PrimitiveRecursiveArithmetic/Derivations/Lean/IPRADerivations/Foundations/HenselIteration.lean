import IPRADerivations.Foundations.FilteredTaylor

/-!
# The precision invariant of filtered lifting for one polynomial equation over `ℤ`

Packet: `foundations/ipra_coherent_methods_2026-11-15`, `paper/sections/04_lifting.tex`, Theorem
`thm:filtered-lifting` ("Finite filtered lifting") with `cor:modular-hensel` (`F^k = q^k`): from
`P(a) ∈ F^1`, `I − J(a) U ∈ F^1` (H), the sequence `b_0 = a`, `b_{r+1} = b_r − U P(b_r)` (L) satisfies, for
every `r`, `b_r − a ∈ F^1` and `P(b_r) ∈ F^{r+1}` (I). "No derivative inverse is recomputed during the
iteration, and no division occurs after the data `a, U` are supplied."

Here for one equation `P : PE 1` (a polynomial expression of `Analysis/PolynomialRemainder`) over the
integers with `F^k = q^k ℤ`; membership is an exact equation with an explicit witness.

* `step_eqs` (one step of (I)): from `1 − J(a) U = q e`, `b − a = q σ` and `P(b) = q^{K'+1} ω`,
  `b' = b − U P(b)` satisfies `b' − a = q (σ − U q^{K'} ω)` and
  `P(b') = q^{K'+2} (ω e − σ ℓ U ω + U² q^{K'} ω² τ)`, with `ℓ` the difference witness of `J(b) − J(a)`
  (`FilteredTaylor.diff_exact` at `∂P`) and `τ` the Taylor witness (`FilteredTaylor.taylor_exact`); the
  certificate (a `linear_combination` of eight equations) was computed by polynomial reduction;
* `seq`, `sig`, `om`: the iterates `b_r` of (L) and the witnesses, by recursion on `r`;
* `invariant` ((I), first two assertions): for every `r`, `b_r − a = q σ_r` and `P(b_r) = q^{r+1} ω_r`;
  at `r = N − 1`, `b_{N−1}` is a root of `P` modulo `q^N`.

The iteration is uniform in the metalevel `r` (each `b_r` is an explicit integer term). Uniqueness and the
system case (matrices) are `Foundations/FilteredLiftingStep`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.HenselIteration

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder (PE ev dv)
open LeanProofs.IPRA.Foundations.FilteredTaylor (pd tq ls taylor_exact diff_exact dv_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- The constant point `(b)`. -/
abbrev pt (b : ZT k) : Fin 1 → ZT k := fun _ => b

variable (P : PE 1) (U : ZT k)

/-- One step of (L): `b ↦ b − U P(b)`. -/
def stepZ (b : ZT k) : ZT k := b + -(U * ev P (pt b))

/-- `J(b) = P'(b)`. -/
abbrev jac (b : ZT k) : ZT k := ev (pd P 0) (pt b)

variable {P U}

/-- One step of the invariant (I). -/
theorem step_eqs {a b σ ω eW : ZT k} {q K' : PTm k}
    (hJ : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 + -(jac P a * U)) (ZT.ofNat q * eW))
    (hσ : Γ ⊢[PRAAx] ZT.eq (b + -a) (ZT.ofNat q * σ))
    (hω : Γ ⊢[PRAAx] ZT.eq (ev P (pt b)) (ZT.ofNat (pw q (succ K')) * ω)) :
    Γ ⊢[PRAAx] ZT.eq (stepZ P U b + -a) (ZT.ofNat q * (σ + -(U * (ZT.ofNat (pw q K') * ω)))) ⋏
      ZT.eq (ev P (pt (stepZ P U b))) (ZT.ofNat (pw q (succ (succ K'))) *
        (ω * eW + -(σ * ls (pd P 0) (pt b) (pt a) 0 * U * ω) +
          U * U * ZT.ofNat (pw q K') * ω * ω * tq P (pt b) (pt (-(U * ev P (pt b)))) 0 0)) := by
  have eJ := ZT.toZ_eq hJ
  have eS := ZT.toZ_eq hσ
  have eP := ZT.toZ_eq hω
  have eT := taylor_exact (Γ := Γ) (x := pt b) (v := pt (-(U * ev P (pt b)))) P
  have eD := diff_exact (Γ := Γ) (x := pt b) (y := pt a) (pd P 0)
  have eV := dv_eq (Γ := Γ) (x := pt b) (v := pt (-(U * ev P (pt b)))) P
  have eK := natEq (pw_succ (Γ := Γ) q K')
  have eK1 := natEq (pw_succ (Γ := Γ) q (succ K'))
  simp only [Analysis.PolynomialRemainder.rem, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat,
    ZT.toZ_natLit, Nat.cast_one, Fin.sum_univ_one, pt, jac] at eJ eS eP eT eD eV
  simp only [Q.mk_mul, map_mul] at eK eK1
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · simp only [stepZ, pt, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
    linear_combination (-ZT.toZ Γ U) * eP + eS + (-ZT.toZ Γ U * ZT.toZ Γ ω) * eK
  · simp only [stepZ, pt, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
    set zU := ZT.toZ Γ U
    set zw := ZT.toZ Γ ω
    set zs := ZT.toZ Γ σ
    set ze := ZT.toZ Γ eW
    set zl := ZT.toZ Γ (ls (pd P 0) (fun _ => b) (fun _ => a) 0)
    set zt := ZT.toZ Γ (tq P (fun _ => b) (fun _ => -(U * ev P fun _ => b)) 0 0)
    set zPb := ZT.toZ Γ (ev P fun _ => b)
    set zJb := ZT.toZ Γ (ev (pd P 0) fun _ => b)
    set zQK := Groth.ι (Q.mk Γ (pw q (succ K')))
    set zQKp := Groth.ι (Q.mk Γ (pw q K'))
    linear_combination (-zJb * zU + zPb * zU ^ 2 * zt + zQK * zU ^ 2 * zt * zw + 1) * eP +
      (-zQK * zU * zl * zw) * eS + (zQK * zw) * eJ + (-zQK * zU * zw) * eD + eT + eV +
      (zQK * zU ^ 2 * zt * zw ^ 2) * eK + (-zQKp * zU ^ 2 * zt * zw ^ 2 + zU * zl * zs * zw - ze * zw) * eK1

variable (P U)

/-- The iterates `b_r` of (L). -/
def seq (a : ZT k) : ℕ → ZT k
  | 0 => a
  | r + 1 => stepZ P U (seq a r)

/-- The witnesses `σ_r` (`b_r − a = q σ_r`) and `ω_r` (`P(b_r) = q^{r+1} ω_r`). -/
def wit (a eW w₀ : ZT k) (q : PTm k) : ℕ → ZT k × ZT k
  | 0 => (ZT.ofNat zero, w₀)
  | r + 1 =>
    let σ := (wit a eW w₀ q r).1
    let ω := (wit a eW w₀ q r).2
    let b := seq P U a r
    (σ + -(U * (ZT.ofNat (pw q (num r)) * ω)),
      ω * eW + -(σ * ls (pd P 0) (pt b) (pt a) 0 * U * ω) +
        U * U * ZT.ofNat (pw q (num r)) * ω * ω * tq P (pt b) (pt (-(U * ev P (pt b)))) 0 0)

variable {P U}

/-- (I): for every `r`, `b_r − a = q σ_r` and `P(b_r) = q^{r+1} ω_r`. -/
theorem invariant {a eW w₀ : ZT k} {q : PTm k}
    (hJ : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 + -(jac P a * U)) (ZT.ofNat q * eW))
    (hP : Γ ⊢[PRAAx] ZT.eq (ev P (pt a)) (ZT.ofNat q * w₀)) (r : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (seq P U a r + -a) (ZT.ofNat q * (wit P U a eW w₀ q r).1) ⋏
      ZT.eq (ev P (pt (seq P U a r))) (ZT.ofNat (pw q (num (r + 1))) * (wit P U a eW w₀ q r).2) := by
  induction r with
  | zero =>
    refine .andI (ZT.derive ?_) (ZT.derive ?_)
    · simp only [seq, wit, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_zero, map_zero]
      ring
    · have e := ZT.toZ_eq hP
      have e1 := natEq (pw_one (Γ := Γ) q)
      simp only [ZT.toZ_mul, ZT.toZ_ofNat] at e
      simp only [seq, wit, ZT.toZ_mul, ZT.toZ_ofNat]
      change ZT.toZ Γ (ev P (pt a)) = Groth.ι (Q.mk Γ (pw q one)) * ZT.toZ Γ w₀
      linear_combination e - ZT.toZ Γ w₀ * e1
  | succ r ih => exact step_eqs hJ (Prf.andE₁ ih) (Prf.andE₂ ih)

end LeanProofs.IPRA.Foundations.HenselIteration
