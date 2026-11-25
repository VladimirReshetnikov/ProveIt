import IPRADerivations.AnalyticNumberTheory.AbsDiff
import IPRADerivations.Core.LinearCombination

/-!
# The open cube is homeomorphic to Euclidean space

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/04_metric.tex`, Proposition
`prop:euclidean-open-cube`: coordinatewise `h(t) = t/(1+|t|)`, `h⁻¹(s) = s/(1−|s|)` give `ℝ^d ≅ (−1,1)^d`; the forward
map is `1`-Lipschitz in sup norm, and on `|s_i| ≤ 1 − δ` the inverse is `δ^{−2}`-Lipschitz. The proof is "rational case
splits": same sign and opposite sign, on the magnitudes. With `|a − b|` the natural distance `AbsDiff.absd`:

* forward map, magnitudes `t, u ≥ 0`:
  - `fwd_same`: `|t(1+u) − u(1+t)| = |t − u|`, so `|h(t) − h(u)| = |t − u|/((1+t)(1+u)) ≤ |t − u|`
    (`fwd_same_le`, cleared by `(1+t)(1+u)`);
  - `fwd_opp`: `t(1+u) + u(1+t) ≤ (t + u)(1+t)(1+u)`, i.e. `|h(t)| + |h(u)| ≤ |t| + |u|` (opposite signs);
  - `fwd_bound`: `t ≤ 1 + t`, i.e. `h(t) < 1`;
* inverse map, `s = σ/M`, `v = τ/M` with `σ, τ ≤ M − D` (`D = δM ≥ 1`):
  - `inv_same`: `|σ(M−τ) − τ(M−σ)| = M|σ − τ|`, and `inv_den`: `D² ≤ (M−σ)(M−τ)`, so
    `inv_same_le`: `D² |σ(M−τ) − τ(M−σ)| ≤ M |σ − τ| (M−σ)(M−τ)`, i.e.
    `|h⁻¹(s) − h⁻¹(v)| ≤ |s − v|/δ²` for `s, v` of the same sign;
  - `inv_opp`: `D² (σ(M−τ) + τ(M−σ)) ≤ M (σ + τ)(M−σ)(M−τ)`, the sum of the one-sided estimates across zero;
* the maps are inverse: `inv_fwd`: `h⁻¹(a/(b+a)) = a/b` (`(b + a) − a = b`), and `fwd_inv`: `h(σ/(M−σ)) = σ/M`
  (`(M − σ) + σ = M` for `σ ≤ M`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.OpenCubeHomeo

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `monus (x + c) (y + c) = monus x y`. -/
theorem monus_add_cancel (x y c : PTm n) : Γ ⊢[PRAAx] monus (x + c) (y + c) ≐ monus x y := by
  refine .orE (le_total y x) ?_ ?_
  · let C : List (Fm PTm n) := le y x :: Γ
    have e := natEq (eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] le y x))
    have h1 : C ⊢[PRAAx] le (y + c) (x + c) := le_of_eq_add (d := monus x y) (by
      ipra_lc e)
    ipra_lc e - natEq (eq_add_of_le h1)
  · let C : List (Fm PTm n) := le x y :: Γ
    have h0 : C ⊢[PRAAx] monus x y ≐ zero := Prf.hyp0
    have h1 : C ⊢[PRAAx] le (x + c) (y + c) := by
      have e := natEq (eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] le x y))
      exact le_of_eq_add (d := monus y x) (by apply deriveNat; ipra_simps; linear_combination e)
    exact (h1 : C ⊢[PRAAx] monus (x + c) (y + c) ≐ zero).eqTrans h0.eqSymm

/-! ## The forward map -/

/-- `|t(1+u) − u(1+t)| = |t − u|`. -/
theorem fwd_same (t u : PTm n) : Γ ⊢[PRAAx] absd (t * succ u) (u * succ t) ≐ absd t u := by
  have e1 : Γ ⊢[PRAAx] t * succ u ≐ t + t * u := by ipra_ring
  have e2 : Γ ⊢[PRAAx] u * succ t ≐ u + t * u := by ipra_ring
  exact congrAdd ((congrMonus e1 e2).eqTrans (monus_add_cancel _ _ _))
    ((congrMonus e2 e1).eqTrans (monus_add_cancel _ _ _))

/-- `|h(t) − h(u)| ≤ |t − u|` for `t, u ≥ 0`, cleared: `|t(1+u) − u(1+t)| ≤ |t − u| (1+t)(1+u)`. -/
theorem fwd_same_le (t u : PTm n) :
    Γ ⊢[PRAAx] le (absd (t * succ u) (u * succ t)) (absd t u * (succ t * succ u)) := by
  refine le_of_eq_add (d := absd t u * (t + u + t * u)) ?_
  ipra_lc -natEq (fwd_same (Γ := Γ) t u)

/-- `|h(t)| + |h(u)| ≤ |t| + |u|`, cleared: `t(1+u) + u(1+t) ≤ (t + u)(1+t)(1+u)`. -/
theorem fwd_opp (t u : PTm n) :
    Γ ⊢[PRAAx] le (t * succ u + u * succ t) ((t + u) * (succ t * succ u)) := by
  refine le_of_eq_add (d := t * t + u * u + t * t * u + t * u * u) ?_
  ipra_ring

/-- `h(t) < 1`: `t < 1 + t`. -/
theorem fwd_bound (t : PTm n) : Γ ⊢[PRAAx] lt t (succ t) := le_refl _

/-! ## The inverse map -/

/-- `|σ(M−τ) − τ(M−σ)| = M |σ − τ|` for `σ, τ ≤ M`. -/
theorem inv_same {σ τ M : PTm n} (hs : Γ ⊢[PRAAx] le σ M) (ht : Γ ⊢[PRAAx] le τ M) :
    Γ ⊢[PRAAx] absd (σ * monus M τ) (τ * monus M σ) ≐ M * absd σ τ := by
  have a1 : Γ ⊢[PRAAx] σ * monus M τ + σ * τ ≐ M * σ := by
    ipra_lc (-(𝔞 σ)) * natEq (eq_add_of_le ht)
  have a2 : Γ ⊢[PRAAx] τ * monus M σ + σ * τ ≐ M * τ := by
    ipra_lc (-(𝔞 τ)) * natEq (eq_add_of_le hs)
  have m1 : Γ ⊢[PRAAx] monus (σ * monus M τ) (τ * monus M σ) ≐ monus (M * σ) (M * τ) :=
    (monus_add_cancel _ _ (σ * τ)).eqSymm.eqTrans (congrMonus a1 a2)
  have m2 : Γ ⊢[PRAAx] monus (τ * monus M σ) (σ * monus M τ) ≐ monus (M * τ) (M * σ) :=
    (monus_add_cancel _ _ (σ * τ)).eqSymm.eqTrans (congrMonus a2 a1)
  refine (congrAdd m1 m2).eqTrans ?_
  refine .orE (le_total σ τ) ?_ ?_
  · let C : List (Fm PTm n) := le σ τ :: Γ
    have h : C ⊢[PRAAx] le σ τ := Prf.hyp0
    have z1 : C ⊢[PRAAx] monus σ τ ≐ zero := h
    have z2 : C ⊢[PRAAx] monus (M * σ) (M * τ) ≐ zero := le_mul_mono (le_refl M) h
    have d := natEq (eq_add_of_le h)
    have dM := natEq (eq_add_of_le (le_mul_mono (le_refl M) h : C ⊢[PRAAx] le (M * σ) (M * τ)))
    have zz1 := natEq z1
    have zz2 := natEq z2
    apply deriveNat; ipra_simps
    linear_combination zz2 - dM - 𝔞 M * zz1 + 𝔞 M * d
  · let C : List (Fm PTm n) := le τ σ :: Γ
    have h : C ⊢[PRAAx] le τ σ := Prf.hyp0
    have z1 : C ⊢[PRAAx] monus τ σ ≐ zero := h
    have z2 : C ⊢[PRAAx] monus (M * τ) (M * σ) ≐ zero := le_mul_mono (le_refl M) h
    have d := natEq (eq_add_of_le h)
    have dM := natEq (eq_add_of_le (le_mul_mono (le_refl M) h : C ⊢[PRAAx] le (M * τ) (M * σ)))
    have zz1 := natEq z1
    have zz2 := natEq z2
    apply deriveNat; ipra_simps
    linear_combination zz2 - dM - 𝔞 M * zz1 + 𝔞 M * d

/-- `D² ≤ (M − σ)(M − τ)` for `σ, τ ≤ M − D`. -/
theorem inv_den {σ τ M D : PTm n} (hs : Γ ⊢[PRAAx] le (σ + D) M) (ht : Γ ⊢[PRAAx] le (τ + D) M) :
    Γ ⊢[PRAAx] le (D * D) (monus M σ * monus M τ) := by
  have ls : Γ ⊢[PRAAx] le σ M := le_trans (le_of_eq_add (d := D) (.eqRefl _)) hs
  have lt' : Γ ⊢[PRAAx] le τ M := le_trans (le_of_eq_add (d := D) (.eqRefl _)) ht
  have a : Γ ⊢[PRAAx] le D (monus M σ) := le_of_eq_add (d := monus M (σ + D)) (by
    ipra_lc natEq (eq_add_of_le hs) - natEq (eq_add_of_le ls))
  have b : Γ ⊢[PRAAx] le D (monus M τ) := le_of_eq_add (d := monus M (τ + D)) (by
    ipra_lc natEq (eq_add_of_le ht) - natEq (eq_add_of_le lt'))
  exact le_mul_mono a b

/-- `|h⁻¹(s) − h⁻¹(v)| ≤ |s − v|/δ²` for `s = σ/M`, `v = τ/M` of the same sign, `σ, τ ≤ M − D`:
`D² |σ(M−τ) − τ(M−σ)| ≤ M |σ − τ| (M−σ)(M−τ)`. -/
theorem inv_same_le {σ τ M D : PTm n} (hs : Γ ⊢[PRAAx] le (σ + D) M) (ht : Γ ⊢[PRAAx] le (τ + D) M) :
    Γ ⊢[PRAAx] le (D * D * absd (σ * monus M τ) (τ * monus M σ)) (M * absd σ τ * (monus M σ * monus M τ)) := by
  have ls : Γ ⊢[PRAAx] le σ M := le_trans (le_of_eq_add (d := D) (.eqRefl _)) hs
  have lt' : Γ ⊢[PRAAx] le τ M := le_trans (le_of_eq_add (d := D) (.eqRefl _)) ht
  have e := inv_same ls lt'
  have m := le_mul_mono (inv_den hs ht) (le_refl (M * absd σ τ))
  exact le_congr (congrMul (.eqRefl _) e).eqSymm (mul_comm _ _) m

/-- Across zero: `D² (σ(M−τ) + τ(M−σ)) ≤ M (σ + τ)(M−σ)(M−τ)`, i.e. `|h⁻¹(s)| + |h⁻¹(v)| ≤ (|s| + |v|)/δ²`. -/
theorem inv_opp {σ τ M D : PTm n} (hs : Γ ⊢[PRAAx] le (σ + D) M) (ht : Γ ⊢[PRAAx] le (τ + D) M) :
    Γ ⊢[PRAAx] le (D * D * (σ * monus M τ + τ * monus M σ)) (M * (σ + τ) * (monus M σ * monus M τ)) := by
  have ls : Γ ⊢[PRAAx] le σ M := le_trans (le_of_eq_add (d := D) (.eqRefl _)) hs
  have lt' : Γ ⊢[PRAAx] le τ M := le_trans (le_of_eq_add (d := D) (.eqRefl _)) ht
  have num : Γ ⊢[PRAAx] le (σ * monus M τ + τ * monus M σ) (M * (σ + τ)) :=
    le_of_eq_add (d := two * (σ * τ)) (by
      ipra_lc 𝔞 σ * natEq (eq_add_of_le lt') + 𝔞 τ * natEq (eq_add_of_le ls))
  have m := le_mul_mono (inv_den hs ht) num
  exact le_congr (.eqRefl _) (by ipra_ring) m

/-! ## The maps are inverse -/

/-- `h⁻¹(h(a/b)) = a/b`: `h(a/b) = a/(b + a)` and `(b + a) − a = b`. -/
theorem inv_fwd (a b : PTm n) : Γ ⊢[PRAAx] monus (b + a) a ≐ b :=
  (congrMonus (.eqRefl _) (zero_add a).eqSymm).eqTrans ((monus_add_cancel b zero a).eqTrans (monus_zero b))

/-- `h(h⁻¹(σ/M)) = σ/M`: `h⁻¹(σ/M) = σ/(M − σ)` and `(M − σ) + σ = M` for `σ ≤ M`. -/
theorem fwd_inv {σ M : PTm n} (hs : Γ ⊢[PRAAx] le σ M) : Γ ⊢[PRAAx] monus M σ + σ ≐ M :=
  (add_comm _ _).eqTrans (eq_add_of_le hs).eqSymm

end LeanProofs.IPRA.Topology.OpenCubeHomeo
