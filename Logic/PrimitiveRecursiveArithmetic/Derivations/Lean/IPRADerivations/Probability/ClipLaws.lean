import IPRADerivations.Probability.EventAlgebraMetric
import IPRADerivations.Probability.Minkowski

/-!
# Clipping, excess and the capped distance on finite tables

Packets: `foundations/ipra_measure_transport_2026-11-20`, `lean/Truncation.lean` (host-level Lean there:
`clip_bounds`, `clip_lipschitz`, `clip_error_exact`, `excess_lipschitz`, `rho_bounds`, `rho_le_abs`,
`rho_triangle`, `truncation_pointwise`, `clip_rho_bound`), and `probability/ipra_probability_2026-11-20`, Lemma
`lem:prob-clipping` ("`d₁(f, g) ≤ max(1, 2K) d₀(f, g) + I(R_K(f)) + I(R_K(g))`"). Object-level derivations for
nonnegative values (absolute values, natural numerators on a scale `D` for `1`), with the clip
`T_K(x) = min(K, x)` (`meet K x`), the excess `R_K(x) = (x − K)^+` (`monus x K`) and the capped distance
`ρ(x, y) = min(1, |x − y|)` (`meet D (ad x y)`):

* `clip_le`, `clip_le_self`, `clip_split` (`T_K(x) + R_K(x) = x`), `clip_lipschitz`, `excess_lipschitz`;
* `ad_triangle`, `rho_le`, `rho_le_abs`, `rho_triangle` (`ρ(x, z) ≤ ρ(x, y) + ρ(y, z)`);
* `truncation_pt` (`|x − y| ≤ |T_K x − T_K y| + R_K x + R_K y`), `clip_rho` (`D |T_K x − T_K y| ≤ K ρ(x, y)`
  for `K ≥ D`, i.e. `|T_K x − T_K y| ≤ K min(1, |x − y|)`);
* `clipping`: on a finite weighted table, `D d₁(f, g) ≤ K d₀(f, g) + D (I(R_K f) + I(R_K g))`, the clipping
  estimate for nonnegative tables.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.ClipLaws

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of le_add_ad ad_add_le)
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum wsum_le inter_pt)
open LeanProofs.IPRA.Probability.Minkowski (monus_le_of_le_add)
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right meet_le_left meet_le_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem clip_le (K x : PTm n) : Γ ⊢[PRAAx] le (meet K x) K := meet_le_left K x

theorem clip_le_self (K x : PTm n) : Γ ⊢[PRAAx] le (meet K x) x := meet_le_right K x

/-- `T_K(x) + R_K(x) = x`. -/
theorem clip_split (K x : PTm n) : Γ ⊢[PRAAx] meet K x + monus x K ≐ x := by
  refine .orE (le_total K x) ?_ ?_
  · have e1 := natEq (meet_left (Γ := le K x :: Γ) (Prf.hyp0 : (le K x :: Γ) ⊢[PRAAx] le K x))
    have e2 := natEq (eq_add_of_le (Prf.hyp0 : (le K x :: Γ) ⊢[PRAAx] le K x))
    apply deriveNat; ipra_simps
    linear_combination e1 - e2
  · have e1 := natEq (meet_right (Γ := le x K :: Γ) (Prf.hyp0 : (le x K :: Γ) ⊢[PRAAx] le x K))
    have e2 := natEq (Prf.hyp0 : (le x K :: Γ) ⊢[PRAAx] monus x K ≐ zero)
    apply deriveNat; ipra_simps
    linear_combination e1 + e2

/-- `|T_K x − T_K y| ≤ |x − y|`. -/
theorem clip_lipschitz (K x y : PTm n) : Γ ⊢[PRAAx] le (ad (meet K x) (meet K y)) (ad x y) := by
  have h := inter_pt (Γ := Γ) K x K y
  have e := natEq (le_refl (Γ := Γ) K)
  ipra_le sl h with e + e

/-- `|R_K x − R_K y| ≤ |x − y|`. -/
theorem excess_lipschitz (K x y : PTm n) : Γ ⊢[PRAAx] le (ad (monus x K) (monus y K)) (ad x y) := by
  refine ad_le_of ?_ ?_
  · refine monus_le_of_le_add ?_
    have s := natEq (clip_split (Γ := Γ) K y)
    have c := clip_le (Γ := Γ) K y
    have p := le_add_ad (Γ := Γ) x y
    ipra_le sl p + sl c with s
  · refine monus_le_of_le_add ?_
    have s := natEq (clip_split (Γ := Γ) K x)
    have c := clip_le (Γ := Γ) K x
    have p := le_add_ad (Γ := Γ) y x
    ipra_le sl p + sl c with s

/-- `|x − z| ≤ |x − y| + |y − z|`. -/
theorem ad_triangle (x y z : PTm n) : Γ ⊢[PRAAx] le (ad x z) (ad x y + ad y z) := by
  have p1 := le_add_ad (Γ := Γ) x y
  have p2 := le_add_ad (Γ := Γ) y z
  have q1 := le_add_ad (Γ := Γ) z y
  have q2 := le_add_ad (Γ := Γ) y x
  refine ad_le_of ?_ ?_
  · ipra_le sl p1 + sl p2
  · ipra_le sl q1 + sl q2

theorem rho_le (D x y : PTm n) : Γ ⊢[PRAAx] le (meet D (ad x y)) D := meet_le_left _ _

theorem rho_le_abs (D x y : PTm n) : Γ ⊢[PRAAx] le (meet D (ad x y)) (ad x y) := meet_le_right _ _

/-- `ρ(x, z) ≤ ρ(x, y) + ρ(y, z)`. -/
theorem rho_triangle (D x y z : PTm n) :
    Γ ⊢[PRAAx] le (meet D (ad x z)) (meet D (ad x y) + meet D (ad y z)) := by
  refine .orE (le_total D (ad x y)) ?_ ?_
  · have m := meet_le_left (Γ := le D (ad x y) :: Γ) D (ad x z)
    have e := natEq (meet_left (Γ := le D (ad x y) :: Γ) Prf.hyp0)
    ipra_le sl m + 𝔟 (meet D (ad y z)) with e
  · refine .orE (le_total D (ad y z)) ?_ ?_
    · have m := meet_le_left (Γ := le D (ad y z) :: le (ad x y) D :: Γ) D (ad x z)
      have e := natEq (meet_left (Γ := le D (ad y z) :: le (ad x y) D :: Γ) Prf.hyp0)
      ipra_le sl m + 𝔟 (meet D (ad x y)) with e
    · let Δ := le (ad y z) D :: le (ad x y) D :: Γ
      have e1 := natEq (meet_right (Γ := Δ) (Prf.hyp1 : Δ ⊢[PRAAx] le (ad x y) D))
      have e2 := natEq (meet_right (Γ := Δ) (Prf.hyp0 : Δ ⊢[PRAAx] le (ad y z) D))
      have m := meet_le_right (Γ := Δ) D (ad x z)
      have t := ad_triangle (Γ := Δ) x y z
      ipra_le sl m + sl t with e1 + e2

/-- `|x − y| ≤ |T_K x − T_K y| + R_K x + R_K y`. -/
theorem truncation_pt (K x y : PTm n) :
    Γ ⊢[PRAAx] le (ad x y) (ad (meet K x) (meet K y) + (monus x K + monus y K)) := by
  have sx := clip_split (Γ := Γ) K x
  have sy := clip_split (Γ := Γ) K y
  have h := ad_add_le (Γ := Γ) (meet K x) (monus x K) (meet K y) (monus y K)
  have hr : Γ ⊢[PRAAx] le (ad (monus x K) (monus y K)) (monus x K + monus y K) :=
    ad_le_of (by ipra_le 𝔟 (monus y K) + 𝔟 (monus y K)) (by ipra_le 𝔟 (monus x K) + 𝔟 (monus x K))
  have h' := le_congr (congrAdd (congrMonus sx sy) (congrMonus sy sx)) (.eqRefl _) h
  ipra_le sl h' + sl hr

/-- `D |T_K x − T_K y| ≤ K ρ(x, y)` for `K ≥ D`. -/
theorem clip_rho {D K : PTm n} (x y : PTm n) (hDK : Γ ⊢[PRAAx] le D K) :
    Γ ⊢[PRAAx] le (D * ad (meet K x) (meet K y)) (K * meet D (ad x y)) := by
  have hl := clip_lipschitz (Γ := Γ) K x y
  have ck : Γ ⊢[PRAAx] le (ad (meet K x) (meet K y)) K := by
    have cx := clip_le (Γ := Γ) K x
    have cy := clip_le (Γ := Γ) K y
    exact ad_le_of (by ipra_le sl cx + 𝔟 (meet K y)) (by ipra_le sl cy + 𝔟 (meet K x))
  refine .orE (le_total D (ad x y)) ?_ ?_
  · have e := natEq (meet_left (Γ := le D (ad x y) :: Γ) Prf.hyp0)
    have ck' : (le D (ad x y) :: Γ) ⊢[PRAAx] le (ad (meet K x) (meet K y)) K := ck.wk
    ipra_le 𝔟 D * sl ck' with 𝔟 K * e
  · have e := natEq (meet_right (Γ := le (ad x y) D :: Γ) Prf.hyp0)
    have hl' : (le (ad x y) D :: Γ) ⊢[PRAAx] le (ad (meet K x) (meet K y)) (ad x y) := hl.wk
    have hDK' : (le (ad x y) D :: Γ) ⊢[PRAAx] le D K := hDK.wk
    ipra_le 𝔟 D * sl hl' + 𝔟 (ad x y) * sl hDK' with 𝔟 K * e

/-- `lem:prob-clipping` for nonnegative tables: `D d₁ ≤ K d₀ + D (I(R_K f) + I(R_K g))`. -/
theorem clipping {α : Type} (w f g : α → PTm n) (L : List α) {D K : PTm n} (hDK : Γ ⊢[PRAAx] le D K) :
    Γ ⊢[PRAAx] le (wsum w (fun r => D * ad (f r) (g r)) L)
      (wsum w (fun r => K * meet D (ad (f r) (g r))) L +
        wsum w (fun r => D * (monus (f r) K + monus (g r) K)) L) :=
  wsum_le w _ _ _ L fun r _ => by
    have t := truncation_pt (Γ := Γ) K (f r) (g r)
    have c := clip_rho (Γ := Γ) (f r) (g r) hDK
    ipra_le 𝔟 D * sl t + sl c

end LeanProofs.IPRA.Probability.ClipLaws
