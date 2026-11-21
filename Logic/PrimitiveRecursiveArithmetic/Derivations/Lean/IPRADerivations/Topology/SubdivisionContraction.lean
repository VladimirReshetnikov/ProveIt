import IPRADerivations.Probability.GeometricTail
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Probability.MedianWeighted

/-!
# The contraction count of barycentric subdivision

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/07_spheres.tex`, Lemma
`lem:sphere-subdivision` (S02): "one subdivision has simplex diameter at most `nD/(n+1)`. If `n ≥ 1`, after
`r = n(k+1)` subdivisions an initial diameter bound `2` is reduced to at most `2^{−k}`. … `(1 + 1/n)^n ≥ 2` by
the first two binomial terms. Therefore `(n/(n+1))^n ≤ 1/2`."

With `n = e + 1 ≥ 1`:

* `half_contraction`: `2 n^n ≤ (n + 1)^n`, from the homogeneous Bernoulli inequality
  (`Probability/GeometricTail.bern_hom`);
* `subdivision_count`: `2^{k+1} n^{n(k+1)} ≤ (n + 1)^{n(k+1)}`, i.e. `2 (n/(n+1))^{n(k+1)} ≤ 2^{−k}`;
* `bary_coord` (the diameter step, "write `b_υ = (p/q)b_τ + (1/q)∑_{v∈υ∖τ} v`. Hence
  `‖b_υ − b_τ‖_∞ ≤ (q − p)D/q`"): in one coordinate, for the `q − p` added vertices `v` with `|v − b_τ| ≤ D`,
  `|∑ v − (q − p) b_τ| ≤ (q − p) D`, i.e. `q |b_υ − b_τ| ≤ (q − p) D`, for a list of vertices of any length.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.SubdivisionContraction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.GeometricTail (bern_hom)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_add_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(1 + 1/n)^n ≥ 2`, cleared: `2 n^n ≤ (n + 1)^n` for `n = e + 1`. -/
theorem half_contraction (e : PTm n) :
    Γ ⊢[PRAAx] le (two * pw (succ e) (succ e)) (pw (succ (succ e)) (succ e)) := by
  have h := bern_hom (Γ := Γ) (succ e) one e
  have p := natEq (pw_succ (Γ := Γ) (succ e) e)
  have c := natEq (congrAp2 (Γ := Γ) powF (.eqRefl (succ e)) (show Γ ⊢[PRAAx] succ e + one ≐ succ (succ e) by
    apply deriveNat; ipra_simps; ring))
  ipra_le sl h using
    rw [p] at *
    rw [← c]; ring

/-- After `r = n(k+1)` subdivisions: `2^{k+1} n^r ≤ (n + 1)^r`. -/
theorem subdivision_count (e k : PTm n) :
    Γ ⊢[PRAAx] le (pw two (succ k) * pw (succ e) (succ e * succ k))
      (pw (succ (succ e)) (succ e * succ k)) :=
  le_congr ((mul_pw _ _ _).eqTrans (congrMul (.eqRefl _) (pw_mul _ _ _))) (pw_mul _ _ _)
    (pw_le_pw (succ k) (half_contraction e))

/-- `∑ v` over a list of vertex coordinates. -/
def vsum : List (PTm n) → PTm n
  | [] => zero
  | v :: vs => v + vsum vs

/-- `|∑ v − m b| ≤ m D` for `m` vertices with `|v − b| ≤ D`. -/
theorem bary_coord (vs : List (PTm n)) {b D : PTm n} (h : ∀ v ∈ vs, Γ ⊢[PRAAx] le (ad v b) D) :
    Γ ⊢[PRAAx] le (ad (vsum vs) (num vs.length * b)) (num vs.length * D) := by
  induction vs with
  | nil =>
    show Γ ⊢[PRAAx] le (ad zero (num 0 * b)) (num 0 * D)
    have e : Γ ⊢[PRAAx] num 0 * b ≐ zero := by apply deriveNat; ipra_simps; ring
    have ce : Γ ⊢[PRAAx] ad zero (num 0 * b) ≐ ad zero zero :=
      congrAdd (congrMonus (.eqRefl _) e) (congrMonus e (.eqRefl _))
    have hz : Γ ⊢[PRAAx] ad zero zero ≐ zero :=
      (congrAdd (zero_monus zero) (zero_monus zero)).eqTrans (add_zero zero)
    exact le_congr (ce.eqTrans hz).eqSymm (.eqRefl _) (zero_le _)
  | cons v vs ih =>
    show Γ ⊢[PRAAx] le (ad (v + vsum vs) (num (vs.length + 1) * b)) (num (vs.length + 1) * D)
    have hv := h v List.mem_cons_self
    have hs := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have hab := ad_add_le (Γ := Γ) v (vsum vs) b (num vs.length * b)
    have e : Γ ⊢[PRAAx] num (vs.length + 1) * b ≐ b + num vs.length * b := by
      apply deriveNat; ipra_simps; push_cast; ring
    have ce : Γ ⊢[PRAAx] ad (v + vsum vs) (num (vs.length + 1) * b) ≐ ad (v + vsum vs) (b + num vs.length * b) :=
      congrAdd (congrMonus (.eqRefl _) e) (congrMonus e (.eqRefl _))
    have h1 := le_congr ce.eqSymm (.eqRefl _) hab
    refine le_trans h1 ?_
    ipra_le sl hv + sl hs using
      push_cast; ring

end LeanProofs.IPRA.Topology.SubdivisionContraction
