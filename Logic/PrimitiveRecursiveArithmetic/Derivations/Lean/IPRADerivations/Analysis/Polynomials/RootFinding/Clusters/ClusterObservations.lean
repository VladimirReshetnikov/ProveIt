import IPRADerivations.Analysis.Polynomials.Evaluation.PolynomialCertificates
import Mathlib.Data.List.Sublists

/-!
# Polynomial observations of matched clusters

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/06_clusters.tex`, Proposition
`prop:cluster-polynomial-observations` ("If a matching has error at most `δ`, then, for `k ≥ 1`,
`‖∑ a_i^k − ∑ b_i^k‖ ≤ N k R^{k−1} δ`. For `1 ≤ k ≤ N`, the elementary symmetric polynomials satisfy
`‖e_k(a) − e_k(b)‖ ≤ C(N, k) k R^{k−1} δ`"), for matched lists of `N` nonnegative centers given by natural terms
(the nonnegative real case of the paper's Gaussian-rational statement), with `a_i, b_i ≤ R` and
`|a_i − b_i| ≤ δ` after reordering by the matching:

* `power_sums`: `|∑_i a_i^{k+1} − ∑_i b_i^{k+1}| ≤ N (k+1) R^k δ`, by `PolynomialCertificates.pow_ad`;
* `prod_ad` ("subtract the two corresponding products by changing one factor at a time. The telescoping sum has
  `k` terms, each bounded by `R^{k−1} δ`"): `|∏_{j ∈ S} a_j − ∏_{j ∈ S} b_j| ≤ (k+1) R^k δ` for a list `S` of
  `k + 1` indices;
* `esym_bound`: for `e_{k+1}` as the sum over the `(k+1)`-element sublists of the indices (`List.sublistsLen`),
  `|e_{k+1}(a) − e_{k+1}(b)| ≤ C(N, k+1) (k+1) R^k δ`.
-/

namespace LeanProofs.IPRA.Analysis.ClusterObservations

open_ipra
open LeanProofs.IPRA.Analysis.PolynomialCertificates (mpow pow_ad ad_mul_step ad_self)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_add_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The sum of a list of terms. -/
def lsum : List (PTm n) → PTm n
  | [] => zero
  | t :: L => t + lsum L

theorem ad_lsum_le {α : Type} (F G : α → PTm n) : (S : List α) →
    Γ ⊢[PRAAx] le (ad (lsum (S.map F)) (lsum (S.map G))) (lsum (S.map fun s => ad (F s) (G s)))
  | [] => ad_self zero
  | s :: S => by
    have h1 := ad_add_le (Γ := Γ) (F s) (lsum (S.map F)) (G s) (lsum (S.map G))
    have ih := ad_lsum_le F G S
    show Γ ⊢[PRAAx] le (ad (F s + lsum (S.map F)) (G s + lsum (S.map G)))
      (ad (F s) (G s) + lsum (S.map fun s => ad (F s) (G s)))
    ipra_le sl h1 + sl ih

theorem lsum_le_const {α : Type} (H : α → PTm n) (c : PTm n) : (S : List α) →
    (∀ s ∈ S, Γ ⊢[PRAAx] le (H s) c) → (Γ ⊢[PRAAx] le (lsum (S.map H)) (num S.length * c))
  | [], _ => by show Γ ⊢[PRAAx] le zero (num 0 * c); ipra_le 0
  | s :: S, h => by
    have hs := h s List.mem_cons_self
    have ih := lsum_le_const H c S fun t ht => h t (List.mem_cons_of_mem _ ht)
    show Γ ⊢[PRAAx] le (H s + lsum (S.map H)) (num (S.length + 1) * c)
    ipra_le sl hs + sl ih using push_cast; ring

/-- `∏_{j ∈ S} a_j`. -/
def prodL {α : Type} (a : α → PTm n) : List α → PTm n
  | [] => one
  | j :: L => a j * prodL a L

theorem prodL_le {α : Type} {a : α → PTm n} {R : PTm n} (ha : ∀ j, Γ ⊢[PRAAx] le (a j) R) :
    (L : List α) → Γ ⊢[PRAAx] le (prodL a L) (mpow R L.length)
  | [] => le_refl _
  | j :: L => by
    have ih := prodL_le ha L
    have hj := ha j
    show Γ ⊢[PRAAx] le (a j * prodL a L) (R * mpow R L.length)
    ipra_le 𝔟 R * sl ih + 𝔟 (prodL a L) * sl hj

variable {α : Type} {a b : α → PTm n} {R δ : PTm n}

/-- One product of `k + 1` factors: `|∏ a_j − ∏ b_j| ≤ (k+1) R^k δ`. -/
theorem prod_ad (ha : ∀ j, Γ ⊢[PRAAx] le (a j) R) (hb : ∀ j, Γ ⊢[PRAAx] le (b j) R)
    (hd : ∀ j, Γ ⊢[PRAAx] le (ad (a j) (b j)) δ) :
    ∀ (j : α) (L : List α), Γ ⊢[PRAAx] le (ad (prodL a (j :: L)) (prodL b (j :: L)))
      (num (L.length + 1) * mpow R L.length * δ)
  | j, [] => by
    have step := ad_mul_step (Γ := Γ) (a j) (b j) one one
    have h11 := ad_self (Γ := Γ) (one : PTm n)
    have hdj := hd j
    show Γ ⊢[PRAAx] le (ad (a j * one) (b j * one)) (num 1 * one * δ)
    ipra_le sl step + 𝔟 (a j) * sl h11 + sl hdj
  | j, q :: L => by
    have step := ad_mul_step (Γ := Γ) (a j) (b j) (prodL a (q :: L)) (prodL b (q :: L))
    have ih := prod_ad ha hb hd q L
    have haj := ha j
    have hdj := hd j
    have hQ : Γ ⊢[PRAAx] le (prodL b (q :: L)) (R * mpow R L.length) := prodL_le hb (q :: L)
    show Γ ⊢[PRAAx] le (ad (a j * prodL a (q :: L)) (b j * prodL b (q :: L)))
      (num (L.length + 1 + 1) * (R * mpow R L.length) * δ)
    ipra_le sl step + 𝔟 R * sl ih +
      (𝔟 (monus (prodL a (q :: L)) (prodL b (q :: L))) + 𝔟 (monus (prodL b (q :: L)) (prodL a (q :: L)))) * sl haj +
      𝔟 (prodL b (q :: L)) * sl hdj + 𝔟 δ * sl hQ using push_cast; ring

/-- Power sums: `|∑_i a_i^{k+1} − ∑_i b_i^{k+1}| ≤ N (k+1) R^k δ`. -/
theorem power_sums {N : ℕ} {a b : Fin N → PTm n} (ha : ∀ j, Γ ⊢[PRAAx] le (a j) R)
    (hb : ∀ j, Γ ⊢[PRAAx] le (b j) R) (hd : ∀ j, Γ ⊢[PRAAx] le (ad (a j) (b j)) δ) (k : ℕ) :
    Γ ⊢[PRAAx] le (ad (lsum ((List.finRange N).map fun i => mpow (a i) (k + 1)))
        (lsum ((List.finRange N).map fun i => mpow (b i) (k + 1))))
      (num N * (num (k + 1) * mpow R k * δ)) := by
  have h := ad_lsum_le (Γ := Γ) (fun i => mpow (a i) (k + 1)) (fun i => mpow (b i) (k + 1)) (List.finRange N)
  have hc := lsum_le_const (Γ := Γ) (fun i => ad (mpow (a i) (k + 1)) (mpow (b i) (k + 1)))
    (num (k + 1) * mpow R k * δ) (List.finRange N) fun i _ => by
      have p := pow_ad (ha i) (hb i) k
      have d := hd i
      ipra_le sl p + ((k : Groth (Q Γ)) + 1) * 𝔟 (mpow R k) * sl d using push_cast; ring
  rw [List.length_finRange] at hc
  exact le_trans h hc

/-- `e_{k+1}` as the sum of the products over the `(k+1)`-element sublists of the indices. -/
def esym {N : ℕ} (a : Fin N → PTm n) (k : ℕ) : PTm n :=
  lsum ((List.sublistsLen (k + 1) (List.finRange N)).map fun S => prodL a S)

/-- `|e_{k+1}(a) − e_{k+1}(b)| ≤ C(N, k+1) (k+1) R^k δ`. -/
theorem esym_bound {N : ℕ} {a b : Fin N → PTm n} (ha : ∀ j, Γ ⊢[PRAAx] le (a j) R)
    (hb : ∀ j, Γ ⊢[PRAAx] le (b j) R) (hd : ∀ j, Γ ⊢[PRAAx] le (ad (a j) (b j)) δ) (k : ℕ) :
    Γ ⊢[PRAAx] le (ad (esym a k) (esym b k)) (num (N.choose (k + 1)) * (num (k + 1) * mpow R k * δ)) := by
  have h := ad_lsum_le (Γ := Γ) (fun S => prodL a S) (fun S => prodL b S)
    (List.sublistsLen (k + 1) (List.finRange N))
  have hc := lsum_le_const (Γ := Γ) (fun S => ad (prodL a S) (prodL b S)) (num (k + 1) * mpow R k * δ)
    (List.sublistsLen (k + 1) (List.finRange N)) fun S hS => by
      have hl := List.length_of_sublistsLen hS
      match S, hl with
      | j :: L, hl =>
        have hL : L.length = k := by simpa using hl
        have p := prod_ad ha hb hd j L
        rw [hL] at p
        exact p
  rw [List.length_sublistsLen, List.length_finRange] at hc
  exact le_trans h hc

end LeanProofs.IPRA.Analysis.ClusterObservations
