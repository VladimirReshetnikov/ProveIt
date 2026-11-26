import IPRADerivations.Probability.MedianWeighted
import IPRADerivations.Analysis.Observation.PrefixObject
import IPRADerivations.Foundations.FiniteObservations.MetricKernel
import IPRADerivations.Core.OrderCertificates

/-!
# The represented Boolean event algebra

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, Proposition "Represented
Boolean event algebra": "Complement is an isometry for `d_ev`, and union and intersection satisfy
`d_ev(A ∪ B, A' ∪ B'), d_ev(A ∩ B, A' ∩ B') ≤ d_ev(A, A') + d_ev(B, B')`", with
`d_ev(A, B) = P(A △ B) = d₁(1_A, 1_B)`.

On a finite cylinder table, events are columns of values (indicator bits, or any natural values) with cell
weights; union is the maximum `larger` (`Analysis/Observation/PrefixObject`), intersection the minimum `meet`
(`Foundations/FiniteObservations/MetricKernel`), complement `c ∸ a`. For an arbitrary finite list of cells
(an index type `α` with weight and value functions):

* `union_pt`, `inter_pt`: `|max(a, b) − max(a', b')|, |min(a, b) − min(a', b')| ≤ |a − a'| + |b − b'|`;
* `compl_pt`: `|(c ∸ a) − (c ∸ a')| ≤ |a − a'|` for `a, a' ≤ c` (and the reverse inequality by symmetry);
* `wsum_le`: a pointwise inequality `x ≤ y + z` passes to the weighted sums;
* `union_dist`, `inter_dist`, `compl_dist`: the proposition for the weighted distances `∑ w |·|`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.EventAlgebraMetric

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of le_add_ad)
open LeanProofs.IPRA.Analysis.Observation.PrefixObject (larger larger_le le_larger_left le_larger_right)
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right meet_le_left meet_le_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem up_bound (a a' b b' : PTm n) :
    Γ ⊢[PRAAx] le (larger a b) (larger a' b' + (ad a a' + ad b b')) := by
  have l1 := le_larger_left (Γ := Γ) a' b'
  have l2 := le_larger_right (Γ := Γ) a' b'
  have p1 := le_add_ad (Γ := Γ) a a'
  have p2 := le_add_ad (Γ := Γ) b b'
  refine larger_le ?_ ?_
  · ipra_le sl p1 + sl l1 + 𝔟 (ad b b')
  · ipra_le sl p2 + sl l2 + 𝔟 (ad a a')

/-- Union: `|max(a, b) − max(a', b')| ≤ |a − a'| + |b − b'|`. -/
theorem union_pt (a b a' b' : PTm n) :
    Γ ⊢[PRAAx] le (ad (larger a b) (larger a' b')) (ad a a' + ad b b') := by
  refine ad_le_of (up_bound a a' b b') ?_
  have h := up_bound (Γ := Γ) a' a b' b
  ipra_le sl h

private theorem down_bound (a a' b b' : PTm n) :
    Γ ⊢[PRAAx] le (meet a b) (meet a' b' + (ad a a' + ad b b')) := by
  refine .orE (le_total a' b') ?_ ?_
  · have m := meet_le_left (Γ := le a' b' :: Γ) a b
    refine le_congr (.eqRefl _) (congrAdd (meet_left Prf.hyp0).eqSymm (.eqRefl _)) ?_
    have p1' := le_add_ad (Γ := le a' b' :: Γ) a a'
    ipra_le sl m + sl p1' + 𝔟 (ad b b')
  · have m := meet_le_right (Γ := le b' a' :: Γ) a b
    refine le_congr (.eqRefl _) (congrAdd (meet_right Prf.hyp0).eqSymm (.eqRefl _)) ?_
    have p2' := le_add_ad (Γ := le b' a' :: Γ) b b'
    ipra_le sl m + sl p2' + 𝔟 (ad a a')

/-- Intersection: `|min(a, b) − min(a', b')| ≤ |a − a'| + |b − b'|`. -/
theorem inter_pt (a b a' b' : PTm n) :
    Γ ⊢[PRAAx] le (ad (meet a b) (meet a' b')) (ad a a' + ad b b') := by
  refine ad_le_of (down_bound a a' b b') ?_
  have h := down_bound (Γ := Γ) a' a b' b
  ipra_le sl h

/-- Complement: `|(c ∸ a) − (c ∸ a')| ≤ |a − a'|` for `a, a' ≤ c`. -/
theorem compl_pt {a a' c : PTm n} (ha : Γ ⊢[PRAAx] le a c) (ha' : Γ ⊢[PRAAx] le a' c) :
    Γ ⊢[PRAAx] le (ad (monus c a) (monus c a')) (ad a a') := by
  have e1 := natEq (eq_add_of_le ha)
  have e2 := natEq (eq_add_of_le ha')
  have q1 := le_add_ad (Γ := Γ) a' a
  have q2 := le_add_ad (Γ := Γ) a a'
  refine ad_le_of ?_ ?_
  · ipra_le sl q1 with e1 - e2
  · ipra_le sl q2 with e2 - e1

/-- `∑ w_i f_i` over a finite list of cells. -/
def wsum {α : Type} (w f : α → PTm n) : List α → PTm n
  | [] => zero
  | r :: rs => w r * f r + wsum w f rs

/-- A pointwise `x ≤ y + z` passes to weighted sums. -/
theorem wsum_le {α : Type} (w x y z : α → PTm n) (L : List α)
    (h : ∀ r ∈ L, Γ ⊢[PRAAx] le (x r) (y r + z r)) :
    Γ ⊢[PRAAx] le (wsum w x L) (wsum w y L + wsum w z L) := by
  induction L with
  | nil =>
    show Γ ⊢[PRAAx] le zero (zero + zero)
    ipra_le 0
  | cons r rs ih =>
    show Γ ⊢[PRAAx] le (w r * x r + wsum w x rs) ((w r * y r + wsum w y rs) + (w r * z r + wsum w z rs))
    have hr := h r List.mem_cons_self
    have hs := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    ipra_le 𝔟 (w r) * sl hr + sl hs

variable {α : Type} (w a b a' b' : α → PTm n) (L : List α)

/-- `d_ev(A ∪ B, A' ∪ B') ≤ d_ev(A, A') + d_ev(B, B')`. -/
theorem union_dist :
    Γ ⊢[PRAAx] le (wsum w (fun r => ad (larger (a r) (b r)) (larger (a' r) (b' r))) L)
      (wsum w (fun r => ad (a r) (a' r)) L + wsum w (fun r => ad (b r) (b' r)) L) :=
  wsum_le w _ _ _ L fun r _ => union_pt _ _ _ _

/-- `d_ev(A ∩ B, A' ∩ B') ≤ d_ev(A, A') + d_ev(B, B')`. -/
theorem inter_dist :
    Γ ⊢[PRAAx] le (wsum w (fun r => ad (meet (a r) (b r)) (meet (a' r) (b' r))) L)
      (wsum w (fun r => ad (a r) (a' r)) L + wsum w (fun r => ad (b r) (b' r)) L) :=
  wsum_le w _ _ _ L fun r _ => inter_pt _ _ _ _

/-- Complement does not increase `d_ev`: `d_ev(Aᶜ, A'ᶜ) ≤ d_ev(A, A')` (indicator values `≤ c`). -/
theorem compl_dist (c : PTm n) (ha : ∀ r ∈ L, Γ ⊢[PRAAx] le (a r) c) (ha' : ∀ r ∈ L, Γ ⊢[PRAAx] le (a' r) c) :
    Γ ⊢[PRAAx] le (wsum w (fun r => ad (monus c (a r)) (monus c (a' r))) L)
      (wsum w (fun r => ad (a r) (a' r)) L + wsum w (fun _ => zero) L) :=
  wsum_le w _ _ _ L fun r hr =>
    le_congr (.eqRefl _) (add_zero _).eqSymm (compl_pt (ha r hr) (ha' r hr))

end LeanProofs.IPRA.Probability.EventAlgebraMetric
