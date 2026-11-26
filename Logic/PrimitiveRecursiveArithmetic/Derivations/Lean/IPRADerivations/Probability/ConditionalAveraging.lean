import IPRADerivations.Foundations.PartitionRefinement
import IPRADerivations.Probability.MedianWeighted

/-!
# Conditional averaging on a finite partition

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, Theorem "Conditional
averaging and a quantified martingale limit": "The finite maps `C_n` preserve positivity and expectation, are
`d₁` contractions, and satisfy `C_n C_m = C_{min(n,m)}` … For an `F_n` cylinder variable `h`, the same finite
regrouping gives `I(h C_n f) = I(h f)` … If `n ≥ ℓ(k)`, then `C_n x_k = x_k`. Hence
`‖C_n X − X‖₁ ≤ ‖C_n(X − x_k)‖₁ + ‖x_k − X‖₁`".

Fine cells `j < m` carry natural weights `W_j`, the parent map `p : Fin m → Fin k` (fixed finite data) assigns
them to coarse cells with masses `C_i = ∑_{p j = i} W_j`, and observations are natural terms. In cleared form,
`C_i · (C f)_i` is the block sum `blk p W f i = ∑_{p j = i} W_j f_j`:

* `cond_total` (expectation): `∑_i blk f i = ∑_j W_j f_j`;
* `cond_defining` (the defining identity, `I(h C f) = I(h f)` for measurable `h = h' ∘ p`):
  `∑_j W_j h'(p j) f_j = ∑_i h'_i blk f i`;
* `cond_measurable` (`C x = x` for measurable `x = x' ∘ p`): `blk (x' ∘ p) i = C_i x'_i`;
* `cond_tower` (`C_n C_m = C_{min(n,m)}`, regrouping along a coarser map `q`):
  `blk_{q ∘ p} f c = ∑_{q i = c} blk_p f i`;
* `cond_contract` (the `d₁` contraction): `∑_i |blk f i − blk g i| ≤ ∑_j W_j |f_j − g_j|`.

Positivity is immediate for natural terms. Ring-level regrouping lemmas are transported by `deriveNat`.
-/

namespace LeanProofs.IPRA.Probability.ConditionalAveraging

open_ipra
open LeanProofs.IPRA.Foundations.ErrorBudget (nsum toG_nsum)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_add_le ad_mul ad_le_of)

variable {n k l m : ℕ} {Γ : List (Fm PTm n)}

/-! ## Regrouping in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

theorem regroup_total (p : Fin m → Fin k) (T : Fin m → R) :
    ∑ i, ∑ j, (if p j = i then T j else 0) = ∑ j, T j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]; simp

theorem regroup_defining (p : Fin m → Fin k) (H : Fin k → R) (T : Fin m → R) :
    ∑ j, H (p j) * T j = ∑ i, H i * ∑ j, (if p j = i then T j else 0) := by
  have : ∀ i, H i * ∑ j, (if p j = i then T j else 0) = ∑ j, (if p j = i then H i * T j else 0) :=
    fun i => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]; simp

theorem regroup_measurable (p : Fin m → Fin k) (W : Fin m → R) (C F : Fin k → R)
    (hm : ∀ i, ∑ j, (if p j = i then W j else 0) = C i) (i : Fin k) :
    ∑ j, (if p j = i then W j * F (p j) else 0) = C i * F i := by
  rw [← hm i, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> simp [h]

theorem regroup_tower (p : Fin m → Fin k) (q : Fin k → Fin l) (T : Fin m → R) (c : Fin l) :
    ∑ j, (if q (p j) = c then T j else 0) = ∑ i, (if q i = c then ∑ j, (if p j = i then T j else 0) else 0) := by
  have : ∀ i, (if q i = c then ∑ j, (if p j = i then T j else 0) else 0) =
      ∑ j, (if p j = i then (if q i = c then T j else 0) else 0) :=
    fun i => by split_ifs with h <;> simp [h]
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]; simp

end Ring

/-! ## Block sums -/

theorem toG_ite (c : Prop) [Decidable c] (a : PTm n) :
    Groth.ι (Q.mk Γ (if c then a else zero)) = if c then Groth.ι (Q.mk Γ a) else 0 := by
  split_ifs <;> simp [Q.mk_zero]

/-- The block sum `∑_{p j = i} W_j f_j`, the cleared conditional average `C_i (C f)_i`. -/
def blk (p : Fin m → Fin k) (W f : Fin m → PTm n) (i : Fin k) : PTm n :=
  nsum fun j => if p j = i then W j * f j else zero

/-- Expectation is preserved. -/
theorem cond_total (p : Fin m → Fin k) (W f : Fin m → PTm n) :
    Γ ⊢[PRAAx] (nsum fun i => blk p W f i) ≐ nsum fun j => W j * f j := by
  apply deriveNat
  simp only [blk, toG_nsum, toG_ite, Q.mk_mul, map_mul]
  exact regroup_total p _

/-- The defining identity `I(h C f) = I(h f)` for measurable `h = h' ∘ p`. -/
theorem cond_defining (p : Fin m → Fin k) (W f : Fin m → PTm n) (h : Fin k → PTm n) :
    Γ ⊢[PRAAx] (nsum fun j => h (p j) * (W j * f j)) ≐ nsum fun i => h i * blk p W f i := by
  apply deriveNat
  simp only [blk, toG_nsum, toG_ite, Q.mk_mul, map_mul]
  exact regroup_defining (R := Groth (Q Γ)) p (fun i => Groth.ι (Q.mk Γ (h i)))
    (fun j => Groth.ι (Q.mk Γ (W j)) * Groth.ι (Q.mk Γ (f j)))

/-- Measurable variables are fixed: `blk (x' ∘ p) i = C_i x'_i`. -/
theorem cond_measurable (p : Fin m → Fin k) (W : Fin m → PTm n) (C x : Fin k → PTm n)
    (hm : ∀ i, Γ ⊢[PRAAx] (nsum fun j => if p j = i then W j else zero) ≐ C i) (i : Fin k) :
    Γ ⊢[PRAAx] blk p W (fun j => x (p j)) i ≐ C i * x i := by
  have hm' : ∀ i, ∑ j, (if p j = i then Groth.ι (Q.mk Γ (W j)) else 0) = Groth.ι (Q.mk Γ (C i)) := by
    intro i
    have e := natEq (hm i)
    rw [toG_nsum] at e
    rw [← e]
    exact Finset.sum_congr rfl fun j _ => by rw [toG_ite]
  apply deriveNat
  simp only [blk, toG_nsum, toG_ite, Q.mk_mul, map_mul]
  exact regroup_measurable p _ _ (fun i => Groth.ι (Q.mk Γ (x i))) hm' i

/-- The tower law: averaging along `q ∘ p` regroups the block sums along `q`. -/
theorem cond_tower (p : Fin m → Fin k) (q : Fin k → Fin l) (W f : Fin m → PTm n) (c : Fin l) :
    Γ ⊢[PRAAx] blk (fun j => q (p j)) W f c ≐ nsum fun i => if q i = c then blk p W f i else zero := by
  apply deriveNat
  simp only [blk, toG_nsum, toG_ite, Q.mk_mul, map_mul]
  exact regroup_tower p q _ c

/-! ## The `d₁` contraction -/

theorem nsum_mono : {k : ℕ} → {a b : Fin k → PTm n} → (∀ j, Γ ⊢[PRAAx] le (a j) (b j)) →
    (Γ ⊢[PRAAx] le (nsum a) (nsum b))
  | 0, _, _, _ => by show Γ ⊢[PRAAx] le zero zero; ipra_le 0
  | _ + 1, a, b, h => by
    have h0 := h 0
    have hs := nsum_mono (a := fun i => a i.succ) (b := fun i => b i.succ) fun j => h j.succ
    show Γ ⊢[PRAAx] le (a 0 + nsum fun i => a i.succ) (b 0 + nsum fun i => b i.succ)
    ipra_le sl h0 + sl hs

/-- `|∑ F − ∑ G| ≤ ∑ |F − G|`. -/
theorem ad_nsum_le : {k : ℕ} → (F G : Fin k → PTm n) →
    (Γ ⊢[PRAAx] le (ad (nsum F) (nsum G)) (nsum fun j => ad (F j) (G j)))
  | 0, _, _ => by
    show Γ ⊢[PRAAx] le (ad zero zero) zero
    exact ad_le_of (by ipra_le 0) (by ipra_le 0)
  | _ + 1, F, G => by
    have h1 := ad_add_le (Γ := Γ) (F 0) (nsum fun i => F i.succ) (G 0) (nsum fun i => G i.succ)
    have h2 : Γ ⊢[PRAAx] le (ad (nsum fun i => F i.succ) (nsum fun i => G i.succ))
        (nsum fun j => ad (F j.succ) (G j.succ)) := ad_nsum_le (fun i => F i.succ) (fun i => G i.succ)
    show Γ ⊢[PRAAx] le (ad (F 0 + nsum fun i => F i.succ) (G 0 + nsum fun i => G i.succ))
      (ad (F 0) (G 0) + nsum fun i => ad (F i.succ) (G i.succ))
    ipra_le sl h1 + sl h2

/-- One block: `|blk f i − blk g i| ≤ ∑_{p j = i} W_j |f_j − g_j|`. -/
theorem blk_contract (p : Fin m → Fin k) (W f g : Fin m → PTm n) (i : Fin k) :
    Γ ⊢[PRAAx] le (ad (blk p W f i) (blk p W g i))
      (nsum fun j => if p j = i then W j * ad (f j) (g j) else zero) := by
  refine le_trans (ad_nsum_le _ _) (nsum_mono fun j => ?_)
  by_cases h : p j = i
  · simp only [h, ↓reduceIte]
    exact le_congr (.eqRefl _) (ad_mul _ _ _) (le_refl _)
  · simp only [h, ↓reduceIte]
    exact ad_le_of (by ipra_le 0) (by ipra_le 0)

/-- The `d₁` contraction: `∑_i |blk f i − blk g i| ≤ ∑_j W_j |f_j − g_j|`. -/
theorem cond_contract (p : Fin m → Fin k) (W f g : Fin m → PTm n) :
    Γ ⊢[PRAAx] le (nsum fun i => ad (blk p W f i) (blk p W g i)) (nsum fun j => W j * ad (f j) (g j)) := by
  have h₁ := nsum_mono (Γ := Γ) fun i => blk_contract p W f g i
  have h₂ : Γ ⊢[PRAAx] (nsum fun i => nsum fun j => if p j = i then W j * ad (f j) (g j) else zero) ≐
      nsum fun j => W j * ad (f j) (g j) := by
    apply deriveNat
    simp only [toG_nsum, toG_ite]
    exact regroup_total p _
  exact le_congr (.eqRefl _) h₂ h₁

end LeanProofs.IPRA.Probability.ConditionalAveraging
