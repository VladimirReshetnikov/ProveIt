import GowersSzemeredi.Definitions
import Mathlib.Algebra.Order.Chebyshev

/-! The anchor step of a **single-piece** Lemma 16.10 (Notes Part L:
the direct trilinear attack).

Gowers's printed lift covers *all* of `φ₁`. It samples `r = ⌈qσ⁻²⌉` anchors
and takes the union over all `r²` anchor pairs. That union drives the
exponent `p = 4r²γ⁻²s` and the failing comparison
`q(σ/p, γ, k+1)^p ≤ q(ρ, γ, k+1)`. One dense piece needs only **one** anchor
pair.

Let `D ⊆ T × J`. Give each point a class label in `Fin q`; for fixed `h`, the
points `(h, x)` with a given label form one class.
* `exists_anchor_pair_capture`: some anchors `a, b ∈ J` with `a ≠ b` capture
  the set `W` of points whose class contains both `(h, a)` and `(h, b)`, and
  `|D|³ ≤ (q|T|)²·(|J|²·|W| + |J|·|D|)`. The loss is polynomial in `1/q`
  and the density, from two Cauchy–Schwarz steps over the class sizes and
  an average over anchor pairs.
* `anchor_reconstruction`: if `φ(h, ·)` is affine on each class (Lemma 16.9's
  line cover), then on `W`
  `φ(h, x) = φ(h, a) + (φ(h, a) − φ(h, b))·(a − b)⁻¹·(x − a)`.
  So on the captured set, `φ` is determined by its two cross-sections at
  `x = a` and `x = b`. With one multilinear graph for each cross-section,
  this is one `(k+1)`-multilinear piece. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

variable {A : Type*} [DecidableEq A] {N q : Nat}

/-- The class of a point: same first coordinate, same label. -/
def anchorClass (D : Finset (A × ZMod N)) (cls : A × ZMod N → Fin q) (p : A × ZMod N) :
    Finset (A × ZMod N) :=
  D.filter fun p' => p'.1 = p.1 ∧ cls p' = cls p

/-- The points captured by the anchors `a` and `b`. -/
def anchorCapture (D : Finset (A × ZMod N)) (cls : A × ZMod N → Fin q) (a b : ZMod N) :
    Finset (A × ZMod N) :=
  D.filter fun p => a ≠ b ∧ (p.1, a) ∈ anchorClass D cls p ∧ (p.1, b) ∈ anchorClass D cls p

theorem anchorClass_card_le (D : Finset (A × ZMod N)) (cls : A × ZMod N → Fin q)
    {J : Finset (ZMod N)} {T : Finset A} (hD : D ⊆ T ×ˢ J) (p : A × ZMod N) :
    (anchorClass D cls p).card ≤ J.card := by
  refine Finset.card_le_card_of_injOn (fun p' => p'.2) ?_ ?_
  · intro p' hp'
    exact (Finset.mem_product.mp (hD (Finset.mem_filter.mp hp').1)).2
  · intro p' hp' p'' hp'' h
    have h1 := (Finset.mem_filter.mp hp').2.1
    have h2 := (Finset.mem_filter.mp hp'').2.1
    exact Prod.ext (h1.trans h2.symm) h

/-- The anchor pairs that capture a fixed point number `c(c − 1)`. -/
theorem anchor_pairs_card (D : Finset (A × ZMod N)) (cls : A × ZMod N → Fin q)
    {J : Finset (ZMod N)} {T : Finset A} (hD : D ⊆ T ×ˢ J) (p : A × ZMod N) :
    ((J ×ˢ J).filter fun ab => ab.1 ≠ ab.2 ∧ (p.1, ab.1) ∈ anchorClass D cls p ∧
        (p.1, ab.2) ∈ anchorClass D cls p).card =
      (anchorClass D cls p).card * (anchorClass D cls p).card - (anchorClass D cls p).card := by
  -- the second coordinates `X` of the class: the pairs are the off-diagonal of `X`
  set C := anchorClass D cls p
  have hfst : ∀ p' ∈ C, p'.1 = p.1 := fun p' hp' => (Finset.mem_filter.mp hp').2.1
  have hJ : ∀ x, (p.1, x) ∈ C → x ∈ J := fun x hx =>
    (Finset.mem_product.mp (hD (Finset.mem_filter.mp hx).1)).2
  have hX : ∀ x, x ∈ C.image Prod.snd ↔ (p.1, x) ∈ C := fun x =>
    ⟨fun hx => by obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hx; rwa [← hfst p' hp'],
      fun hx => Finset.mem_image.mpr ⟨_, hx, rfl⟩⟩
  rw [← Finset.card_image_of_injOn (f := Prod.snd) (s := C) fun p' hp' p'' hp'' h =>
    Prod.ext ((hfst p' hp').trans (hfst p'' hp'').symm) h, ← Finset.offDiag_card]
  congr 1
  ext ab
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag, hX]
  exact ⟨fun h => ⟨h.2.2.1, h.2.2.2, h.2.1⟩, fun h => ⟨⟨hJ _ h.1, hJ _ h.2.1⟩, h.2.2, h.1, h.2.1⟩⟩

/-- **One anchor pair captures a polynomial fraction.** -/
theorem exists_anchor_pair_capture (T : Finset A) (J : Finset (ZMod N))
    (D : Finset (A × ZMod N)) (hD : D ⊆ T ×ˢ J) (hDne : D.Nonempty)
    (cls : A × ZMod N → Fin q) :
    ∃ a ∈ J, ∃ b ∈ J, (D.card : Real) ^ 3 ≤ ((q : Real) * T.card) ^ 2 *
      ((J.card : Real) ^ 2 * (anchorCapture D cls a b).card + J.card * D.card) := by
  -- the classes are the fibres of `κ p = (p.1, cls p)` over the `q|T|` keys
  let κ : A × ZMod N → A × Fin q := fun p => (p.1, cls p)
  have hκ : ∀ p ∈ D, κ p ∈ T ×ˢ (Finset.univ : Finset (Fin q)) := fun p hp =>
    Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hD hp)).1, Finset.mem_univ _⟩
  have hS1 : ∑ p ∈ D, (anchorClass D cls p).card =
      ∑ k ∈ T ×ˢ (Finset.univ : Finset (Fin q)), (D.filter fun p => κ p = k).card ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hκ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq]
    refine Finset.sum_const_nat fun p hp => ?_
    rw [← (Finset.mem_filter.mp hp).2]
    congr 1
    ext p'
    simp only [anchorClass, Finset.mem_filter, κ, Prod.mk.injEq]
  -- Cauchy–Schwarz over the keys, then over `D`
  have hcs1 := sq_sum_le_card_mul_sum_sq (s := T ×ˢ (Finset.univ : Finset (Fin q)))
    (f := fun k => (D.filter fun p => κ p = k).card)
  rw [← Finset.card_eq_sum_card_fiberwise (s := D) hκ, ← hS1, Finset.card_product,
    Finset.card_univ, Fintype.card_fin] at hcs1
  have hcs2 := sq_sum_le_card_mul_sum_sq (s := D) (f := fun p => (anchorClass D cls p).card)
  -- the double count over anchor pairs
  have hS2 : ∑ p ∈ D, (anchorClass D cls p).card ^ 2 ≤ ∑ ab ∈ J ×ˢ J,
      (anchorCapture D cls ab.1 ab.2).card + ∑ p ∈ D, (anchorClass D cls p).card := by
    have h : ∑ ab ∈ J ×ˢ J, (anchorCapture D cls ab.1 ab.2).card =
        ∑ p ∈ D, ((J ×ˢ J).filter fun ab => ab.1 ≠ ab.2 ∧ (p.1, ab.1) ∈ anchorClass D cls p ∧
          (p.1, ab.2) ∈ anchorClass D cls p).card := by
      simp only [anchorCapture, Finset.card_filter]
      exact Finset.sum_comm
    rw [h, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => by rw [anchor_pairs_card D cls hD p, sq]; exact le_tsub_add
  -- the best pair
  have hJne : J.Nonempty := (hDne.mono hD).snd
  obtain ⟨ab, hab, hmax⟩ := Finset.exists_max_image (J ×ˢ J)
    (fun ab => (anchorCapture D cls ab.1 ab.2).card) (hJne.product hJne)
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  refine ⟨ab.1, ha, ab.2, hb, ?_⟩
  have hK := Finset.sum_le_card_nsmul (J ×ˢ J) (fun ab => (anchorCapture D cls ab.1 ab.2).card)
    (anchorCapture D cls ab.1 ab.2).card hmax
  have hlin := Finset.sum_le_card_nsmul D (fun p => (anchorClass D cls p).card) J.card
    fun p _ => anchorClass_card_le D cls hD p
  simp only [Finset.card_product, smul_eq_mul] at hK hlin
  -- combine, with `c_p = |class of p|`: `|D|⁴ ≤ (q|T|)²(Σ c_p)² ≤ (q|T|)²·|D|·Σ c_p²`
  have h3 : D.card ^ 3 ≤ (q * T.card) ^ 2 * ∑ p ∈ D, (anchorClass D cls p).card ^ 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ hDne.card_pos
    linarith [Nat.mul_le_mul hcs1 hcs1, Nat.mul_le_mul_left ((q * T.card) ^ 2) hcs2]
  have h : D.card ^ 3 ≤ (q * T.card) ^ 2 *
      (J.card ^ 2 * (anchorCapture D cls ab.1 ab.2).card + J.card * D.card) :=
    h3.trans (Nat.mul_le_mul_left _ (by linarith))
  exact_mod_cast h

/-- **Reconstruction on the captured set.** -/
theorem anchor_reconstruction [Fact N.Prime] (D : Finset (A × ZMod N))
    (cls : A × ZMod N → Fin q) (φ : A × ZMod N → ZMod N)
    (ell : A → Fin q → ZMod N → ZMod N) (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hφ : ∀ p ∈ D, φ p = ell p.1 (cls p) p.2) {a b : ZMod N} {p : A × ZMod N}
    (hp : p ∈ anchorCapture D cls a b) :
    φ p = φ (p.1, a) + (φ (p.1, a) - φ (p.1, b)) * (a - b)⁻¹ * (p.2 - a) := by
  obtain ⟨hpD, hne, ha, hb⟩ := Finset.mem_filter.mp hp
  obtain ⟨haD, -, hacls⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbD, -, hbcls⟩ := Finset.mem_filter.mp hb
  obtain ⟨s, t, hst⟩ := hell p.1 (cls p)
  have e0 : φ p = s * p.2 + t := by rw [hφ p hpD]; exact hst _ (Finset.mem_univ _)
  have ea : φ (p.1, a) = s * a + t := by
    rw [hφ _ haD, show cls (p.1, a) = cls p from hacls]; exact hst _ (Finset.mem_univ _)
  have eb : φ (p.1, b) = s * b + t := by
    rw [hφ _ hbD, show cls (p.1, b) = cls p from hbcls]; exact hst _ (Finset.mem_univ _)
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  rw [e0, ea, eb]
  field_simp
  ring

end LeanProofs.GowersSzemeredi
