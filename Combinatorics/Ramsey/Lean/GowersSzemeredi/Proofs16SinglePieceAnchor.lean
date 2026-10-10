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

variable {A : Type*} {N q : Nat}

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
  set C := anchorClass D cls p with hC
  let X := C.image fun p' => p'.2
  have hXcard : X.card = C.card := by
    apply Finset.card_image_of_injOn
    intro p' hp' p'' hp'' h
    have h1 := (Finset.mem_filter.mp hp').2.1
    have h2 := (Finset.mem_filter.mp hp'').2.1
    exact Prod.ext (h1.trans h2.symm) h
  have hmemX : ∀ x, x ∈ X ↔ (p.1, x) ∈ C := by
    intro x
    constructor
    · intro hx
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hx
      have h1 := (Finset.mem_filter.mp hp').2.1
      have : (p.1, p'.2) = p' := Prod.ext h1.symm rfl
      rw [this]; exact hp'
    · intro hx
      exact Finset.mem_image.mpr ⟨_, hx, rfl⟩
  have hXJ : X ⊆ J := by
    intro x hx
    exact (Finset.mem_product.mp (hD (Finset.mem_filter.mp ((hmemX x).mp hx)).1)).2
  have heq : ((J ×ˢ J).filter fun ab => ab.1 ≠ ab.2 ∧ (p.1, ab.1) ∈ C ∧ (p.1, ab.2) ∈ C) =
      (X ×ˢ X).filter fun ab => ab.1 ≠ ab.2 := by
    ext ab
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨-, hne, h1, h2⟩
      exact ⟨⟨(hmemX _).mpr h1, (hmemX _).mpr h2⟩, hne⟩
    · rintro ⟨⟨h1, h2⟩, hne⟩
      exact ⟨⟨hXJ h1, hXJ h2⟩, hne, (hmemX _).mp h1, (hmemX _).mp h2⟩
  rw [heq]
  have hsplit := Finset.card_filter_add_card_filter_not (s := X ×ˢ X) (fun ab => ab.1 ≠ ab.2)
  have hdiag : ((X ×ˢ X).filter fun ab => ¬ ab.1 ≠ ab.2).card = X.card := by
    refine Finset.card_bij (fun ab _ => ab.1) ?_ ?_ ?_
    · intro ab hab
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
    · intro ab hab ab' hab' h
      have e1 := not_not.mp (Finset.mem_filter.mp hab).2
      have e2 := not_not.mp (Finset.mem_filter.mp hab').2
      exact Prod.ext h (e1.symm.trans (h.trans e2))
    · intro x hx
      exact ⟨(x, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, by simp⟩, rfl⟩
  rw [Finset.card_product, hdiag, hXcard] at hsplit
  omega

/-- **One anchor pair captures a polynomial fraction.** -/
theorem exists_anchor_pair_capture (T : Finset A) (J : Finset (ZMod N))
    (D : Finset (A × ZMod N)) (hD : D ⊆ T ×ˢ J) (hDne : D.Nonempty)
    (cls : A × ZMod N → Fin q) :
    ∃ a ∈ J, ∃ b ∈ J, (D.card : Real) ^ 3 ≤ ((q : Real) * T.card) ^ 2 *
      ((J.card : Real) ^ 2 * (anchorCapture D cls a b).card + J.card * D.card) := by
  -- the class sizes
  let c : A × ZMod N → Real := fun p => ((anchorClass D cls p).card : Real)
  have hcJ : ∀ p, c p ≤ J.card := fun p => by
    show ((anchorClass D cls p).card : Real) ≤ J.card
    exact_mod_cast anchorClass_card_le D cls hD p
  -- keys of classes
  let keys := T ×ˢ (Finset.univ : Finset (Fin q))
  let κ : A × ZMod N → A × Fin q := fun p => (p.1, cls p)
  have hκ : ∀ p ∈ D, κ p ∈ keys := fun p hp =>
    Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hD hp)).1, Finset.mem_univ _⟩
  have hclass : ∀ p, anchorClass D cls p = D.filter fun p' => κ p' = κ p := by
    intro p
    ext p'
    simp only [anchorClass, Finset.mem_filter, κ, Prod.mk.injEq]
  -- Σ_p c_p = Σ_keys |fiber|², and Cauchy–Schwarz over keys
  let fib : A × Fin q → Real := fun k => ((D.filter fun p' => κ p' = k).card : Real)
  have hsum1 : ∑ p ∈ D, c p = ∑ k ∈ keys, fib k ^ 2 := by
    have h := Finset.sum_fiberwise_of_maps_to (s := D) (t := keys) (g := κ) hκ (f := c)
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∀ p ∈ D.filter (fun p' => κ p' = k), c p = fib k := by
      intro p hp
      simp only [c, fib, hclass p, (Finset.mem_filter.mp hp).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, sq]
  have hsumfib : ∑ k ∈ keys, fib k = D.card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := D) (t := keys) (f := κ) hκ
    simp only [fib]
    exact_mod_cast h.symm
  have hkeys : (keys.card : Real) = q * T.card := by
    simp only [keys, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast; ring
  have hcs1 := sq_sum_le_card_mul_sum_sq (s := keys) (f := fib)
  rw [hsumfib, hkeys] at hcs1
  -- Σ_p c_p² ≥ (Σ_p c_p)²/|D|
  have hcs2 := sq_sum_le_card_mul_sum_sq (s := D) (f := c)
  have hDpos : (0 : Real) < D.card := by exact_mod_cast hDne.card_pos
  have hS1 : (D.card : Real) ^ 2 ≤ ((q : Real) * T.card) * ∑ p ∈ D, c p := by
    rw [hsum1]; exact hcs1
  -- the double count over anchor pairs
  let pairs := J ×ˢ J
  have hdouble : ∑ ab ∈ pairs, ((anchorCapture D cls ab.1 ab.2).card : Real) =
      ∑ p ∈ D, (c p * c p - c p) := by
    have hnat : ∑ ab ∈ pairs, (anchorCapture D cls ab.1 ab.2).card =
        ∑ p ∈ D, ((pairs.filter fun ab => ab.1 ≠ ab.2 ∧ (p.1, ab.1) ∈ anchorClass D cls p ∧
          (p.1, ab.2) ∈ anchorClass D cls p).card) := by
      simp only [anchorCapture, Finset.card_filter]
      exact Finset.sum_comm
    have hc : ∀ p ∈ D, (((pairs.filter fun ab => ab.1 ≠ ab.2 ∧ (p.1, ab.1) ∈ anchorClass D cls p ∧
          (p.1, ab.2) ∈ anchorClass D cls p).card : Nat) : Real) = c p * c p - c p := by
      intro p _
      rw [anchor_pairs_card D cls hD p]
      have hle : (anchorClass D cls p).card ≤ (anchorClass D cls p).card *
          (anchorClass D cls p).card := Nat.le_mul_self _
      rw [Nat.cast_sub hle]
      push_cast; rfl
    rw [show (∑ ab ∈ pairs, ((anchorCapture D cls ab.1 ab.2).card : Real)) =
        ((∑ ab ∈ pairs, (anchorCapture D cls ab.1 ab.2).card : Nat) : Real) by push_cast; rfl,
      hnat]
    push_cast
    exact Finset.sum_congr rfl hc
  -- choose the best pair
  have hJne : J.Nonempty := by
    obtain ⟨p, hp⟩ := hDne
    exact ⟨p.2, (Finset.mem_product.mp (hD hp)).2⟩
  have hpairsne : pairs.Nonempty := hJne.product hJne
  obtain ⟨ab, hab, hmax⟩ := Finset.exists_max_image pairs
    (fun ab => ((anchorCapture D cls ab.1 ab.2).card : Real)) hpairsne
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  refine ⟨ab.1, ha, ab.2, hb, ?_⟩
  have hpairscard : (pairs.card : Real) = (J.card : Real) ^ 2 := by
    simp only [pairs, Finset.card_product]; push_cast; ring
  have havg : ∑ p ∈ D, (c p * c p - c p) ≤
      (J.card : Real) ^ 2 * (anchorCapture D cls ab.1 ab.2).card := by
    rw [← hdouble, ← hpairscard]
    calc ∑ ab' ∈ pairs, ((anchorCapture D cls ab'.1 ab'.2).card : Real)
        ≤ ∑ _ab' ∈ pairs, ((anchorCapture D cls ab.1 ab.2).card : Real) :=
          Finset.sum_le_sum fun ab' h => hmax ab' h
      _ = (pairs.card : Real) * (anchorCapture D cls ab.1 ab.2).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hlin : ∑ p ∈ D, c p ≤ (J.card : Real) * D.card := by
    calc ∑ p ∈ D, c p ≤ ∑ _p ∈ D, (J.card : Real) := Finset.sum_le_sum fun p _ => hcJ p
      _ = (J.card : Real) * D.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsq : ∑ p ∈ D, c p * c p = ∑ p ∈ D, c p ^ 2 := by
    refine Finset.sum_congr rfl fun p _ => ?_; ring
  have hsub : ∑ p ∈ D, (c p * c p - c p) = ∑ p ∈ D, c p ^ 2 - ∑ p ∈ D, c p := by
    rw [Finset.sum_sub_distrib, hsq]
  -- combine: |D|⁴ ≤ n²(Σc)² ≤ n²·|D|·Σc²
  set n := (q : Real) * T.card with hn
  have hn0 : 0 ≤ n := by positivity
  have hS0 : 0 ≤ ∑ p ∈ D, c p := Finset.sum_nonneg fun p _ => Nat.cast_nonneg _
  have h4 : (D.card : Real) ^ 4 ≤ n ^ 2 * ((D.card : Real) * ∑ p ∈ D, c p ^ 2) := by
    have e1 : ((D.card : Real) ^ 2) ^ 2 ≤ (n * ∑ p ∈ D, c p) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hS1 2
    calc (D.card : Real) ^ 4 = ((D.card : Real) ^ 2) ^ 2 := by ring
      _ ≤ (n * ∑ p ∈ D, c p) ^ 2 := e1
      _ = n ^ 2 * (∑ p ∈ D, c p) ^ 2 := by ring
      _ ≤ n ^ 2 * ((D.card : Real) * ∑ p ∈ D, c p ^ 2) :=
          mul_le_mul_of_nonneg_left hcs2 (by positivity)
  have h3 : (D.card : Real) ^ 3 ≤ n ^ 2 * ∑ p ∈ D, c p ^ 2 := by
    have : (D.card : Real) * (D.card : Real) ^ 3 ≤ (D.card : Real) * (n ^ 2 * ∑ p ∈ D, c p ^ 2) := by
      nlinarith [h4]
    exact le_of_mul_le_mul_left this hDpos
  have hfinal : ∑ p ∈ D, c p ^ 2 ≤ (J.card : Real) ^ 2 * (anchorCapture D cls ab.1 ab.2).card +
      J.card * D.card := by
    linarith [havg, hsub, hlin]
  calc (D.card : Real) ^ 3 ≤ n ^ 2 * ∑ p ∈ D, c p ^ 2 := h3
    _ ≤ n ^ 2 * ((J.card : Real) ^ 2 * (anchorCapture D cls ab.1 ab.2).card + J.card * D.card) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)

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
