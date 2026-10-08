import GowersSzemeredi.Proofs16FreimanBilinearReadout

/-! Bilinear Bohr varieties and the pre-extension form of Milićević's theorem.

Milićević (arXiv:2601.01682, Theorem 1.6 and the proof overview of
Theorem 1.4) works with **bilinear Bohr varieties**
`{(x, y) ∈ B(Γ;ρ) × B(Ψ;ρ) : x ∈ B(L₁(y), …, L_r(y); ρ)}`, where the `L_i`
are Freiman-linear maps on `B(Ψ;ρ)`. His proof produces a Freiman
bihomomorphism on such a variety and only afterwards *extends* it, with
controlled errors, to the `E`-bihomomorphism on a product of Bohr sets that
Theorem 1.4 states.

For the readout (R) of research notes J.2, the pre-extension object is
what is needed. This module provides:

* `bilinearBohrVariety Γ Ψ L ρ` over `ZMod N`;
* `MilicevicVarietyStructure D`, the pre-extension statement with bounds
  `milicevicBound D c`, as a hypothesis (not asserted);
* `freiman_on_variety_biaffine`: on any product of progressions satisfying
  the variety's conditions, a Freiman bihomomorphism on the variety is
  bi-affine.

The variety conditions on a product box say that the `r` bilinear-type
quantities `L_i(y) · x` are simultaneously small. Producing such boxes is
item (D). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The bilinear Bohr variety `{(x, y) ∈ B(Γ;ρ) × B(Ψ;ρ) : x ∈ B({L_i y};ρ)}`. -/
def bilinearBohrVariety {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) (ρ : Real) : Finset (ZMod N × ZMod N) :=
  (bohr Γ ρ ×ˢ bohr Ψ ρ).filter fun p =>
    p.1 ∈ bohr (Finset.univ.image fun i => L i p.2) ρ

/-- `L` is Freiman-linear on `B`: it respects additive quadruples in `B`. -/
def IsFreimanLinearOn {N : Nat} (B : Finset (ZMod N)) (L : ZMod N → ZMod N) : Prop :=
  ∀ y₁ y₂ y₃ y₄, y₁ ∈ B → y₂ ∈ B → y₃ ∈ B → y₄ ∈ B → y₁ + y₂ = y₃ + y₄ →
    L y₁ + L y₂ = L y₃ + L y₄

/-- **Milićević's structure, pre-extension form.** A Freiman bihomomorphism
on a density-`c` set agrees, after shifts, with a Freiman bihomomorphism on
a bilinear Bohr variety of codimension and inverse radius at most
`milicevicBound D c`, on at least `exp(−milicevicBound D c) N²` points.
Stated as a hypothesis for the dimension-three route; not asserted. -/
def MilicevicVarietyStructure (D : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (A : Finset (ZMod N × ZMod N))
    (φ : ZMod N × ZMod N → ZMod N) (c : Real),
    0 < c → c * (N : Real) ^ 2 ≤ A.card → IsEBihomomorphism A φ {0} →
    ∃ (Γ Ψ : Finset (ZMod N)) (r : Nat) (L : Fin r → ZMod N → ZMod N) (ρ : Real)
      (s t : ZMod N) (Φ : ZMod N × ZMod N → ZMod N),
      (Γ.card : Real) ≤ milicevicBound D c ∧ (Ψ.card : Real) ≤ milicevicBound D c ∧
      (r : Real) ≤ milicevicBound D c ∧ Real.exp (-milicevicBound D c) ≤ ρ ∧
      (∀ i, IsFreimanLinearOn (bohr Ψ ρ) (L i)) ∧
      IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0} ∧
      Real.exp (-milicevicBound D c) * (N : Real) ^ 2 ≤
        (((bilinearBohrVariety Γ Ψ L ρ).filter fun p =>
          (p.1 + s, p.2 + t) ∈ A ∧ Φ p = φ (p.1 + s, p.2 + t)).card : Real)

/-- A product of progressions satisfying the variety's three conditions lies
in the variety. -/
theorem product_mem_bilinearBohrVariety {N : Nat} [NeZero N] {Γ Ψ : Finset (ZMod N)} {r : Nat}
    {L : Fin r → ZMod N → ZMod N} {ρ : Real} {x y : ZMod N}
    (hx : x ∈ bohr Γ ρ) (hy : y ∈ bohr Ψ ρ)
    (hsmall : ∀ i, (centeredAbs (L i y * x) : Real) ≤ ρ * N) :
    (x, y) ∈ bilinearBohrVariety Γ Ψ L ρ := by
  unfold bilinearBohrVariety
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
  unfold bohr
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro z hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  exact hsmall i

/-- **Readout on the variety.** If a product of progressions satisfies the
variety's conditions (Bohr membership in each coordinate, and every
`L_i(y) · x` small), then a Freiman bihomomorphism on the variety is
bi-affine on it. -/
theorem freiman_on_variety_biaffine {N : Nat} [NeZero N] {Γ Ψ : Finset (ZMod N)} {r : Nat}
    {L : Fin r → ZMod N → ZMod N} {ρ : Real} {Φ : ZMod N × ZMod N → ZMod N}
    (hΦ : IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0})
    (a d b e : ZMod N) (L₁ L₂ : Nat) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hx : ∀ i, i < L₁ → a + (i : ZMod N) * d ∈ bohr Γ ρ)
    (hy : ∀ j, j < L₂ → b + (j : ZMod N) * e ∈ bohr Ψ ρ)
    (hsmall : ∀ i j, i < L₁ → j < L₂ → ∀ k,
      (centeredAbs (L k (b + (j : ZMod N) * e) * (a + (i : ZMod N) * d)) : Real) ≤ ρ * N) :
    let f : Nat → Nat → ZMod N := fun i j => Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e)
    ∀ i j, i < L₁ → j < L₂ →
      f i j = f 0 0 + i • (f 1 0 - f 0 0) + j • (f 0 1 - f 0 0) +
        (i * j) • (f 1 1 - f 1 0 - f 0 1 + f 0 0) :=
  freiman_bihom_biaffine_on_product hΦ a d b e L₁ L₂ hL₁ hL₂
    (fun i j hi hj => product_mem_bilinearBohrVariety (hx i hi) (hy j hj) (hsmall i j hi hj))

end LeanProofs.GowersSzemeredi
