import GowersSzemeredi.Proofs16PropNineThreeGoodPairs
import GowersSzemeredi.Proofs16RepeatedQuadrupleCounts

/-! **Milićević's Proposition 9.3 in `ℤ/N`** (arXiv:2601.01682, printed
pp. 65–68), assembled as recorded in J.5c.

**Input.** A system of column maps `L x : ZMod N → ZMod N`, each
Freiman-linear on `B(T x; r)` with `L x 0 = 0` and `|T x| ≤ d`. At most
`ε₁N³` quadruples `(x+a, x, z+a, z)` are incompatible
(`incompatibleTriples (colComp T L r)`), and at most `ε₂N¹¹` 12-tuples
have an unrespected x- or y-side 8-tuple.

**Output** (`milicevic_prop_9_3`).
* Freiman 8-homomorphisms `θ_i` on domains `D_i`, and a window `J` of
  `8s₀` indices.
* A set `X` of `a`'s and chosen pairs `c(a) = (x_a, y_a)`. The glued map
  `ψ_a = chosenGlued T L r c a` is normalized and Freiman-linear on
  `U_a = B(θ_i(a) : i ∈ J; η)`.
* `ψ_a` relates back: `x_a` is compatible with at least `N/2` columns `z`,
  and `ψ_a = φ_{z+a} − φ_z` on the common quarter Bohr set for each of them.
* `a ∈ D_i` for the indices `i` actually used by `a`.
* At least
  `[((1 − 2η′)³ − 2η′ − 16(ε + 2ε₂))N³ − 6N²] / C(m + 8s₀, 8s₀)`
  additive quadruples in `X` are respected by `ψ` on `⋂_j U_{a_j}`, where
  `η′ = 5ε₁ + ε`.
* `m` is bounded by the iteration's potential.

The chain: iteration; good pairs and the Markov set `A′`; the pair choice
F3 with `Bad = Bad12 ∪` unrespected 8-tuples; the window chosen for
quadruples; then Lemmas A and B. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Compatibility of `(x + a, x)` with `(z + a, z)`. -/
def colComp {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (x z a : ZMod N) : Prop :=
  ColumnPairCompatible T L r (colPair x a) (colPair z a)

/-- Our additive quadruples have at most `6N²` repeated-index members. -/
theorem additiveQuadruplesIn_repeated_card_le {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    ((additiveQuadruplesIn A).filter fun q => ¬ Function.Injective q).card ≤ 6 * N ^ 2 := by
  let e : (Fin 4 → ZMod N) → (Fin 4 → ZMod N) := fun q => ![q 0, q 2, q 1, q 3]
  have he : Function.Injective e := by
    intro q q' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    funext j
    fin_cases j
    · exact h0
    · exact h2
    · exact h1
    · exact h3
  let Q' := (additiveQuadruplesIn A).image e
  have hQ' : ∀ q ∈ Q', q 0 - q 1 + q 2 - q 3 = 0 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have := (Finset.mem_filter.mp hp).2.1
    show p 0 - p 2 + p 1 - p 3 = 0
    linear_combination this
  let σ : Fin 4 → Fin 4 := ![0, 2, 1, 3]
  have hσ : Function.Injective σ := by decide
  have heq : ∀ q : Fin 4 → ZMod N, e q = q ∘ σ := fun q => by
    funext j; fin_cases j <;> rfl
  have hinv : ∀ q : Fin 4 → ZMod N, q = (q ∘ σ) ∘ σ := fun q => by
    funext j; fin_cases j <;> rfl
  have hinjiff : ∀ q, Function.Injective (e q) ↔ Function.Injective q := by
    intro q
    rw [heq]
    constructor
    · intro h
      rw [hinv q]
      exact h.comp hσ
    · intro h
      exact h.comp hσ
  have hcard : ((additiveQuadruplesIn A).filter fun q => ¬ Function.Injective q).card =
      (Q'.filter fun q => ¬ Function.Injective q).card := by
    rw [Finset.filter_image]
    refine (Finset.card_image_of_injective _ he).symm.trans ?_
    congr 1
    ext q
    simp only [Finset.mem_filter, Function.comp, hinjiff]
  rw [hcard]
  exact repeated_additive_quadruples_card_le Q' hQ'

end LeanProofs.GowersSzemeredi
