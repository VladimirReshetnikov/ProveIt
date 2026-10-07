import OAI.Combinatorics.Progressions.Lattices.CenteredAffineCoefficient
import OAI.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}

def AffinePolynomialLiftProperties (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
    (center : ∀ j, J j → ℝ) (frame : Option K → V → ℝ) (T : K → ℝ)
    (Y : ∀ j, J j → MvPolynomial K ℝ) (β : ∀ j, J j → MvPolynomial K ℤ) : Prop :=
  (∀ j i, (Y j i).totalDegree ≤ j.val + 1) ∧
  (∀ j i, (β j i).totalDegree ≤ j.val + 1) ∧
  (∀ j i α, |(Y j i).coeff α| ≤ (1 / 4 : ℝ) / monomialScale T α) ∧
  (∀ j (x : K → ℝ), (∀ v, |x v| ≤ T v) → ∀ i, |MvPolynomial.eval x (Y j i)| < 1 / 2) ∧
  (∀ j i (x : K → ℝ),
    eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i - center j i =
      MvPolynomial.eval x (Y j i) + MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i)))

def HasAffinePolynomialLifts (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
    (center : ∀ j, J j → ℝ) (frame : Option K → V → ℝ) (T : K → ℝ) : Prop :=
  ∃ Y β, AffinePolynomialLiftProperties p center frame T Y β

theorem AffinePolynomialLiftProperties.integer_evaluation
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    {frame : Option K → V → ℤ} {T : K → ℝ}
    {Y : ∀ j, J j → MvPolynomial K ℝ} {β : ∀ j, J j → MvPolynomial K ℤ}
    (h : AffinePolynomialLiftProperties p center (fun k v => (frame k v : ℝ)) T Y β)
    (j : Fin m) (i : J j) (x : K → ℤ) :
    eval (fun v => (integerAffineMap (fun v k => frame (some k) v) (frame none) x v : ℝ)) (p j) i -
        center j i = MvPolynomial.eval (fun k => (x k : ℝ)) (Y j i) + (MvPolynomial.eval x (β j i) : ℝ) := by
  have he := h.2.2.2.2 j i (fun k => (x k : ℝ))
  have hcast : MvPolynomial.eval (fun k => (x k : ℝ))
      (MvPolynomial.map (Int.castRingHom ℝ) (β j i)) = (MvPolynomial.eval x (β j i) : ℝ) :=
    (MvPolynomial.map_eval (Int.castRingHom ℝ) x (β j i)).symm
  rw [hcast] at he
  simpa only [integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul] using he

theorem HasAffinePolynomialLifts.sitewise
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    {frame : Option K → V → ℤ} {T : K → ℝ}
    (h : HasAffinePolynomialLifts p center (fun k v => (frame k v : ℝ)) T)
    (y : ∀ j, (V → ℤ) → J j → ℝ) (z : ∀ j, (V → ℤ) → J j → ℤ)
    (E : Set (V → ℤ))
    (hframe : ∀ x : K → ℤ, (∀ k, |(x k : ℝ)| ≤ T k) →
      integerAffineMap (fun v k => frame (some k) v) (frame none) x ∈ E)
    (hy : ∀ j u, u ∈ E → ∀ i, |y j u i| < 1 / 2)
    (hsite : ∀ j u, u ∈ E → ∀ i,
      eval (fun v => (u v : ℝ)) (p j) i - center j i = y j u i + (z j u i : ℝ)) :
    ∃ Y β, AffinePolynomialLiftProperties p center (fun k v => (frame k v : ℝ)) T Y β ∧
      ∀ x : K → ℤ, (∀ k, |(x k : ℝ)| ≤ T k) → ∀ j,
        (fun i => MvPolynomial.eval (fun k => (x k : ℝ)) (Y j i)) =
          y j (integerAffineMap (fun v k => frame (some k) v) (frame none) x) ∧
        (fun i => MvPolynomial.eval x (β j i)) =
          z j (integerAffineMap (fun v k => frame (some k) v) (frame none) x) := by
  obtain ⟨Y, β, hYβ⟩ := h
  refine ⟨Y, β, hYβ, ?_⟩
  intro x hx j
  let u := integerAffineMap (fun v k => frame (some k) v) (frame none) x
  have hu : u ∈ E := hframe x hx
  have he (i : J j) := hYβ.integer_evaluation j i x
  have heq := small_coordinate_lift_unique
    (fun i => eval (fun v => (u v : ℝ)) (p j) i - center j i)
    (fun i => MvPolynomial.eval (fun k => (x k : ℝ)) (Y j i)) (y j u)
    (hYβ.2.2.2.1 j _ hx) (hy j u hu)
    (fun i => ⟨MvPolynomial.eval x (β j i), by linarith [he i]⟩)
    (fun i => ⟨z j u i, by linarith [hsite j u hu i]⟩)
  refine ⟨heq, ?_⟩
  funext i
  apply Int.cast_injective (α := ℝ)
  have hi := congrFun heq i
  linarith [he i, hsite j u hu i]

theorem HasAffinePolynomialLifts.sitewise_residue
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    {frame : Option K → V → ℤ} {T : K → ℝ}
    (h : HasAffinePolynomialLifts p center (fun k v => (frame k v : ℝ)) T)
    (y : ∀ j, (V → ℤ) → J j → ℝ) (z : ∀ j, (V → ℤ) → J j → ℤ)
    (E : Set (V → ℤ))
    (hframe : ∀ x : K → ℤ, (∀ k, |(x k : ℝ)| ≤ T k) →
      integerAffineMap (fun v k => frame (some k) v) (frame none) x ∈ E)
    (hy : ∀ j u, u ∈ E → ∀ i, |y j u i| < 1 / 2)
    (hsite : ∀ j u, u ∈ E → ∀ i,
      eval (fun v => (u v : ℝ)) (p j) i - center j i = y j u i + (z j u i : ℝ))
    (q : ℕ) (x x' : K → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ T k) (hx' : ∀ k, |(x' k : ℝ)| ≤ T k)
    (hmod : integerResidueMap K q x = integerResidueMap K q x') (j : Fin m) (i : J j) :
    (z j (integerAffineMap (fun v k => frame (some k) v) (frame none) x) i : ZMod q) =
      (z j (integerAffineMap (fun v k => frame (some k) v) (frame none) x') i : ZMod q) := by
  obtain ⟨Y, β, _, hvalues⟩ := h.sitewise y z E hframe hy hsite
  rw [← congrFun (hvalues x hx j).2 i, ← congrFun (hvalues x' hx' j).2 i]
  exact integerPolynomial_eval_congr (β j i) q hmod

end Erdos3.VectorPolynomial

end

end OAI
