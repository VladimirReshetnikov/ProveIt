import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {R B : Type*} [CommRing R]

theorem polynomialTranslate_comp_ring (h k : B → R) (P : MvPolynomial B R) :
    polynomialTranslate h (polynomialTranslate k P) = polynomialTranslate (h + k) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, polynomialTranslate_X, map_add, polynomialTranslate_C, Pi.add_apply]
    rw [add_assoc]

@[simp] theorem polynomialTranslate_zero_ring (P : MvPolynomial B R) :
    polynomialTranslate (0 : B → R) P = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp]

@[ext] structure PolynomialTranslationGroupOver (R B : Type*) [CommRing R] where
  base : B → R
  polynomial : MvPolynomial B R

namespace PolynomialTranslationGroupOver

noncomputable instance : Mul (PolynomialTranslationGroupOver R B) where
  mul a b := ⟨a.base + b.base, polynomialTranslate (-b.base) a.polynomial + b.polynomial⟩

noncomputable instance : One (PolynomialTranslationGroupOver R B) where
  one := ⟨0, 0⟩

noncomputable instance : Inv (PolynomialTranslationGroupOver R B) where
  inv a := ⟨-a.base, -polynomialTranslate a.base a.polynomial⟩

@[simp] theorem base_mul (a b : PolynomialTranslationGroupOver R B) :
    (a * b).base = a.base + b.base := rfl

@[simp] theorem polynomial_mul (a b : PolynomialTranslationGroupOver R B) :
    (a * b).polynomial = polynomialTranslate (-b.base) a.polynomial + b.polynomial := rfl

@[simp] theorem base_one : (1 : PolynomialTranslationGroupOver R B).base = 0 := rfl
@[simp] theorem polynomial_one : (1 : PolynomialTranslationGroupOver R B).polynomial = 0 := rfl
@[simp] theorem base_inv (a : PolynomialTranslationGroupOver R B) : (a⁻¹).base = -a.base := rfl
@[simp] theorem polynomial_inv (a : PolynomialTranslationGroupOver R B) :
    (a⁻¹).polynomial = -polynomialTranslate a.base a.polynomial := rfl

noncomputable instance : Group (PolynomialTranslationGroupOver R B) :=
  Group.ofLeftAxioms
    (by
      intro a b c
      apply PolynomialTranslationGroupOver.ext
      · exact add_assoc _ _ _
      · simp only [polynomial_mul, base_mul, map_add, polynomialTranslate_comp_ring,
          neg_add_rev, add_assoc])
    (by intro a; apply PolynomialTranslationGroupOver.ext <;> simp)
    (by
      intro a
      apply PolynomialTranslationGroupOver.ext
      · simp
      · simp [polynomialTranslate_comp_ring])

theorem algebraic_major_identity (D D₀ V : MvPolynomial B R) (A : B → R)
    (left middle right : PolynomialTranslationGroupOver R B)
    (hfactor : (⟨A, D - polynomialTranslate (-A) D₀⟩ : PolynomialTranslationGroupOver R B) =
      left * middle * right)
    (hpotential : middle.polynomial = V - polynomialTranslate (-middle.base) V) :
    A = left.base + middle.base + right.base ∧
      D = polynomialTranslate (-A) D₀ +
        polynomialTranslate (-A + left.base) left.polynomial -
        polynomialTranslate (-A + left.base) V + right.polynomial +
        polynomialTranslate (-right.base) V := by
  have hbase : A = left.base + middle.base + right.base := congrArg base hfactor
  have hpoly := congrArg polynomial hfactor
  change D - polynomialTranslate (-A) D₀ =
    polynomialTranslate (-right.base)
      (polynomialTranslate (-middle.base) left.polynomial + middle.polynomial) +
        right.polynomial at hpoly
  rw [hpotential, map_add, map_sub, polynomialTranslate_comp_ring,
    polynomialTranslate_comp_ring] at hpoly
  have hshift : -right.base + -middle.base = -A + left.base := by
    rw [hbase]
    abel
  rw [hshift] at hpoly
  refine ⟨hbase, ?_⟩
  calc
    D = (D - polynomialTranslate (-A) D₀) + polynomialTranslate (-A) D₀ := by abel
    _ = _ := by rw [hpoly]; abel

theorem algebraic_major_decomposition (D D₀ V : MvPolynomial B R) (A : B → R)
    (left middle right : PolynomialTranslationGroupOver R B)
    (hfactor : (⟨A, D - polynomialTranslate (-A) D₀⟩ : PolynomialTranslationGroupOver R B) =
      left * middle * right)
    (hpotential : middle.polynomial = V - polynomialTranslate (-middle.base) V) :
    D = polynomialTranslate (-A)
      (D₀ + polynomialTranslate left.base left.polynomial - polynomialTranslate left.base V) +
        (right.polynomial + polynomialTranslate (-right.base) V) := by
  rw [(algebraic_major_identity D D₀ V A left middle right hfactor hpotential).2]
  simp only [map_sub, map_add, polynomialTranslate_comp_ring]
  abel

end PolynomialTranslationGroupOver

theorem PolynomialTranslationGroup.algebraic_major_identity
    (D D₀ V : MvPolynomial B ℚ) (A : B → ℚ)
    (left middle right : PolynomialTranslationGroup B)
    (hfactor : (⟨A, D - polynomialTranslate (-A) D₀⟩ : PolynomialTranslationGroup B) =
      left * middle * right)
    (hpotential : middle ∈ PolynomialTranslationGroup.potentialSubgroup V) :
    A = left.base + middle.base + right.base ∧
      D = polynomialTranslate (-A) D₀ +
        polynomialTranslate (-A + left.base) left.polynomial -
        polynomialTranslate (-A + left.base) V + right.polynomial +
        polynomialTranslate (-right.base) V := by
  let convert : PolynomialTranslationGroup B → PolynomialTranslationGroupOver ℚ B :=
    fun g => ⟨g.base, g.polynomial⟩
  exact PolynomialTranslationGroupOver.algebraic_major_identity D D₀ V A
    (convert left) (convert middle) (convert right) (congrArg convert hfactor)
    ((PolynomialTranslationGroup.mem_potentialSubgroup V middle).mp hpotential)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B R T : Type*} [CommRing R] [CommRing T]

noncomputable def specializeMajorParameters (φ : R →+* T)
    (P : MvPolynomial (U ⊕ B) R) (u : U → T) : MvPolynomial B T :=
  eval₂Hom (C.comp φ) (Sum.elim (fun i => C (u i)) X) P

theorem specializeMajorParameters_eval (φ : R →+* T)
    (P : MvPolynomial (U ⊕ B) R) (u : U → T) (b : B → T) :
    eval b (specializeMajorParameters φ P u) = eval₂ φ (Sum.elim u b) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [specializeMajorParameters]
  | add p q hp hq => simpa only [specializeMajorParameters, map_add, eval₂_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    simp only [specializeMajorParameters, coe_eval₂Hom] at hp
    cases i <;> simp [specializeMajorParameters, hp]

theorem polynomialTranslate_eval_ring (h : B → R) (P : MvPolynomial B R) (b : B → R) :
    eval b (polynomialTranslate h P) = eval (fun i => b i + h i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, polynomialTranslate_X, map_add, eval_X, eval_C]

noncomputable def normalizedMajorLeft (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (H u : U → ℝ) : PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval (fun i => u i / H i) (e j),
    specializeMajorParameters (RingHom.id ℝ) E (fun i => u i / H i)⟩

noncomputable def rationalMajorRight (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (u : U → ℝ) : PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval₂ (algebraMap ℚ ℝ) u (a j),
    specializeMajorParameters (algebraMap ℚ ℝ) Q u⟩

noncomputable def algebraicMajorSymbol (D : MvPolynomial (U ⊕ B) ℝ)
    (D₀ : MvPolynomial B ℝ) (A : B → MvPolynomial U ℝ) (u : U → ℝ) :
    PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval u (A j), specializeMajorParameters (RingHom.id ℝ) D u -
    polynomialTranslate (fun j => -eval u (A j)) D₀⟩

theorem algebraic_major_normalized_identity
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (V : MvPolynomial B ℚ) (H : U → ℝ)
    (middle : (U → ℝ) → PolynomialTranslationGroupOver ℝ B)
    (hfactor : ∀ u, algebraicMajorSymbol D D₀ A u =
      normalizedMajorLeft E e H u * middle u * rationalMajorRight Q a u)
    (hpotential : ∀ u, (middle u).polynomial = map (algebraMap ℚ ℝ) V -
      polynomialTranslate (-(middle u).base) (map (algebraMap ℚ ℝ) V))
    (u : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim u b) D =
      eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j)))
        (majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e) +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (majorRationalPolynomial Q V a) := by
  have hpoly := (PolynomialTranslationGroupOver.algebraic_major_identity
    (specializeMajorParameters (RingHom.id ℝ) D u) D₀ (map (algebraMap ℚ ℝ) V)
    (fun j => eval u (A j)) (normalizedMajorLeft E e H u) (middle u) (rationalMajorRight Q a u)
    (hfactor u) (hpotential u)).2
  have h := congrArg (eval b) hpoly
  simp only [map_add, map_sub, polynomialTranslate_eval_ring,
    specializeMajorParameters_eval, eval₂_id, normalizedMajorLeft, rationalMajorRight,
    eval_map, Pi.add_apply, Pi.neg_apply] at h
  rw [majorSlowPolynomial_eval, majorRationalPolynomial_eval₂]
  simp only [eval_map]
  simpa only [sub_eq_add_neg, add_assoc] using h

theorem algebraic_major_normalized_slow_mass
    (D₀ : MvPolynomial B ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (V : MvPolynomial B ℚ) (e : B → MvPolynomial U ℝ)
    {M : ℝ} (hM : 0 ≤ M) (he : ∀ j, realPolynomialMass (e j) ≤ M) {d : ℕ}
    (hE : E.totalDegree ≤ d) (hV : (map (algebraMap ℚ ℝ) V).totalDegree ≤ d) :
    realPolynomialMass (majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e) ≤
      realPolynomialMass D₀ +
        (realPolynomialMass E + realPolynomialMass (map (algebraMap ℚ ℝ) V)) * (1 + M) ^ d :=
  majorSlowPolynomial_mass_le D₀ E (map (algebraMap ℚ ℝ) V) e hM he hE hV

theorem algebraic_major_normalized_decomposition
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (V : MvPolynomial B ℚ) (H : U → ℝ)
    (middle : (U → ℝ) → PolynomialTranslationGroupOver ℝ B)
    (hfactor : ∀ u, algebraicMajorSymbol D D₀ A u =
      normalizedMajorLeft E e H u * middle u * rationalMajorRight Q a u)
    (hpotential : ∀ u, (middle u).polynomial = map (algebraMap ℚ ℝ) V -
      polynomialTranslate (-(middle u).base) (map (algebraMap ℚ ℝ) V))
    (q d : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (he : ∀ j, realPolynomialMass (e j) ≤ M)
    (hE : E.totalDegree ≤ d) (hV : V.totalDegree ≤ d)
    (hQgrid : (fun m => Q.coeff m) ∈ denominatorGrid q)
    (hVgrid : (fun m => V.coeff m) ∈ denominatorGrid q)
    (hagrid : ∀ j, (fun m => (a j).coeff m) ∈ denominatorGrid q) :
    ∃ S : MvPolynomial (U ⊕ B) ℝ, ∃ R : MvPolynomial (U ⊕ B) ℚ,
      (∀ (u : U → ℝ) (b : B → ℝ),
        eval (Sum.elim u b) D =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R) ∧
      realPolynomialMass S ≤ realPolynomialMass D₀ +
        (realPolynomialMass E + realPolynomialMass (map (algebraMap ℚ ℝ) V)) *
          (1 + M) ^ d ∧
      (fun m => R.coeff m) ∈ denominatorGrid (q ^ (d + 1)) := by
  refine ⟨majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e,
    majorRationalPolynomial Q V a, ?_, ?_, ?_⟩
  · exact algebraic_major_normalized_identity D D₀ A E e Q a V H middle
      hfactor hpotential
  · apply algebraic_major_normalized_slow_mass D₀ E V e hM he hE
    apply le_trans (b := V.totalDegree) ?_ hV
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) V hm)
  · exact majorRationalPolynomial_denominatorGrid Q V a q d hV hQgrid hVgrid hagrid

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

private theorem majorFunctionAdd {B R : Type*} [Add R] (f g : B → R) :
    f + g = fun i => f i + g i := rfl

private theorem majorFunctionSub {B R : Type*} [Sub R] (f g : B → R) :
    f - g = fun i => f i - g i := rfl

private theorem majorFunctionNeg {B R : Type*} [Neg R] (f : B → R) :
    -f = fun i => -f i := rfl

namespace PolynomialTranslationGroupOver

theorem algebraic_major_eval_on_subspace
    {B R : Type*} [CommRing R] (K : Submodule R (B → R))
    (D D₀ V : MvPolynomial B R) (A : B → R)
    (left middle right : PolynomialTranslationGroupOver R B)
    (hfactor : (⟨A, D - polynomialTranslate (-A) D₀⟩ : PolynomialTranslationGroupOver R B) =
      left * middle * right)
    (hpotential : ∀ z ∈ K, eval z middle.polynomial = eval z V - eval (z - middle.base) V)
    (hright : right.base ∈ K) (b : B → R) (hb : b ∈ K) :
    eval b D = eval (b - A) D₀ + eval (b - A + left.base) left.polynomial -
      eval (b - A + left.base) V + eval b right.polynomial + eval (b - right.base) V := by
  have hbase : A = left.base + middle.base + right.base := congrArg base hfactor
  have hpoly := congrArg (fun g : PolynomialTranslationGroupOver R B => eval b g.polynomial) hfactor
  change eval b (D - polynomialTranslate (-A) D₀) =
    eval b (polynomialTranslate (-right.base)
      (polynomialTranslate (-middle.base) left.polynomial + middle.polynomial) +
        right.polynomial) at hpoly
  simp only [map_sub, map_add, polynomialTranslate_eval_ring] at hpoly
  have hpot := hpotential (b - right.base) (K.sub_mem hb hright)
  have hx' : b - right.base - middle.base = b - A + left.base := by rw [hbase]; abel
  rw [hx'] at hpot
  have hpoly' : eval b D - eval (b - A) D₀ =
      eval (b - right.base - middle.base) left.polynomial +
        eval (b - right.base) middle.polynomial + eval b right.polynomial := by
    simpa only [majorFunctionSub, majorFunctionAdd, majorFunctionNeg,
      sub_eq_add_neg, Pi.add_apply, Pi.neg_apply] using hpoly
  rw [hx', hpot] at hpoly'
  linear_combination hpoly'

end PolynomialTranslationGroupOver

theorem algebraic_major_normalized_identity_on_subspace
    {U B : Type*} (K : Submodule ℝ (B → ℝ))
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (V : MvPolynomial B ℚ) (H : U → ℝ)
    (middle : (U → ℝ) → PolynomialTranslationGroupOver ℝ B)
    (hfactor : ∀ u, algebraicMajorSymbol D D₀ A u =
      normalizedMajorLeft E e H u * middle u * rationalMajorRight Q a u)
    (hpotential : ∀ u, ∀ z ∈ K,
      eval z (middle u).polynomial = eval₂ (algebraMap ℚ ℝ) z V -
        eval₂ (algebraMap ℚ ℝ) (z - (middle u).base) V)
    (hright : ∀ u, (fun j => eval₂ (algebraMap ℚ ℝ) u (a j)) ∈ K)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) D =
      eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j)))
        (majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e) +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (majorRationalPolynomial Q V a) := by
  have h := PolynomialTranslationGroupOver.algebraic_major_eval_on_subspace K
    (specializeMajorParameters (RingHom.id ℝ) D u) D₀ (map (algebraMap ℚ ℝ) V)
    (fun j => eval u (A j)) (normalizedMajorLeft E e H u) (middle u)
    (rationalMajorRight Q a u) (hfactor u)
    (by simpa only [eval_map] using hpotential u) (hright u) b hb
  rw [majorSlowPolynomial_eval, majorRationalPolynomial_eval₂]
  simp only [normalizedMajorLeft, rationalMajorRight, specializeMajorParameters_eval,
    eval₂_id, eval_map] at h ⊢
  simpa only [majorFunctionSub, majorFunctionAdd, Pi.sub_apply, Pi.add_apply, add_assoc] using h

theorem algebraic_major_normalized_decomposition_on_subspace
    {U B : Type*} (K : Submodule ℝ (B → ℝ))
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (V : MvPolynomial B ℚ) (H : U → ℝ)
    (middle : (U → ℝ) → PolynomialTranslationGroupOver ℝ B)
    (hfactor : ∀ u, algebraicMajorSymbol D D₀ A u =
      normalizedMajorLeft E e H u * middle u * rationalMajorRight Q a u)
    (hpotential : ∀ u, ∀ z ∈ K,
      eval z (middle u).polynomial = eval₂ (algebraMap ℚ ℝ) z V -
        eval₂ (algebraMap ℚ ℝ) (z - (middle u).base) V)
    (hright : ∀ u, (fun j => eval₂ (algebraMap ℚ ℝ) u (a j)) ∈ K)
    (q d : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (he : ∀ j, realPolynomialMass (e j) ≤ M)
    (hE : E.totalDegree ≤ d) (hV : V.totalDegree ≤ d)
    (hQgrid : (fun m => Q.coeff m) ∈ denominatorGrid q)
    (hVgrid : (fun m => V.coeff m) ∈ denominatorGrid q)
    (hagrid : ∀ j, (fun m => (a j).coeff m) ∈ denominatorGrid q) :
    ∃ S : MvPolynomial (U ⊕ B) ℝ, ∃ R : MvPolynomial (U ⊕ B) ℚ,
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) D =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R) ∧
      realPolynomialMass S ≤ realPolynomialMass D₀ +
        (realPolynomialMass E + realPolynomialMass (map (algebraMap ℚ ℝ) V)) *
          (1 + M) ^ d ∧
      (fun m => R.coeff m) ∈ denominatorGrid (q ^ (d + 1)) := by
  refine ⟨majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e,
    majorRationalPolynomial Q V a, ?_, ?_, ?_⟩
  · exact algebraic_major_normalized_identity_on_subspace K D D₀ A E e Q a V H middle
      hfactor hpotential hright
  · apply algebraic_major_normalized_slow_mass D₀ E V e hM he hE
    apply le_trans (b := V.totalDegree) ?_ hV
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) V hm)
  · exact majorRationalPolynomial_denominatorGrid Q V a q d hV hQgrid hVgrid hagrid

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem specializeMajorParameters_translatedSlice {U B : Type*}
    (P0 : MvPolynomial B ℝ) (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ)
      (eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j)) P0) u =
        polynomialTranslate (fun j => -eval u (x j)) P0 := by
  apply MvPolynomial.funext
  intro b
  rw [specializeMajorParameters_eval, polynomialTranslate_eval_ring]
  change eval₂ (RingHom.id ℝ) (Sum.elim u b)
    (eval₂ C (fun j => X (Sum.inr j) - rename Sum.inl (x j)) P0) = _
  rw [← eval₂_assoc]
  simp only [eval₂_id]
  apply congrArg (fun f : B → ℝ => eval f P0)
  funext j
  rw [map_sub, eval_X, eval_rename]
  rfl

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem specializeMajorParameters_zero_weightedSupportLE (w : B → ℕ)
    {v : U → ℕ} {d : ℕ} {P : MvPolynomial (U ⊕ B) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) d) :
    specializeMajorParameters (RingHom.id R) P (fun _ => 0) ∈
      weightedSupportLE w d := by
  change aeval (Sum.elim (fun _ : U => C (0 : R)) X) P ∈ weightedSupportLE w d
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  cases i with
  | inl i => exact weightedSupportLE_C w (v i) 0
  | inr i => exact weightedSupportLE_X w i

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical

variable {X B J V : Type*} [Fintype J]
  [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem exists_vector_algebraic_major_decomposition
    (basis : Basis J ℝ V) (p : VectorPolynomial (X ⊕ B) ℚ V)
    (K : J → Submodule ℝ (B → ℝ))
    (D₀ : J → MvPolynomial B ℝ) (A : B → MvPolynomial X ℝ)
    (E : J → MvPolynomial (X ⊕ B) ℝ) (e : J → B → MvPolynomial X ℝ)
    (Q : J → MvPolynomial (X ⊕ B) ℚ) (a : J → B → MvPolynomial X ℚ)
    (potential : J → MvPolynomial B ℚ) (H : X → ℝ)
    (middle : J → (X → ℝ) → PolynomialTranslationGroupOver ℝ B)
    (hfactor : ∀ j u,
      algebraicMajorSymbol (coordinate (basis.coord j).toAddMonoidHom p) (D₀ j) A u =
        normalizedMajorLeft (E j) (e j) H u * middle j u * rationalMajorRight (Q j) (a j) u)
    (hpotential : ∀ j u z, z ∈ K j →
      MvPolynomial.eval z (middle j u).polynomial =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) z (potential j) -
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (z - (middle j u).base) (potential j))
    (hright : ∀ j u, (fun b => MvPolynomial.eval₂ (algebraMap ℚ ℝ) u (a j b)) ∈ K j)
    (q d : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (he : ∀ j b, realPolynomialMass (e j b) ≤ M)
    (hE : ∀ j, (E j).totalDegree ≤ d) (hV : ∀ j, (potential j).totalDegree ≤ d)
    (hQgrid : ∀ j, (fun α => (Q j).coeff α) ∈ denominatorGrid q)
    (hVgrid : ∀ j, (fun α => (potential j).coeff α) ∈ denominatorGrid q)
    (hagrid : ∀ j b, (fun α => (a j b).coeff α) ∈ denominatorGrid q) :
    ∃ slow rat : VectorPolynomial (X ⊕ B) ℚ V,
      (∀ u z, (∀ j, z ∈ K j) →
        eval₂ (Sum.elim u z) p =
          eval₂ (Sum.elim u z) (realChartSubstitute (normalizedRealPolynomialChart H A) slow) +
            eval₂ (Sum.elim u z) rat) ∧
      (∀ α j, |basis.repr (coefficients slow α) j| ≤ realPolynomialMass (D₀ j) +
        (realPolynomialMass (E j) +
          realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) (potential j))) * (1 + M)^d) ∧
      (∀ α, (fun j => basis.repr (coefficients rat α) j) ∈ realDenominatorGrid (q^(d+1))) := by
  have hdecomp (j : J) := algebraic_major_normalized_decomposition_on_subspace
    (K j) (coordinate (basis.coord j).toAddMonoidHom p) (D₀ j) A (E j) (e j)
    (Q j) (a j) (potential j) H (middle j) (hfactor j) (hpotential j) (hright j)
    q d hM (he j) (hE j) (hV j) (hQgrid j) (hVgrid j) (hagrid j)
  choose S R hidentity hmass hgrid using hdecomp
  let slow : VectorPolynomial (X ⊕ B) ℚ V := ofCoordinates basis S
  let rat : VectorPolynomial (X ⊕ B) ℚ V :=
    ofCoordinates basis (fun j => MvPolynomial.map (algebraMap ℚ ℝ) (R j))
  have hslowcoeff (α : (X ⊕ B) →₀ ℕ) (j : J) :
      basis.repr (coefficients slow α) j = (S j).coeff α := by
    exact congrArg (fun polynomial : MvPolynomial (X ⊕ B) ℝ => polynomial.coeff α)
      (coordinate_ofCoordinates basis S j)
  have hratcoeff (α : (X ⊕ B) →₀ ℕ) (j : J) :
      basis.repr (coefficients rat α) j =
        (MvPolynomial.map (algebraMap ℚ ℝ) (R j)).coeff α := by
    exact congrArg (fun polynomial : MvPolynomial (X ⊕ B) ℝ => polynomial.coeff α)
      (coordinate_ofCoordinates basis (fun j => MvPolynomial.map (algebraMap ℚ ℝ) (R j)) j)
  refine ⟨slow, rat, ?_, ?_, ?_⟩
  · intro u z hz
    rw [eval₂_normalizedRealPolynomialChart]
    apply basis.repr.injective
    ext j
    change basis.coord j (eval₂ _ p) = basis.coord j (eval₂ _ slow + eval₂ _ rat)
    rw [map_add, coordinate_eval₂, coordinate_eval₂, coordinate_eval₂]
    change MvPolynomial.eval _ (coordinate (basis.coord j).toAddMonoidHom p) =
      MvPolynomial.eval _ (coordinate (basis.coord j).toAddMonoidHom (ofCoordinates basis S)) +
        MvPolynomial.eval _ (coordinate (basis.coord j).toAddMonoidHom
          (ofCoordinates basis (fun j => MvPolynomial.map (algebraMap ℚ ℝ) (R j))))
    rw [coordinate_ofCoordinates, coordinate_ofCoordinates, MvPolynomial.eval_map]
    exact hidentity j u z (hz j)
  · intro α j
    rw [hslowcoeff]
    exact (realPolynomialMass_coeff_le (S j) α).trans (hmass j)
  · intro α
    have hrealgrid (j : J) : realPolynomialCoefficientGrid (q^(d+1))
        (MvPolynomial.map (algebraMap ℚ ℝ) (R j)) :=
      (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr (hgrid j)
    choose z hz using hrealgrid
    refine ⟨fun j => z j α, funext fun j => ?_⟩
    change (z j α : ℝ) = (q^(d+1) : ℕ) * basis.repr (coefficients rat α) j
    rw [hratcoeff]
    exact congrFun (hz j) α

end Erdos3.VectorPolynomial

end

end OAI
