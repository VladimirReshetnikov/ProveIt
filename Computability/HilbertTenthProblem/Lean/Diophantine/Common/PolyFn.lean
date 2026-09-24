import Diophantine.Common.RefinedRelationCombiningPolynomial

/-!
# Integer functions given by integer polynomials

`PolyFn f` says that `f : (σ → ℤ) → ℤ` is the evaluation of an integer multivariate polynomial.
The class is closed under constants, coordinates, ring operations, substitution into a
univariate integer polynomial, and the refined relation-combining value.
-/

namespace Diophantine

open MvPolynomial

variable {σ : Type*}

/-- `f` is the evaluation function of an integer polynomial. -/
def PolyFn (f : (σ → ℤ) → ℤ) : Prop :=
  ∃ p : MvPolynomial σ ℤ, ∀ v, eval v p = f v

namespace PolyFn

theorem const (c : ℤ) : PolyFn (σ := σ) fun _ => c := ⟨C c, fun _ => eval_C _⟩

theorem var (i : σ) : PolyFn fun v : σ → ℤ => v i := ⟨X i, fun _ => eval_X _⟩

theorem add {f g : (σ → ℤ) → ℤ} (hf : PolyFn f) (hg : PolyFn g) :
    PolyFn fun v => f v + g v := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun v => by simp [hp, hq]⟩

theorem sub {f g : (σ → ℤ) → ℤ} (hf : PolyFn f) (hg : PolyFn g) :
    PolyFn fun v => f v - g v := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun v => by simp [hp, hq]⟩

theorem mul {f g : (σ → ℤ) → ℤ} (hf : PolyFn f) (hg : PolyFn g) :
    PolyFn fun v => f v * g v := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun v => by simp [hp, hq]⟩

theorem pow {f : (σ → ℤ) → ℤ} (hf : PolyFn f) (n : ℕ) : PolyFn fun v => f v ^ n := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ n, fun v => by simp [hp]⟩

theorem natCast (n : ℕ) : PolyFn (σ := σ) fun _ => (n : ℤ) := const _

theorem ofNat (n : ℕ) [n.AtLeastTwo] : PolyFn (σ := σ) fun _ => (OfNat.ofNat n : ℤ) := const _

theorem one : PolyFn (σ := σ) fun _ => (1 : ℤ) := const _

theorem congr {f g : (σ → ℤ) → ℤ} (hf : PolyFn f) (h : ∀ v, f v = g v) : PolyFn g := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, fun v => (hp v).trans (h v)⟩

theorem eval_aeval (p : Polynomial ℤ) (q : MvPolynomial σ ℤ) (v : σ → ℤ) :
    eval v (Polynomial.aeval q p) = p.eval (eval v q) := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | monomial n a _ => simp

/-- Substitution into a univariate integer polynomial. -/
theorem polyEval (p : Polynomial ℤ) {f : (σ → ℤ) → ℤ} (hf : PolyFn f) :
    PolyFn fun v => p.eval (f v) := by
  obtain ⟨q, hq⟩ := hf
  exact ⟨Polynomial.aeval q p, fun v => by rw [eval_aeval, hq]⟩

/-- The refined relation-combining value. -/
theorem rcValue (q : ℕ) {A V : Fin q → (σ → ℤ) → ℤ} {n B C D : (σ → ℤ) → ℤ}
    (hA : ∀ i, PolyFn (A i)) (hV : ∀ i, PolyFn (V i)) (hn : PolyFn n) (hB : PolyFn B)
    (hC : PolyFn C) (hD : PolyFn D) :
    PolyFn fun v => RefinedRelationCombiningPolynomial.value q (fun i => A i v)
      (fun i => V i v) (n v) (B v) (C v) (D v) := by
  choose pA hpA using hA
  choose pV hpV using hV
  obtain ⟨pn, hpn⟩ := hn; obtain ⟨pB, hpB⟩ := hB; obtain ⟨pC, hpC⟩ := hC; obtain ⟨pD, hpD⟩ := hD
  refine ⟨RefinedRelationCombiningPolynomial.compose q pA pV pn pB pC pD, fun v => ?_⟩
  rw [RefinedRelationCombiningPolynomial.eval_compose]
  simp only [hpA, hpV, hpn, hpB, hpC, hpD]

end PolyFn

end Diophantine
