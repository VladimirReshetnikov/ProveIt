import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceSubstitution
import OAI.Combinatorics.Progressions.Geometry.ShiftedBoxSites
import OAI.Combinatorics.Progressions.Lattices.AffineTopCoefficient

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

noncomputable def integerSiteValue {K V : Type*} [Fintype K] [AddCommGroup V]
    (site : K → ℤ) (tuple : K → V) : V := ∑ k, site k • tuple k

noncomputable def rowShiftedTuple {h : ℕ} {K X V : Type*} [AddCommGroup V]
    (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (x : Fin h → X) (k : K) : V := base k + ∑ i, rows i k • shift (x i)

theorem rowShiftedSite_eq {h : ℕ} {K X V : Type*} [Fintype K] [AddCommGroup V]
    (site : K → ℤ) (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (x : Fin h → X) :
    integerSiteValue site (rowShiftedTuple base rows shift x) =
      shiftedBoxSite (integerSiteValue site base) (fun i => ∑ k, rows i k * site k) shift x := by
  unfold integerSiteValue rowShiftedTuple shiftedBoxSite
  simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_smul, mul_comm]

theorem row_shifted_site_phase_cauchySchwarz {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] [AddCommGroup V] (hh : 0 < h)
    (site : S → K → ℤ) (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (phase : (K → V) → ℝ) (test : S → V → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character (phase (rowShiftedTuple base rows shift x) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character ((additiveBoxDifference h
        (fun x (_ : Unit) => phase (rowShiftedTuple base rows shift x)) u v () : ℝ) : CircleFourier.Circle)‖ := by
  simpa only [rowShiftedSite_eq] using shifted_site_phase_cauchySchwarz hh
    (fun s => integerSiteValue (site s) base) (fun s i => ∑ k, rows i k * site s k)
    shift hzero (fun x => phase (rowShiftedTuple base rows shift x)) test htest

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem vector_shift_difference_eq_topSymbol {I : Type*} {n : ℕ}
    (base : I → ℝ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n)
    (u v : Fin n → I → ℝ) :
    additiveBoxDifference n
      (fun (w : Fin n → I → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, w i k) P) u v () =
      polynomialTopSymbol n P (fun i k => u i k - v i k) := by
  let f : Fin n → ℝ → I → ℝ := fun i t k => v i k + (u i k - v i k) * t
  have hu : (fun i => f i 1) = u := by
    funext i k
    dsimp [f]
    ring
  have hv : (fun i => f i 0) = v := by
    funext i k
    dsimp [f]
    ring
  have he := additiveBoxDifference_map n f
    (fun (w : Fin n → I → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, w i k) P)
    (fun _ => 1) (fun _ => 0) ()
  rw [hu, hv] at he
  rw [← he]
  have hfun :
      (fun (t : Fin n → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, f i (t i) k) P) =
      (fun (t : Fin n → ℝ) (_ : Unit) => eval (fun k => (base k + ∑ i, v i k) +
        ∑ i, (u i k - v i k) * t i) P) := by
    funext t z
    apply congrArg (fun point : I → ℝ => eval point P)
    funext k
    simp only [f, Finset.sum_add_distrib]
    ring
  rw [hfun]
  simpa only [sub_zero, Finset.prod_const_one, mul_one] using
    affineShift_difference_eq_topSymbol (fun k => base k + ∑ i, v i k)
      (fun i k => u i k - v i k) P hP (fun _ => 1) (fun _ => 0)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem row_shift_difference_eq_topSymbol {K J X : Type*} {h : ℕ}
    (base : K → J → ℝ) (rows : Fin h → K → ℤ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h) (u v : Fin h → X) :
    additiveBoxDifference h
      (fun x (_ : Unit) => eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P) u v () =
      polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) := by
  let f : Fin h → X → (K × J) → ℝ := fun i x z => (rows i z.1 : ℝ) * shift x z.2
  have he :
      (fun x (_ : Unit) => eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P) =
      (fun x (_ : Unit) => eval (fun z => base z.1 z.2 + ∑ i, f i (x i) z) P) := by
    funext x t
    apply congrArg (fun point : (K × J) → ℝ => eval point P)
    funext z
    simp only [rowShiftedTuple, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, f]
    simp only [zsmul_eq_mul]
  rw [he]
  have hm := additiveBoxDifference_map h f
    (fun (w : Fin h → (K × J) → ℝ) (_ : Unit) => eval (fun z => base z.1 z.2 + ∑ i, w i z) P)
    u v ()
  exact hm.trans (by simpa only [f, mul_sub] using
    (vector_shift_difference_eq_topSymbol
      (fun z => base z.1 z.2) P hP (fun i => f i (u i)) (fun i => f i (v i))))

end Erdos3

end

end OAI
