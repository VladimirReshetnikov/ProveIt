import OAI.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization
import OAI.Combinatorics.Progressions.Geometry.MultidegreeCoordinateSplit

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ V : Type*} [DecidableEq σ] [AddCommGroup V] [Module ℚ V]

noncomputable def splitTriple (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) : VectorPolynomial (Option σ) ℚ (V × V × V) :=
  pair (substitute (splitCoordinatePolynomial i (u + v)) p)
    (pair (substitute (splitCoordinatePolynomial i u) p)
      (substitute (splitCoordinatePolynomial i v) p))

theorem eval_splitTriple (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) (x : Option σ → ℚ) :
    eval x (splitTriple i u v p) =
      (eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x (u + v))) p,
       eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x u)) p,
       eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x v)) p) := by
  simp only [splitTriple, eval_pair, eval_substitute, splitCoordinatePolynomial_eval]

theorem splitTriple_zero (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) (hp : coefficients p 0 = 0)
    (hu : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) u = 0)
    (hv : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) v = 0) :
    coefficients (splitTriple i u v p) 0 = 0 := by
  rw [← eval_zero_eq_coefficient, eval_splitTriple]
  simp only [map_add, hu, hv, add_zero, Function.update_eq_self, eval_zero_eq_coefficient, hp]
  rfl

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem splitTriple_neutral (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleNeutral (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) a +
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a = _
  rw [h]
  abel

theorem splitTriple_left (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleLeft (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
        VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair, map_sub, Finsupp.sub_apply]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a = _
  rw [h]
  abel

theorem splitTriple_right (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleRight (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p -
        VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair, map_sub, Finsupp.sub_apply]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) a = _
  rw [h]
  abel

theorem splitTriple_coefficient_mem (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hv : v ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : Option σ →₀ ℕ) :
    coefficients (splitTriple i u v p) a ∈
      F.additiveTripleLayer i (omittedCoordinateWeight i) (Finsupp.weight (fun _ : Option σ => 1) a) := by
  rw [F.mem_additiveTripleLayer, F.splitTriple_neutral i hi u v hp,
    F.splitTriple_left i hi u v hp, F.splitTriple_right i hi u v hp]
  exact ⟨F.split_substitution_zero_weighted i hp a,
    F.split_substitution_sub_mem_active i u hu hp a,
    F.split_substitution_sub_mem_active i v hv hp a⟩

end MultidegreeLieFiltration

end Erdos3

end

end OAI
