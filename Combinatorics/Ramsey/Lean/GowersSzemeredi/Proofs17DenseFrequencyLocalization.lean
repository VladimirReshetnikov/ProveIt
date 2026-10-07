import GowersSzemeredi.Proofs17MultilinearBoxEnergy

/-! Polynomial localization from arbitrary positive Fourier-box controls.
The proof retains the density, width exponent, and upper cell-length bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A dense multilinear frequency on a wide proper box supplies all the
geometry and energy needed for Proposition 17.7. -/
theorem polynomial_localization_of_dense_frequency_box {N d : Nat} [Fact N.Prime]
    (hd : 0 < d) (P : Box N d) (hP : P.IsProper)
    (f : ZMod N → Complex) (mu : Point N d → ZMod N) {alpha delta e : Real}
    (hα : 0 < alpha) (hδ : 0 < delta) (he : e ≤ 1 / 2)
    (hf : DiscValued f) (hmu : IsMultilinear mu)
    (hwidth : (N : Real) ^ e ≤ P.width) (hlarge : 4 ≤ (N : Real) ^ e)
    (hmass : delta * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha) :
    ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
      PolynomialOn (d + 1) Finset.univ phi ∧
      IsPartition (fun i => (Q i).carrier) Finset.univ ∧
      (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
      (N : Real) ^ e / (6 * d) ≤ l ∧
      (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
      ¬ UniformOnPartition (phaseTwist f phi) d
        ((2 : Real) ^ (-(2 * (d + 1) ^ 3 : Int)) * (delta / (2 : Real) ^ d * alpha ^ 2 / 4)) Q (l + 1) := by
  classical
  let B := P.carrier.filter fun x => alpha / 2 * N ≤ ‖fourier (cubeDifference f x) (mu x)‖
  have hBcard : B.card = section16LargeMultilinearFrequencyCount f P mu alpha := by
    unfold section16LargeMultilinearFrequencyCount countWhere
    congr 1
    ext x
    simp [B]
  obtain ⟨m, S, C, hm, hmpos, hmlower, hmsqrt, _, hstep, hp, hw, haxes, hCB, hCS, hCm⟩ :=
    P.dense_odd_short_box hP hd B hδ.le he hwidth hlarge (Finset.filter_subset _ _)
      (by rwa [hBcard])
  have henergy := multilinear_box_fourier_energy S C f mu hα.le hCS hCm
    (fun x hx => (Finset.mem_filter.mp (hCB hx)).2)
  have hrho : 0 < delta / (2 : Real) ^ d * alpha ^ 2 / 4 := by positivity
  obtain ⟨phi, K, l, Q, hpoly, hpart, hproper, hlength, hupper, hfail⟩ :=
    proposition_17_7_with_upper N d m f S mu _ hrho hd hm hw haxes hstep hmsqrt hf hmu henergy
  refine ⟨phi, K, l, Q, hpoly, hpart, hproper, ?_, ?_, hfail⟩
  · have hd0 : (0 : Real) < d := by exact_mod_cast hd
    calc
      _ = ((N : Real) ^ e / 2) / (3 * d) := by field_simp; ring
      _ ≤ (m : Real) / (3 * d) := div_le_div_of_nonneg_right hmlower (by positivity)
      _ ≤ _ := hlength
  · intro i
    exact (by exact_mod_cast hupper i : ((Q i).length : Real) ≤ m).trans hmsqrt

end LeanProofs.GowersSzemeredi
