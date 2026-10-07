import OAI.Combinatorics.Progressions.Dynamics.LayerRemovalBudgets
import OAI.Combinatorics.Progressions.Estimates.ModeShiftLengths
import OAI.Combinatorics.Progressions.Estimates.SubspaceLayeredModeSmoothRemoval
import OAI.Combinatorics.Progressions.Fourier.AffineFrequencyLift

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators
open VectorPolynomial

theorem cubeModePolynomialBudget_pos (q : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 < cubeModePolynomialBudget q L := by
  unfold cubeModePolynomialBudget
  positivity

theorem affineSite_intCast {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (s : Finset (Fin q)) :
    (fun k => ((affineSite root difference s k : ℤ) : ℝ)) =
      affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s := by
  exact (affineSite_map (Int.castRingHom ℝ) root difference s).symm

theorem exists_affine_bounded_integer_mode {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : (K →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree ≤ h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, Homogeneous h p →
        affineModeLift (coefficientFunctional (fun d j => (frequency d j : ℝ))) (map W.subtype p) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(integerContractedRow (affineLiftFrequency frequency) (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * cubeModePolynomialBudget q L ^ h) ∧
      ∃ w : W, (∑ j, (integerContractedRow (affineLiftFrequency frequency)
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  apply exists_vertex_bounded_integer_mode W root difference hlin hL hC hsite
    (affineLiftFrequency frequency) h (affineLiftFrequency_bound frequency hbound)
  simpa only [affineModeLift_integerFrequency] using hnonfactor

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_selected_affine_mode_rows {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ p, Homogeneous (i.val + 1) p →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype p) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) p)) :
    ∃ (i : Fin m) (rows : Fin (i.val + 1) → Option K → ℤ),
      (∀ j, i < j → ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
        ∀ p, DegreeLE (1 : Option K → ℕ) (j.val + 1) p →
          affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))) (map (U j).subtype p) =
            M (VectorPolynomial.siteEvaluation
              (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) p)) ∧
      (∀ r k, |(rows r k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      (∀ s : Finset (Fin q), ∃ r, (∑ k, rows r k * affineSite root difference s k) = 0) ∧
      (∀ a, |(integerContractedRow (affineLiftFrequency (frequency i))
        (∏ r, rowPolynomial (rows r)) a : ℝ)| ≤ C * cubeModePolynomialBudget q L ^ (i.val + 1)) ∧
      ∃ w : U i, (∑ a, (integerContractedRow (affineLiftFrequency (frequency i))
        (∏ r, rowPolynomial (rows r)) a : ℝ) * w.val a) ≠ 0 := by
  let site : Finset (Fin q) → K → ℝ :=
    fun s k => (root k : ℝ) + ∑ r ∈ s, (difference r k : ℝ)
  have he : (fun s (k : Option K) => k.elim 1 (site s)) =
      (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) := by
    funext s k
    cases k <;> rfl
  obtain ⟨i, hi, hh⟩ := exists_highest_affine_subspace_nonfactor U site
    (fun j => coefficientFunctional (fun d a => (frequency j d a : ℝ))) (by rwa [he])
  rw [he] at hi hh
  obtain ⟨rows, hr, hz, hb, hw⟩ := exists_affine_bounded_integer_mode (U i) root difference hlin
    hL hC hsite (frequency i) (i.val + 1) (hbound i) hi
  exact ⟨i, rows, hh, hr, hz, hb, hw⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_local_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m,
      ((i.val + 1).factorial : ℝ) * (C * cubeModePolynomialBudget q L ^ (i.val + 1)) ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    {β : ℝ} (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ∃ i : Fin m, ∃ rows : Fin (i.val + 1) → Option K → ℤ,
      (∀ a k, |(rows a k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      ∀ base : Option K → I → ℝ,
        ‖𝔼 x : Fin (i.val + 1) → ∀ j, Fin (N j),
          layeredModeTestedPhase
            (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
            p Q (fun s => affineSite root difference s) test
            (rowShiftedTuple base rows
              (fun (y : ∀ j, Fin (N j)) j => (stride j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ β := by
  classical
  obtain ⟨i, rows, hfactor, hrows, hzero, hcontract, hnonzero⟩ :=
    exists_selected_affine_mode_rows U root difference hlin hL hC hsite frequency hbound hbad
  have hcast : (fun s k => ((affineSite root difference s k : ℤ) : ℝ)) =
      (fun s => affineSite (fun k => (root k : ℝ)) (fun a k => (difference a k : ℝ)) s) := by
    funext s
    exact affineSite_intCast root difference s
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_subspace_layered_mode_reduction i U
    (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
    p hm hp (fun s => affineSite root difference s)
    (by rw [hcast]; exact hfactor) Q (hQ.trans_lt (Nat.zero_lt_succ _)) test htest
  refine ⟨i, rows, hrows, ?_⟩
  intro base
  simp_rw [he, affineModeLift_integerFrequency]
  exact inhomogeneous_coefficient_mode_local_removal (affineLiftFrequency (frequency i)) rows
    (p i) (hp i) (U i) N stride hs hζ (hN i) H hH hA hscale (hrank i)
    hcontract (hrowBudget i) hnonzero (hdenom i) (hcoeff i)
    (fun s => affineSite root difference s) hzero Q' hQ' test' ht hβ (hpower i) base

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_cube_mode_residue_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m,
      ((i.val + 1).factorial : ℝ) * (C * cubeModePolynomialBudget q L ^ (i.val + 1)) ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {r β : ℝ} (hr : 0 ≤ r)
    (hmove : ∀ i : Fin m, ∀ z,
      ((i.val + 1 : ℕ) : ℝ) * cubeModePolynomialBudget q L *
        ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  obtain ⟨i, rows, hrows, hlocal⟩ := exists_affine_cube_local_removal
    U root difference hlin hL hC hsite frequency hbound hbad p hp hm N stride hs hζ hN
    H hH hA hscale hrank hrowBudget hdenom hcoeff Q hQ test htest hβ hpower
  have hNp k : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos i.val hζ).trans_le (hN i k)
  exact residue_smooth_row_shift_transfer N stride hNp hs rows residue V hV hZ hV1
    hδ hδ1 hmesh hsmall (cubeModePolynomialBudget_pos q hL).le hrows hr (hmove i)
    _ (layeredModeTestedPhase_norm_le _ p Q _ test htest) hlocal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem anchored_affine_cube_mode_residue_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    (anchor : Option K × I → ℤ)
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m,
      ((i.val + 1).factorial : ℝ) * (C * cubeModePolynomialBudget q L ^ (i.val + 1)) ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {r β : ℝ} (hr : 0 ≤ r)
    (hmove : ∀ i : Fin m, ∀ z,
      ((i.val + 1 : ℕ) : ℝ) * cubeModePolynomialBudget q L *
        ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => ((anchor + residueLatticeArray residue stride z) (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  obtain ⟨i, rows, hrows, hlocal⟩ := exists_affine_cube_local_removal
    U root difference hlin hL hC hsite frequency hbound hbad p hp hm N stride hs hζ hN
    H hH hA hscale hrank hrowBudget hdenom hcoeff Q hQ test htest hβ hpower
  have hNp k : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos i.val hζ).trans_le (hN i k)
  have h := anchored_residue_smooth_row_shift_transfer (fun k i => (anchor (k,i) : ℝ)) N stride hNp hs rows residue V hV hZ hV1
    hδ hδ1 hmesh hsmall (cubeModePolynomialBudget_pos q hL).le hrows hr (hmove i)
    _ (layeredModeTestedPhase_norm_le _ p Q _ test htest) hlocal

  simpa only [← integerArrayFrame_add] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators NNReal

theorem affine_cube_mode_smooth_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m,
      ((i.val + 1).factorial : ℝ) * (C * cubeModePolynomialBudget q L ^ (i.val + 1)) ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (hV1 : ∀ z, 1 ≤ V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {r β : ℝ} (hr : 0 ≤ r)
    (hmove : ∀ i : Fin m, ∀ z,
      ((i.val + 1 : ℕ) : ℝ) * cubeModePolynomialBudget q L *
        ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((smoothProductPMF V hV z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  obtain ⟨i, rows, hfactor, hrows, hzero, hcontract, hnonzero⟩ :=
    exists_selected_affine_mode_rows U root difference hlin hL hC hsite frequency hbound hbad
  have hcast : (fun s k => ((affineSite root difference s k : ℤ) : ℝ)) =
      (fun s => affineSite (fun k => (root k : ℝ)) (fun a k => (difference a k : ℝ)) s) := by
    funext s
    exact affineSite_intCast root difference s
  apply subspace_layered_mode_smooth_removal i (affineLiftFrequency (frequency i)) rows
    (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
    (affineModeLift_integerFrequency (frequency i)) p hp U hm N stride hs hζ (hN i)
    H hH hA hscale (hrank i) hcontract (hrowBudget i) hnonzero (hdenom i) (hcoeff i)
    (fun s => affineSite root difference s) _ hzero Q (hQ.trans_lt (Nat.zero_lt_succ _))
    test htest V hV hV1 hδ hδ1 hmesh hsmall (cubeModePolynomialBudget_pos q hL).le hrows
    hr (hmove i) hβ (hpower i)
  rw [hcast]
  exact hfactor

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators NNReal

theorem affine_cube_residue_removal_of_widths {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R T S : ℝ} (hζ : 0 < ζ) (hT : 0 < T) (hS : 0 ≤ S)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (hH : ∀ k, 0 < H k)
    (hsize : ∀ k, (stride k : ℝ) * T * (finiteLayerBiasBudget m ζ + 1) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : layerRemovalRankBudget m (Fintype.card I) C (cubeModePolynomialBudget q L)
      (finiteLayerBiasBudget m ζ) (2 * T) S ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {ρ r β : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (hmove : (m : ℝ) * cubeModePolynomialBudget q L ≤ r * ρ * T)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  let B := finiteLayerBiasBudget m ζ
  let D := cubeModePolynomialBudget q L
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m hζ
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hA : 0 ≤ 2 * T := by positivity
  have hb (i : Fin m) : multiaffineBiasBudget i.val ζ ≤ B :=
    multiaffineBiasBudget_le_finite i hζ
  obtain ⟨N, hN, hscale, hshift⟩ := exists_mode_shift_lengths m hT hB hρ hr hmove H stride hs hsize V hwidth
  have hbud (i : Fin m) := layerRemovalRankBudget_bounds i (Fintype.card I) hC hD
    (zero_le_one.trans hB) hA hS
  apply affine_cube_mode_residue_removal U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm N stride hs hζ (fun i k => (hb i).trans (hN k)) H hH hA hscale hrank
    (fun i => (hbud i).1.trans hR) _ _ Q hQ test htest residue V hV hZ hV1 hδ hδ1 hmesh hsmall hr _ hβ hpower
  · intro i
    have hi := tensorDenominatorBound_le (H := Fin (i.val + 1))
      (multiaffineBiasBudget_pos i.val hζ).le (fun k => (stride k : ℝ))
      (fun k => Nat.cast_nonneg _) hstride
    have hi' : (∏ j : Fin (i.val + 1) → I,
        (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤
        (multiaffineBiasBudget i.val ζ * S ^ (i.val + 1)) ^ (Fintype.card I ^ (i.val + 1)) := by
      simpa only [Fintype.card_fin] using hi
    apply hi'.trans
    apply le_trans _ ((hbud i).2.1.trans hR)
    exact pow_le_pow_left₀
      (mul_nonneg (multiaffineBiasBudget_pos i.val hζ).le (pow_nonneg hS _))
      (mul_le_mul_of_nonneg_right (hb i) (pow_nonneg hS _)) _
  · intro i
    apply le_trans _ ((hbud i).2.2.trans hR)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hb i) (pow_nonneg hA _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  · intro i z
    have hi : ((i.val + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    apply le_trans _ (hshift z)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hD)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators NNReal

theorem anchored_affine_cube_residue_removal_of_widths {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    (anchor : Option K × I → ℤ)
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R T S : ℝ} (hζ : 0 < ζ) (hT : 0 < T) (hS : 0 ≤ S)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (hH : ∀ k, 0 < H k)
    (hsize : ∀ k, (stride k : ℝ) * T * (finiteLayerBiasBudget m ζ + 1) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : layerRemovalRankBudget m (Fintype.card I) C (cubeModePolynomialBudget q L)
      (finiteLayerBiasBudget m ζ) (2 * T) S ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {ρ r β : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (hmove : (m : ℝ) * cubeModePolynomialBudget q L ≤ r * ρ * T)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => ((anchor + residueLatticeArray residue stride z) (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  let B := finiteLayerBiasBudget m ζ
  let D := cubeModePolynomialBudget q L
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m hζ
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hA : 0 ≤ 2 * T := by positivity
  have hb (i : Fin m) : multiaffineBiasBudget i.val ζ ≤ B :=
    multiaffineBiasBudget_le_finite i hζ
  obtain ⟨N, hN, hscale, hshift⟩ := exists_mode_shift_lengths m hT hB hρ hr hmove H stride hs hsize V hwidth
  have hbud (i : Fin m) := layerRemovalRankBudget_bounds i (Fintype.card I) hC hD
    (zero_le_one.trans hB) hA hS
  apply anchored_affine_cube_mode_residue_removal anchor U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm N stride hs hζ (fun i k => (hb i).trans (hN k)) H hH hA hscale hrank
    (fun i => (hbud i).1.trans hR) _ _ Q hQ test htest residue V hV hZ hV1 hδ hδ1 hmesh hsmall hr _ hβ hpower
  · intro i
    have hi := tensorDenominatorBound_le (H := Fin (i.val + 1))
      (multiaffineBiasBudget_pos i.val hζ).le (fun k => (stride k : ℝ))
      (fun k => Nat.cast_nonneg _) hstride
    have hi' : (∏ j : Fin (i.val + 1) → I,
        (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤
        (multiaffineBiasBudget i.val ζ * S ^ (i.val + 1)) ^ (Fintype.card I ^ (i.val + 1)) := by
      simpa only [Fintype.card_fin] using hi
    apply hi'.trans
    apply le_trans _ ((hbud i).2.1.trans hR)
    exact pow_le_pow_left₀
      (mul_nonneg (multiaffineBiasBudget_pos i.val hζ).le (pow_nonneg hS _))
      (mul_le_mul_of_nonneg_right (hb i) (pow_nonneg hS _)) _
  · intro i
    apply le_trans _ ((hbud i).2.2.trans hR)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hb i) (pow_nonneg hA _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  · intro i z
    have hi : ((i.val + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    apply le_trans _ (hshift z)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hD)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Erdos3.BooleanCubeKernel

end

end OAI
