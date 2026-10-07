/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.CubeModeUniformBudget
import OAI.Combinatorics.Progressions.Dynamics.ModeAmplitudeErrorBudget
import OAI.Combinatorics.Progressions.Estimates.BoundedCommonSiteResidual
import OAI.Combinatorics.Progressions.Polynomial.FixedKernelPolynomialCover

namespace OAI

section

namespace Erdos3

noncomputable def modeResidueSideThreshold (m d : ℕ) (D S ρ ε : ℝ) : ℝ :=
  modeRemovalSideThreshold m d D S ρ ε + S / (ρ * modeRemovalMesh d)

theorem modeResidueSideThreshold_bounds (m d : ℕ) {D S ρ ε : ℝ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε) :
    modeRemovalSideThreshold m d D S ρ ε ≤ modeResidueSideThreshold m d D S ρ ε ∧
      S / modeRemovalMesh d ≤ ρ * modeResidueSideThreshold m d D S ρ ε := by
  have hδ := modeRemovalMesh_pos d
  have hb := (modeRemovalSideThreshold_bounds m d hD hS hρ hε).1
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · have hle : S / (ρ * modeRemovalMesh d) ≤ modeResidueSideThreshold m d D S ρ ε :=
      le_add_of_nonneg_left hb.le
    have he : ρ * (S / (ρ * modeRemovalMesh d)) = S / modeRemovalMesh d := by
      field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_left hle hρ.le

theorem modeResidueWidth_mesh (m d : ℕ) {D S ρ ε H V : ℝ} {M : ℕ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hM : 0 < M) (hMS : (M : ℝ) ≤ S)
    (hH : modeResidueSideThreshold m d D S ρ ε ≤ H)
    (hV : 0 < V) (hwidth : ρ * H ≤ V) :
    1 ≤ V / M ∧ 1 / (V / M) ≤ modeRemovalMesh d := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ := modeRemovalMesh_pos d
  have hu : (M : ℝ) / modeRemovalMesh d ≤ V :=
    (div_le_div_of_nonneg_right hMS hδ.le).trans
      (((modeResidueSideThreshold_bounds m d hD hS hρ hε).2.trans
        (mul_le_mul_of_nonneg_left hH hρ.le)).trans hwidth)
  apply modeRemovalMesh_of_width d (div_pos hV hm)
  apply (le_div_iff₀ hm).mpr
  calc
    (1 / modeRemovalMesh d) * M = (M : ℝ) / modeRemovalMesh d := by ring
    _ ≤ V := hu

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothWeight_pos_of_threshold {K I : Type*} [Fintype K] [Fintype I]
    (m : ℕ) {D S ρ ε : ℝ} (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j) (hbound : ∀ j, (modulus j : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ j, modeResidueSideThreshold m (Fintype.card (K × I)) D S ρ ε ≤ H j)
    (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    0 < ∑' x, selectedResidueSmoothWeight modulus G V x := by
  let d := Fintype.card (K × I)
  have hv z : 1 ≤ residueProfileWidth modulus V z ∧
      1 / residueProfileWidth modulus V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hmodulus z.2) (hbound z.2)
      (hsize z.2) (hV z) (hwidth z)
  apply selectedResidueSmoothWeight_mass_pos modulus G hG V hV
  intro r
  rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
  have hlower := shiftedSmoothProductMass_lower
    (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  exact (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos modulus V hmodulus hV z))
    (by norm_num)).trans_le hlower

end Erdos3

end

section

namespace Erdos3

open Polynomial

theorem exists_mode_residue_threshold_exp_budget (m : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F D S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ D → D ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeResidueSideThreshold m d D S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F D S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hbase⟩ := exists_mode_threshold_exp_budget m
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + C K₀) ^ K₀ + (2 * X + modeProfileLogPolynomial + 3) + 1)
  refine ⟨K, hK, ?_⟩
  intro n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  obtain ⟨hs, hr⟩ := hbase n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  have hprof := modeProfileLog_nonneg hP
  have hδ := modeRemovalMesh_pos d
  have he : S / (ρ * modeRemovalMesh d) ≤ Real.exp (2 * P + modeProfileLog P + 3) := by
    calc
      _ = S * (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (modeProfileLog P + 3) := by
        gcongr
        exact modeRemovalMesh_inv_le_exp d hP hd
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp : (P + K₀) ^ K₀ + (2 * P + modeProfileLog P + 3) + 1 ≤ (P + K) ^ K := by
    simpa [Polynomial.eval₂_pow, modeProfileLogPolynomial_eval] using hpoly P hP
  have hb0 : 0 ≤ (P + K₀) ^ K₀ := by positivity
  constructor
  · exact (add_le_exp_add_one hb0 (by linarith) hs he).trans (Real.exp_le_exp.mpr hp)
  · exact hr.trans (Real.exp_le_exp.mpr (by linarith))

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open Polynomial

theorem exists_cube_residue_threshold_exp_budget (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F L S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ L → L ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeResidueSideThreshold m d (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hbase⟩ := exists_cube_mode_threshold_exp_budget m q
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + C K₀) ^ K₀ + (2 * X + modeProfileLogPolynomial + 3) + 1)
  refine ⟨K, hK, ?_⟩
  intro n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  obtain ⟨hs, hr⟩ := hbase n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  have hprof := modeProfileLog_nonneg hP
  have hδ := modeRemovalMesh_pos d
  have he : S / (ρ * modeRemovalMesh d) ≤ Real.exp (2 * P + modeProfileLog P + 3) := by
    calc
      _ = S * (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (modeProfileLog P + 3) := by
        gcongr
        exact modeRemovalMesh_inv_le_exp d hP hd
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp : (P + K₀) ^ K₀ + (2 * P + modeProfileLog P + 3) + 1 ≤ (P + K) ^ K := by
    simpa [Polynomial.eval₂_pow, modeProfileLogPolynomial_eval] using hpoly P hP
  have hb0 : 0 ≤ (P + K₀) ^ K₀ := by positivity
  constructor
  · exact (add_le_exp_add_one hb0 (by linarith) hs he).trans (Real.exp_le_exp.mpr hp)
  · exact hr.trans (Real.exp_le_exp.mpr (by linarith))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_cube_residue_removal_at_error {I K : Type*}
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
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      (cubeModePolynomialBudget q L) S ρ ε ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C (cubeModePolynomialBudget q L) S ρ ε ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  classical
  let d := Fintype.card (Option K × I)
  let D := cubeModePolynomialBudget q L
  let T := modeRemovalShrink m d D ρ ε
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := affine_cube_residue_removal_of_widths U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε) hT hS hstride H hH hsize' hrank hR
    Q hQ test htest residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε).le hwidth
    (modeRemovalShrink_move m d hρ hε) (modeRemovalBeta_pos hε).le (fun i => modeRemovalBias_le i hε)
  exact hout.trans (modeRemovalError_bound d hε)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem anchored_affine_cube_residue_removal_at_error {I K : Type*}
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
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      (cubeModePolynomialBudget q L) S ρ ε ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C (cubeModePolynomialBudget q L) S ρ ε ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => ((anchor + residueLatticeArray residue stride z) (k, j) : ℝ))‖ ≤ ε := by
  classical
  let d := Fintype.card (Option K × I)
  let D := cubeModePolynomialBudget q L
  let T := modeRemovalShrink m d D ρ ε
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := anchored_affine_cube_residue_removal_of_widths anchor U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε) hT hS hstride H hH hsize' hrank hR
    Q hQ test htest residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε).le hwidth
    (modeRemovalShrink_move m d hρ hε) (modeRemovalBeta_pos hε).le (fun i => modeRemovalBias_le i hε)
  exact hout.trans (modeRemovalError_bound d hε)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_amplitude_residue_removal_at_error {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (F : (Option K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      1 S ρ (modeAmplitudeAccuracy Lip ε) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C 1 S ρ (modeAmplitudeAccuracy Lip ε) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤ ε := by
  classical
  let ε₀ := modeAmplitudeAccuracy (Lip : ℝ) ε
  have hε₀ : 0 < ε₀ := modeAmplitudeAccuracy_pos Lip.coe_nonneg hε
  let d := Fintype.card (Option K × I)
  let D : ℝ := 1
  let T := modeRemovalShrink m d D ρ ε₀
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε₀)
  have hD : 0 ≤ D := zero_le_one
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε₀)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε₀)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε₀
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε₀ ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε₀).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε₀ (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := affine_coefficient_residue_removal_of_widths_lipschitz_amplitude U hC frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε₀) hT hS hstride H hH hsize' hrank hR
    residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε₀).le hwidth
    (modeRemovalShrink_move m d hρ hε₀) (modeRemovalBeta_pos hε₀).le (fun i => modeRemovalBias_le i hε₀) F hF hLip
  exact hout.trans (modeAmplitudeError_bound d Lip.coe_nonneg hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_residue_uniform_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hbudget⟩ := exists_cube_residue_threshold_exp_budget m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P C L S ρ ε hP hn hd hC hCP hL hLP hS hSP hρ hρP hε hεP
  exact affine_cube_residue_removal_at_error U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride H (fun k => hside.trans (hsize k)) hrank
    (hrankBudget.trans hR) Q hQ test htest residue V hV hwidth

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_ambient_residue_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_cube_residue_uniform_removal m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  obtain ⟨hZ, hrem⟩ := hremove hP hn hd U root difference hlin hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [residueSmoothPMF_expectation]
  exact hrem

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_congruence_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_cube_ambient_residue_removal m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  have hh (r : G) := hremove hP hn hd U root difference hlin hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest (columnResidueRepresentative stride r.val) V hV hwidth
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

def affineCubeModeFactors {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : Prop :=
  ∀ j, ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
    ∀ P, Homogeneous (j.val + 1) P →
      affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
        (map (U j).subtype P) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P)

theorem not_affineCubeModeFactors_iff {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    ¬affineCubeModeFactors U root difference frequency ↔
      ∃ j, ¬∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
        ∀ P, Homogeneous (j.val + 1) P →
          affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
            (map (U j).subtype P) = M (VectorPolynomial.siteEvaluation
              (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P) := by
  classical
  simp only [affineCubeModeFactors, not_forall]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem affineCubeModeFactors_bounded {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hf : affineCubeModeFactors U root difference frequency) (j : Fin m) :
    ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          M (VectorPolynomial.siteEvaluation (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p) := by
  obtain ⟨M, hM⟩ := hf j
  refine ⟨M, homogeneous_factorization_to_bounded_site (U j) (j.val + 1)
    (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
    (fun d a => (frequency j d a : ℝ)) M ?_⟩
  have hsite : (fun s (k : Option K) => k.elim (1 : ℝ)
      (fun t => ((affineSite root difference s (some t) : ℤ) : ℝ))) =
      (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) := by
    funext s k
    cases k <;> simp [affineSite, Int.cast_sum]
  simpa only [hsite] using hM

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem exists_retained_affine_layer_cover :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K : Type*} [Fintype K] {m q : ℕ}
    (j : Fin m) (root : K → ℤ) (difference : Fin q → K → ℤ)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hE : ∀ s d, RationalHeightLE
      (boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k)) s d : ℚ) H)
    {P : ℝ} (_hP : 0 ≤ P)
    (_hD : (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ) ≤ P)
    (_hS : (Fintype.card (Finset (Fin q)) : ℝ) ≤ P) (_hHP : (H : ℝ) ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {J : Fin m → Type*} [∀ i, Fintype (J i)]
    (U : ∀ i, Submodule ℝ (J i → ℝ)) (frequency : ∀ i, (K →₀ ℕ) → J i → ℤ)
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (_hfrequency : ∀ d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hretained : affineCubeModeFactors U root difference frequency),
    ∃ b : Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ s a, |(b s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        CircleFourier.character
          (coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) : CircleFourier.Circle) =
        subspaceArrayCharacter (U j) b
          (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
            ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
              (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p)) := by
  obtain ⟨A, hA, hcover⟩ := exists_polynomial_site_cover
  refine ⟨A, hA, ?_⟩
  intro K _ m q j root difference H hH hE P hP hD hS hHP
  obtain ⟨D, hDpos, hDP, hrows⟩ := hcover (j.val + 1)
    (fun s k => affineSite root difference s (some k)) hH hE hP hD hS hHP
  refine ⟨D, hDpos, hDP, ?_⟩
  intro J _ U frequency C hC hCP hfrequency hretained
  obtain ⟨M, hM⟩ := affineCubeModeFactors_bounded U root difference frequency hretained j
  exact hrows (U j) (frequency j) hC hCP hfrequency M hM

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial Polynomial
open scoped BigOperators Classical

theorem exists_retained_affine_common_cover (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hE : ∀ (j : Fin m) s d, RationalHeightLE
      (boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k)) s d : ℚ) H)
    {P : ℝ} (_hP : 0 ≤ P)
    (_hD : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ) ≤ P)
    (_hS : (Fintype.card (Finset (Fin q)) : ℝ) ≤ P) (_hHP : (H : ℝ) ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {J : Fin m → Type*} [∀ i, Fintype (J i)]
    (U : ∀ i, Submodule ℝ (J i → ℝ)) (frequency : ∀ i, (K →₀ ℕ) → J i → ℤ)
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (_hfrequency : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hretained : affineCubeModeFactors U root difference frequency),
    ∃ b : ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ j s a, |(b j s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) (p : VectorPolynomial K ℝ (U j)), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        CircleFourier.character
          (coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) : CircleFourier.Circle) =
        subspaceArrayCharacter (U j) (b j)
          (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
            ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
              (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p)) := by
  obtain ⟨A₀, _, hcover⟩ := exists_retained_affine_layer_cover
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget (C (m + 1) * (X + C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro K _ q root difference H hH hE P hP hD hS hHP
  choose D hDpos hDP hrows using fun j : Fin m =>
    hcover j root difference hH (hE j) hP (hD j) hS hHP
  have hB : 0 ≤ (P + A₀) ^ A₀ := by positivity
  have hbud : ((m : ℝ) + 1) * (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hprod : (((∏ j, D j) : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * (P + A₀) ^ A₀) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _j : Fin m, Real.exp ((P + A₀) ^ A₀) :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hDP j)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  refine ⟨∏ j, D j, Finset.prod_pos (fun j _ => hDpos j),
    hprod.trans (Real.exp_le_exp.mpr (by nlinarith)), ?_⟩
  intro J _ U frequency C hC hCP hfrequency hretained
  choose b hb hchar using fun j => hrows j U frequency hC hCP (hfrequency j) hretained
  refine ⟨(fun j s a => (complementaryPeriod D j : ℤ) * b j s a), ?_, ?_⟩
  · intro j s a
    rw [Int.cast_mul, Int.cast_natCast, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ complementaryPeriod D j from Nat.cast_nonneg _)]
    calc
      _ ≤ (complementaryPeriod D j : ℝ) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_left (hb j s a) (Nat.cast_nonneg _)
      _ ≤ (((∏ i, D i) : ℕ) : ℝ) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (complementaryPeriod_le_product D hDpos j))
          (Real.exp_pos _).le
      _ ≤ Real.exp ((m : ℝ) * (P + A₀) ^ A₀) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ = Real.exp (((m : ℝ) + 1) * (P + A₀) ^ A₀) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((P + A) ^ A) := Real.exp_le_exp.mpr hbud
  · intro j p hp
    exact (hchar j p hp).trans (subspaceArrayCharacter_common_period D hDpos j (U j) (b j)
      (VectorPolynomial.siteEvaluation (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p)).symm

end Erdos3.BooleanCubeKernel

end

end OAI
