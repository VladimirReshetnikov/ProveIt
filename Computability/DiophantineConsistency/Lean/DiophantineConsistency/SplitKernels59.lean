import DiophantineConsistency.SplitCertificate59
import DiophantineConsistency.SplitKernelData59

/-! # The literal three kernels equal the extracted source channels -/
namespace DiophantineConsistency.SplitKernels59
open Polynomial SidonPositions SelectiveQuadraticCoding DegreeSeparatedCoding
open SplitCertificate59
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
variable {R : Type*} [CommRing R]

noncomputable abbrev D0 (ports : Fin 4 → R) : R[X] := SplitKernelData59.D0 ports
noncomputable abbrev D1 (ports : Fin 4 → R) : R[X] := SplitKernelData59.D1 ports
noncomputable abbrev D2 (ports : Fin 4 → R) : R[X] := SplitKernelData59.D2 ports

theorem D0_eq (ports : Fin 4 → R) :
    D0 ports = constantCombined (constantCoefficient ports) targets := by
  simp [D0,SplitKernelData59.D0,SplitKernelData59.sparseKernel,
    SplitKernelData59.positions0,SplitKernelData59.coefficients0,
    constantCombined,constantCoefficient,targets,Fin.sum_univ_succ]
  <;> ring_nf
  <;> simp only [map_add,map_sub,map_neg]
  <;> ring

theorem D1_eq (ports : Fin 4 → R) :
    D1 ports = linearCombined weights linearSupport (linearCoefficient ports) targets := by
  simp [D1,SplitKernelData59.D1,SplitKernelData59.sparseKernel,
    SplitKernelData59.positions1,SplitKernelData59.coefficients1,
    linearCombined,linearComplementary,linearCoefficient,linearSupport,
    targets,weights,Fin.sum_univ_succ]
  <;> ring_nf
  <;> simp only [map_add,map_sub,map_neg]
  <;> ring

theorem D2_eq (ports : Fin 4 → R) :
    D2 ports = combined weights quadraticSupport (quadraticCoefficient ports) targets := by
  simp [D2,SplitKernelData59.D2,SplitKernelData59.sparseKernel,
    SplitKernelData59.positions2,SplitKernelData59.coefficients2,
    combined,complementary,quadraticCoefficient,quadraticSupport,quadraticIndices,
    activePair,targets,weights,SelectiveQuadraticCoding.pairWeight,
    QuadraticCoding.correction,Fin.sum_univ_succ]
  <;> ring_nf
  <;> simp only [map_add,map_sub,map_neg]
  <;> ring

noncomputable def sourcePolynomial (ports : Fin 4 → R) (x : Fin 31 → R) : R[X] :=
  encoded weights x ^ 2 * D2 ports + encoded weights x * D1 ports + D0 ports

theorem sourcePolynomial_eq (ports : Fin 4 → R) (x : Fin 31 → R) :
    sourcePolynomial ports x = product weights x (constantCoefficient ports)
      linearSupport (linearCoefficient ports) quadraticSupport (quadraticCoefficient ports)
      targets := by
  rw [sourcePolynomial,D0_eq,D1_eq,D2_eq]
  rfl

theorem coeff_sourcePolynomial (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    (sourcePolynomial ports x).coeff (targets k) = 2*deliveredRows ports x k := by
  rw [sourcePolynomial_eq,SplitCertificate59.coeff_source_rows]

theorem sourcePolynomial_zero_iff (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ) :
    (∀ k,(sourcePolynomial ports x).coeff (targets k) = 0) ↔
      ∀ k,sourceRows ports x k = 0 := by
  simp_rw [sourcePolynomial_eq]
  exact coeff_zero_iff_source_zero ports x

theorem degree_encoded (x : Fin 31 → R) : (encoded weights x).natDegree ≤ 116 := by
  exact SelectiveCarry.encoded_degree_le weights x 116 maximum_weight

theorem degree_sourcePolynomial (ports : Fin 4 → R) (x : Fin 31 → R) :
    (sourcePolynomial ports x).natDegree ≤ 2161 := by
  unfold sourcePolynomial
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · exact (natDegree_mul_le).trans (add_le_add
        (natDegree_pow_le_of_le 2 (degree_encoded x)) (SplitKernelData59.degree_D2 ports))
    · exact (natDegree_mul_le).trans ((add_le_add
        (degree_encoded x) (SplitKernelData59.degree_D1 ports)).trans (by decide))
  · exact (SplitKernelData59.degree_D0 ports).trans (by decide)

theorem kernelBounds_pow (ports : Fin 4 → ℤ) (p q : ℕ)
    (hp : 1 ≤ p) (hpq : p+4 ≤ q)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2^p)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2^q)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2^p)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*2^p) :
    SplitWordBounds.KernelBounds (D0 ports) (D1 ports) (D2 ports) (2^(p+q+1)) := by
  have hB : (2 : ℤ) ≤ 2^p := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hp)
  have hK : 16*(2 : ℤ)^p ≤ 2^q := by
    calc
      16*(2 : ℤ)^p = 2^(p+4) := by rw [pow_add]; norm_num; ring
      _ ≤ 2^q := pow_le_pow_right₀ (by norm_num) hpq
  have he : 2*(2 : ℤ)^p*2^q = 2^(p+q+1) := by
    rw [pow_add,pow_add]
    ring
  rw [← he]
  exact SplitKernelData59.kernelBounds_box ports _ _ hB hK hb hk hm hf

theorem source_one_not_zero (ports : Fin 4 → ℤ) :
    sourceRows ports (fun _ => 1) 9 = -7 := by
  change (-3 : ℤ)+1+(-4)*1+(-1)*(1^2) = -7
  norm_num

theorem source_zero_has_nonzero_digit (ports : Fin 4 → ℤ) (z : Fin 31 → ℕ)
    (hsource : ∀ k, sourceRows ports (fun i => (z i : ℤ)+1) k = 0) :
    ∃ i, 0 < z i := by
  by_contra hn
  have hz : ∀ i, z i = 0 := by
    intro i
    have hi : ¬ 0 < z i := fun h => hn ⟨i,h⟩
    omega
  have he : (fun i => (z i : ℤ)+1) = (fun _ => 1) := by
    funext i
    rw [hz i]
    norm_num
  have h := hsource 9
  rw [he,source_one_not_zero] at h
  norm_num at h

end DiophantineConsistency.SplitKernels59
