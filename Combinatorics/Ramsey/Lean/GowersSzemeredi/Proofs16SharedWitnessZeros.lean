import GowersSzemeredi.Proofs16WitnessProjection
import GowersSzemeredi.Proofs16CommonWitnesses
import GowersSzemeredi.Proofs16PrimeColumnIdentities

/-! Common column witnesses give a dense zero set for a quadruple defect.
The value identities use the original bihomomorphism, not just geometry. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A witness system records both represented values and membership in
the original set. -/
def IsColumnWitnessSystem {N : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
    (rho : Real) : Prop :=
  ∀ x ∈ X, ∀ z ∈ W x,
    (∀ j, (x, z j) ∈ A) ∧ fourSum z ∈ bohr (T x) rho ∧
      L x (fourSum z) = repFourValue (fun y => phi (x, y)) z

/-- A common witness makes the column defect vanish at its represented
point, by horizontal Freiman linearity of the original map. -/
theorem common_witness_defect_zero {N : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
    {rho : Real} (hphi : IsEBihomomorphism A phi {0})
    (hsys : IsColumnWitnessSystem A phi X T L W rho)
    (q : Fin 4 → ZMod N) (hqX : ∀ i, q i ∈ X) (hq : IsAdditiveQuadruple q)
    (z : Fin 4 → ZMod N) (hz : z ∈ commonWitnesses W q) :
    fourSum z ∈ bohr (columnQuadrupleSpectrum T q) rho ∧
      columnQuadrupleDefect L q (fourSum z) = 0 := by
  have hzW : ∀ i, z ∈ W (q i) := by
    simpa only [commonWitnesses, Finset.mem_filter, Finset.mem_univ, true_and] using hz
  have hdata := fun i => hsys (q i) (hqX i) z (hzW i)
  refine ⟨(mem_bohr_family_union (fun i => T (q i)) rho _).mpr (fun i => (hdata i).2.1), ?_⟩
  have hrow (j : Fin 4) :
      phi (q 0, z j) + phi (q 1, z j) - phi (q 2, z j) - phi (q 3, z j) = 0 := by
    exact Set.mem_singleton_iff.mp (hphi.1 (q 0) (q 1) (q 2) (q 3) (z j) hq
      ((hdata 0).1 j) ((hdata 1).1 j) ((hdata 2).1 j) ((hdata 3).1 j))
  dsimp only [columnQuadrupleDefect]
  rw [(hdata 0).2.2, (hdata 1).2.2, (hdata 2).2.2, (hdata 3).2.2]
  dsimp only [repFourValue]
  linear_combination hrow 0 + hrow 1 - hrow 2 - hrow 3

/-- Many common witnesses produce an ambient-dense zero set in the
intersection of the original column domains. -/
theorem common_witness_dense_zero_set {N : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
    {rho theta : Real} (hphi : IsEBihomomorphism A phi {0})
    (hsys : IsColumnWitnessSystem A phi X T L W rho)
    (q : Fin 4 → ZMod N) (hqX : ∀ i, q i ∈ X) (hq : IsAdditiveQuadruple q)
    (hcount : theta * (N : Real)^4 ≤ (commonWitnesses W q).card) :
    ∃ Z : Finset (ZMod N), Z ⊆ bohr (columnQuadrupleSpectrum T q) rho ∧
      theta * N ≤ Z.card ∧ ∀ y ∈ Z, columnQuadrupleDefect L q y = 0 := by
  refine ⟨(commonWitnesses W q).image fourSum, ?_, fourSum_image_density _ hcount, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact (common_witness_defect_zero A phi X T L W hphi hsys q hqX hq z hz).1
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact (common_witness_defect_zero A phi X T L W hphi hsys q hqX hq z hz).2

end LeanProofs.GowersSzemeredi
