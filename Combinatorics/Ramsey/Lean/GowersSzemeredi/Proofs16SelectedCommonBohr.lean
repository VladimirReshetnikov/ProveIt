import GowersSzemeredi.Proofs16BohrRecentering

/-! A common neighborhood for only the active maps, and simultaneous
normalization on a dense cluster of a single parameter set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Taking the union over the active indices costs only their total rank. -/
theorem selected_common_bohr_extensions {N m : Nat} [NeZero N]
    (I : Finset (Fin m)) (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (S : Fin m → Finset (ZMod N))
    {rho R : Real} (hS : ∀ i ∈ I, ((S i).card : Real) ≤ R)
    (hB : ∀ i ∈ I, IsBHomomorphism (E i) (bohr (S i) rho) (L i)) :
    ∃ T : Finset (ZMod N), (T.card : Real) ≤ I.card * R ∧
      ∀ i ∈ I, IsBHomomorphism (E i) (bohr T rho) (L i) := by
  refine ⟨I.biUnion S, ?_, fun i hi => (hB i hi).mono_neighborhood ?_⟩
  · calc
      ((I.biUnion S).card : Real) ≤ ∑ i ∈ I, ((S i).card : Real) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ I, R := Finset.sum_le_sum fun i hi => hS i hi
      _ = I.card * R := by simp
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht => ?_⟩
    exact (Finset.mem_filter.mp hx).2 t (Finset.mem_biUnion.mpr ⟨i, hi, ht⟩)

/-- A single dense cluster works simultaneously for the selected maps.
Agreement is retained on every original domain pair whose difference
belongs to the common neighborhood. -/
theorem selected_common_bohr_cluster {N m : Nat} [NeZero N]
    (I : Finset (Fin m)) (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (S : Fin m → Finset (ZMod N))
    (V : Finset (ZMod N)) {rho R nu : Real}
    (hrho : 0 ≤ rho) (hnu : 0 < nu) (hV : nu * N ≤ V.card)
    (hE : ∀ i ∈ I, (E i).Nonempty)
    (hS : ∀ i ∈ I, ((S i).card : Real) ≤ R)
    (hB : ∀ i ∈ I, IsBHomomorphism (E i) (bohr (S i) rho) (L i)) :
    ∃ (T : Finset (ZMod N)) (a : ZMod N) (C : Finset (ZMod N))
      (psi : Fin m → ZMod N → ZMod N),
      (T.card : Real) ≤ I.card * R ∧ a ∈ C ∧ C ⊆ V ∧
      nu * (bohr T (rho / 2)).card ≤ (C.card : Real) ∧
      (∀ x ∈ C, ∀ y ∈ C, x - y ∈ bohr T rho) ∧
      ∀ i ∈ I, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        (∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
        ∀ x ∈ E i, ∀ y ∈ E i, x - y ∈ bohr T rho →
          L i x - L i y = psi i (x - y) := by
  obtain ⟨T, hT, hcommon⟩ := selected_common_bohr_extensions I E L S hS hB
  obtain ⟨a, C, ha, hCV, hC, hdiff⟩ := exists_dense_bohr_cluster V T hnu hrho hV
  have hex (i : Fin m) : ∃ psi : ZMod N → ZMod N,
      i ∈ I → FreimanHom 2 (bohr T rho) psi ∧ psi 0 = 0 ∧
        (∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi (x + y) = psi x + psi y) ∧
        ∀ x ∈ E i, ∀ y ∈ E i, x - y ∈ bohr T rho →
          L i x - L i y = psi (x - y) := by
    by_cases hi : i ∈ I
    · obtain ⟨psi, hpsi⟩ := (hcommon i hi).normalized_extension (hE i hi) (zero_mem_bohr T hrho)
      exact ⟨psi, fun _ => hpsi⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose psi hpsi using hex
  exact ⟨T, a, C, psi, hT, ha, hCV, hC, hdiff, hpsi⟩

end LeanProofs.GowersSzemeredi
