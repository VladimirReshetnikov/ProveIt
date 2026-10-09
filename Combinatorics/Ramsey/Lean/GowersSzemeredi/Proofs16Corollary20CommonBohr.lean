import GowersSzemeredi.Proofs16Corollary20AllTriples

/-! Put the selected Freiman pieces on one Bohr neighborhood. The common
spectrum costs the sum of the individual ranks, without a radius loss.
The difference maps are normalized at zero and additive wherever the
arguments and their sum stay in the neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A finite family of Bohr extensions has a common neighborhood, with
rank bounded by the sum of the individual ranks. -/
theorem common_bohr_extensions {N m : Nat} [NeZero N]
    (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
    (S : Fin m → Finset (ZMod N)) {ρ R : Real}
    (hS : ∀ i, ((S i).card : Real) ≤ R)
    (hB : ∀ i, IsBHomomorphism (E i) (bohr (S i) ρ) (L i)) :
    ∃ T : Finset (ZMod N), (T.card : Real) ≤ m * R ∧
      ∀ i, IsBHomomorphism (E i) (bohr T ρ) (L i) := by
  refine ⟨Finset.univ.biUnion S, ?_, fun i => (hB i).mono_neighborhood ?_⟩
  · calc
      ((Finset.univ.biUnion S).card : Real) ≤ ∑ i, ((S i).card : Real) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, R := Finset.sum_le_sum fun i _ => hS i
      _ = m * R := by simp
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht => ?_⟩
    exact (Finset.mem_filter.mp hx).2 t
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ht⟩)

/-- On a neighborhood containing zero, the difference map of a nonempty
piece vanishes at zero and is locally additive. -/
theorem IsBHomomorphism.normalized_extension {N : Nat} {A B : Finset (ZMod N)}
    {f : ZMod N → ZMod N} (h : IsBHomomorphism A B f)
    (hA : A.Nonempty) (hB : (0 : ZMod N) ∈ B) :
    ∃ psi : ZMod N → ZMod N, FreimanHom 2 B psi ∧ psi 0 = 0 ∧
      (∀ x ∈ B, ∀ y ∈ B, x + y ∈ B → psi (x + y) = psi x + psi y) ∧
      (∀ x ∈ A, ∀ y ∈ A, x - y ∈ B → f x - f y = psi (x - y)) := by
  obtain ⟨psi, hpsi, hagree⟩ := h
  obtain ⟨a, ha⟩ := hA
  have hz : psi 0 = 0 := by simpa using (hagree a ha a ha (by simpa using hB)).symm
  refine ⟨psi, hpsi, hz, ?_, hagree⟩
  intro x hx y hy hxy
  have hlin := hpsi.isFreimanLinearOn (by decide)
  have heq := hlin x y (x + y) 0 hx hy hxy hB (by simp)
  simpa only [hz, add_zero] using heq.symm

/-- All-triples selection with one common Bohr neighborhood and explicit
normalized difference maps. The rank bound contains no floor or ceiling. -/
theorem corollary20_common_bohr {N : Nat} [NeZero N] [Fact N.Prime]
    (U : ZMod N → Finset (ZMod N)) (h0 : ∀ x, (0 : ZMod N) ∈ U x)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K) {ε : Real}
    (hε : 0 < ε) (hN : 8 / ε ≤ (N : Real)) :
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L psi : Fin m → ZMod N → ZMod N)
      (T : Finset (ZMod N)),
      m ≤ ⌊(K : Real) / corollary20Kappa (ε / 2) K⌋₊ + 1 ∧
      (T.card : Real) ≤ ((K : Real) / corollary20Kappa (ε / 2) K + 1) *
        (16 * (corollary20Kappa (ε / 2) K)^(-(2 : Real))) ∧
      (∀ i, FreimanHom 8 (E i) (L i) ∧ corollary20Kappa (ε / 2) K * N ≤ (E i).card ∧
        (∀ x ∈ E i, L i x ∈ U x) ∧
        FreimanHom 2 (bohr T (corollary20Kappa (ε / 2) K / (32 * Real.pi))) (psi i) ∧
        psi i 0 = 0 ∧
        (∀ x ∈ bohr T (corollary20Kappa (ε / 2) K / (32 * Real.pi)),
          ∀ y ∈ bohr T (corollary20Kappa (ε / 2) K / (32 * Real.pi)),
          x + y ∈ bohr T (corollary20Kappa (ε / 2) K / (32 * Real.pi)) →
          psi i (x + y) = psi i x + psi i y) ∧
        (∀ x ∈ E i, ∀ y ∈ E i,
          x - y ∈ bohr T (corollary20Kappa (ε / 2) K / (32 * Real.pi)) →
          L i x - L i y = psi i (x - y))) ∧
      ((Finset.univ.filter fun t => ∃ v, BadWitness U E L t v).card : Real) < ε * (N : Real)^3 := by
  obtain ⟨m, E, L, S, hm, hE, hbad⟩ := corollary20_bohr_all_triples U h0 hK1 hK hε hN
  let κ := corollary20Kappa (ε / 2) K
  have hk : 0 < κ := by
    dsimp [κ, corollary20Kappa]
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨T, hT, hB⟩ := common_bohr_extensions E L S
    (fun i => (hE i).2.2.2.1) (fun i => (hE i).2.2.2.2)
  have hzero : (0 : ZMod N) ∈ bohr T (κ / (32 * Real.pi)) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht => ?_⟩
    simp only [mul_zero, centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero]
    positivity
  have hnonempty (i : Fin m) : (E i).Nonempty := by
    apply Finset.card_pos.mp
    have hpos := (mul_pos hk hNR).trans_le (hE i).2.1
    exact_mod_cast hpos
  choose psi hpsi hz hadd hagree using fun i =>
    (hB i).normalized_extension (hnonempty i) hzero
  refine ⟨m, E, L, psi, T, hm, ?_, fun i =>
    ⟨(hE i).1, (hE i).2.1, (hE i).2.2.1, hpsi i, hz i, hadd i, hagree i⟩, hbad⟩
  have hmR : (m : Real) ≤ (K : Real) / κ + 1 := by
    have hm' : (m : Real) ≤ (⌊(K : Real) / κ⌋₊ : Real) + 1 := by exact_mod_cast hm
    have hf := Nat.floor_le (show (0 : Real) ≤ (K : Real) / κ by positivity)
    linarith
  exact hT.trans (mul_le_mul_of_nonneg_right hmR (by positivity))

end LeanProofs.GowersSzemeredi
