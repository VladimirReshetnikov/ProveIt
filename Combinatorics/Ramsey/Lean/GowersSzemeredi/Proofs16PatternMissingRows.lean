import GowersSzemeredi.Proofs16CommonNeighborhoodWitnesses
import GowersSzemeredi.Proofs16FourRowCompletion
import GowersSzemeredi.Proofs16VarietyRegularStep

/-! Turn common-neighborhood witnesses into a quantitative bound on the
missing part of each row after two vertical differences. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def patternEdge {N m : Nat} [NeZero N] (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) (eta : Real) {F C : Finset (ZMod N)}
    (d : ↥F) (t : ↥C) : Prop :=
  (d : ZMod N) ∈ bohr (varyingPatternFrequencies psi J t) eta

def patternRepresentationTriples {N : Nat} [NeZero N]
    (W C : Finset (ZMod N)) (y : ZMod N) : Finset (Fin 3 → ↥C) :=
  Finset.univ.filter fun q => (∀ i, (q i : ZMod N) ∈ W) ∧
    (q 0 : ZMod N) + q 1 - q 2 - y ∈ W

/-- A quasirandom pattern graph and many additive representations imply
that only a controlled part of the target Bohr row can be missing. -/
theorem pattern_missing_row_bound {N m : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (W C T F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (a y : ZMod N)
    {rho eta delta epsilon tau : Real} (hrho : 0 ≤ rho) (heta : 0 ≤ eta) (hC : C.Nonempty)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon) (htau : 0 ≤ tau)
    (hW : W ⊆ bohr T (rho / 4))
    (hpsi : ∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0)
    (hgeom : ∀ t ∈ W, ∀ d ∈ bohr F eta,
      d ∈ bohr (varyingPatternFrequencies psi J t) eta → (d, a + t) ∈ A)
    (hbox : boxSum (fun (d : ↥(bohr F eta)) (t : ↥C) =>
        edgeIndicator (patternEdge psi J (eta / 4)) d t - delta) ≤
      epsilon^4 * ((bohr F eta).card : Real)^2 * (C.card : Real)^2)
    (hM : tau * (C.card : Real)^3 ≤
      ((patternRepresentationTriples W C y).card : Real)) :
    (((bohr (F ∪ varyingPatternFrequencies psi J y) (eta / 4)) \
      rowOf (verDiff (verDiff A)) y).card : Real) * (delta^3 * tau)^2 ≤
      12 * epsilon * (bohr F eta).card := by
  let B := bohr F eta
  let M := patternRepresentationTriples W C y
  let E : ↥B → ↥C → Prop := patternEdge psi J (eta / 4)
  letI : Nonempty ↥C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
  have hcount := vertex_no_witness_card E hd0 hd1 heps htau
    (by simpa only [Fintype.card_coe] using hbox) M
    (by simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow] using hM)
  let missing := (bohr (F ∪ varyingPatternFrequencies psi J y) (eta / 4)) \
    rowOf (verDiff (verDiff A)) y
  let bad := Finset.univ.filter fun d : ↥B => ¬ ∃ q ∈ M, ∀ j, E d (q j)
  have hparts (d : ZMod N) (hd : d ∈ missing) :
      d ∈ B ∧ d ∈ bohr (varyingPatternFrequencies psi J y) (eta / 4) := by
    have h := (Finset.mem_sdiff.mp hd).1
    rw [bohr_union] at h
    exact ⟨bohr_mono_radius F (show eta / 4 ≤ eta by linarith) (Finset.mem_inter.mp h).1,
      (Finset.mem_inter.mp h).2⟩
  have hbad (d : ZMod N) (hd : d ∈ missing) : (⟨d, (hparts d hd).1⟩ : ↥B) ∈ bad := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rintro ⟨q, hq, hqE⟩
    have hqW := (Finset.mem_filter.mp hq).2
    have hmem := recentered_four_row_of_triple A W T F psi J a hrho heta hW hpsi hgeom
      (hparts d hd).1 (hparts d hd).2
      ⟨q 0, hqW.1 0, q 1, hqW.1 1, q 2, hqW.1 2, hqW.2, hqE 0, hqE 1, hqE 2⟩
    exact (Finset.mem_sdiff.mp hd).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
  have hcard : missing.card ≤ bad.card := by
    apply Finset.card_le_card_of_injective (f := fun d : ↥missing =>
      (⟨⟨d.val, (hparts d.val d.property).1⟩, hbad d.val d.property⟩ : ↥bad))
    intro d e h
    exact Subtype.ext (congrArg (fun u : ↥bad => (u.val : ZMod N)) h)
  have hcount' : (bad.card : Real) * (delta^3 * tau)^2 ≤
      12 * epsilon * B.card := by
    convert hcount using 1 <;> norm_num [bad, Fintype.card_coe]
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)).trans hcount'

end LeanProofs.GowersSzemeredi
