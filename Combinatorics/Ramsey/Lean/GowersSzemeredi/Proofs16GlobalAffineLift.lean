import GowersSzemeredi.Proofs16FiniteCoverPadding

/-! # Global assembly of the verified affine lift

All cells of the line-cover partition use one sampling budget and one
integer base scale. Local candidate families are padded to a common count,
their proper partitions are flattened, and the original exceptional set
is intersected with the union of the new good sets.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem Section16LineCover.global_affine_lift {N k q r m : Nat} [Fact N.Prime]
    {P : Box N (k + 1)} {B : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {σ l gamma s : ℝ}
    (hline : Section16LineCover P B phi σ l q)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (hk : 0 < k) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s)
    (hm : (m : ℝ) ≤ l) (τ ε : ℝ) (hq : 0 < q)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ ^ 2) :
    let b := (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s)
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : ℝ) ≤ (r : ℝ) * b + (r : ℝ) * r * b * b ∧
      H ⊆ P.carrier ∧ (1 - σ - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, Real.sqrt (((m : ℝ) / 8) ^
        ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s))) / 4 ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  classical
  dsimp only
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hSpart, hSproper, hproduct, hwidth, hell, hc⟩ := hline
  have hlocal : ∀ u, ∃ (p : Nat) (G : Finset (Point N (k + 1)))
      (L : Nat) (R : Fin L → Box N (k + 1))
      (nu : Fin L → ((Fin r × Fin p) ⊕ (Fin r × Fin r × Fin p × Fin p)) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
      G ⊆ (S u).carrier ∧ (1 - 2 * τ - ε) * ((S u).carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition R (S u) ∧
      (∀ j, (R j).IsProper ∧ Real.sqrt (((m : ℝ) / 8) ^
        ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s))) / 4 ≤ (R j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j z, z ∈ (R j).carrier → z ∈ B ∩ E → z ∈ G → ∃ ij, phi z = nu j ij z := by
    intro u
    apply section16_local_affine_lift_all_scales (S u) (hSproper u) hk
      (by exact_mod_cast hm.trans (hwidth u)) B (B ∩ E) Finset.inter_subset_left
      phi gamma s hg hg1 hsections hs (ell u) (hell u) ?_ τ ε hq hτ hτ1 hε hε1 hr
    intro h x hxS hxD
    have hxprod := hxS
    rw [appendCoordinate_eq_snoc] at hxprod
    have hh := ((hproduct u).mem_snoc h x).mp hxprod |>.1
    obtain ⟨hxB, hxE⟩ := Finset.mem_inter.mp hxD
    exact hc u h x hh hxB hxE hxS
  choose p G L R nu hp hG hGm hRpart hRproper hnu hcov using hlocal
  let b := (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s)
  let pmax := Nat.floor b
  let n := r * pmax + r * r * pmax * pmax
  have hrpos : 0 < r := by
    by_contra hz
    have hz' : r = 0 := by omega
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [hz', Nat.cast_zero, zero_mul] at hr
    linarith
  have hb : 1 ≤ b := (section16_slice_control_ranges (k := k) hrpos hs hg hg1 hε hε1).2.2
  have hpmax : (pmax : ℝ) ≤ b := Nat.floor_le (zero_le_one.trans hb)
  have hpn (u : Fin M) :
      Fintype.card ((Fin r × Fin (p u)) ⊕ (Fin r × Fin r × Fin (p u) × Fin (p u))) ≤ n :=
    section16_recovered_candidate_mono (Nat.le_floor (hp u))
  have hgood := IsPartition.good_union hSpart G (2 * τ + ε) hG
    (fun u => by simpa only [sub_add_eq_sub_sub] using hGm u)
  have hmass := good_intersection_mass P.carrier E (Finset.univ.biUnion G)
    σ (2 * τ + ε) hE hgood.1 hEm hgood.2
  let e := section5NatFlattenEquiv L
  refine ⟨n, E ∩ Finset.univ.biUnion G, ∑ u, L u, boxFlatten L R,
    fun j => padFiniteMultilinearFamily (nu (e.symm j).1 (e.symm j).2) n,
    section16_recovered_candidate_bound hpmax, Finset.inter_subset_left.trans hE,
    ?_, boxFlatten_partition P S L R hSpart hRpart,
    fun j => (hRproper _ _).1, fun j => (hRproper _ _).2,
    fun j => padFiniteMultilinearFamily_isMultilinear _ (hnu _ _), ?_⟩
  · simpa only [sub_add_eq_sub_sub] using hmass
  · intro j z hzQ hzB hzH
    obtain ⟨hzE, hzG⟩ := Finset.mem_inter.mp hzH
    have hzS := IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2 hzQ
    have hzlocal := (IsPartition.good_union_mem_iff hSpart G hG (e.symm j).1 hzS).mp hzG
    apply padFiniteMultilinearFamily_covers _ (hpn _) z (phi z)
    exact hcov (e.symm j).1 (e.symm j).2 z hzQ (Finset.mem_inter.mpr ⟨hzB, hzE⟩) hzlocal

end LeanProofs.GowersSzemeredi
