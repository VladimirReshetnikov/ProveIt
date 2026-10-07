import OAI.Combinatorics.Progressions.Estimates.LowerStepSquare
import OAI.Combinatorics.Progressions.Linear.BoundedAdaptedBasis

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}

def topSubspaceIdeal (F : NilpotentLieFiltration L s) (K : Submodule ℚ L)
    (hK : K ≤ F.layer s) : LieIdeal ℚ L :=
  { K with
    lie_mem := by
      intro x y hy
      rw [← lie_skew, F.top_layer_central (hK hy) x, neg_zero]
      exact K.zero_mem }

theorem exists_bounded_adapted_basis_with_top_subspace
    (F : NilpotentLieFiltration L s) (hs : 1 ≤ s) (e : Basis ι ℚ L)
    {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    (K : Submodule ℚ L) (hK : K ≤ F.layer s) {κ : Type*} (vK : κ → K)
    (hspanK : Submodule.span ℚ (Set.range vK) = ⊤) {H : ℕ}
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H)
    (hvK : ∀ j k, RationalHeightLE (e.repr (vK j : L) k) H) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (S : Set (Fin (finrank ℚ L))),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ j k, RationalHeightLE (e.repr (b j) k) H) ∧
      (∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) ∧
      K = Submodule.span ℚ (b '' S) := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  let bounded : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let flag : Fin (s + 1) → Submodule ℚ L := fun i => if i.val < s then F.layer (i.val + 1) else K
  have hflag : Antitone flag := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    dsimp only [flag]
    split_ifs with hi hj
    · exact F.antitone (Nat.add_le_add_right hij 1)
    · omega
    · exact hK.trans (F.antitone (by omega))
    · exact le_rfl
  have hbounded (i : Fin (s + 1)) :
      Submodule.span ℚ (bounded ∩ (flag i : Set L)) = flag i := by
    dsimp only [flag]
    split_ifs with hi
    · exact span_inter_eq_of_spanning_family _ (v i) (hspan i) bounded (hv i)
    · exact span_inter_eq_of_spanning_family K vK hspanK bounded hvK
  have hzero : flag 0 = ⊤ := by
    simpa only [flag, Fin.val_zero, show 0 < s by omega, ite_true, Nat.zero_add] using F.one_eq_top
  have htotal : Submodule.span ℚ bounded = ⊤ := by
    apply top_unique
    rw [← hzero, ← hbounded 0]
    exact Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, u, hu, hub, hbb, hbf⟩ :=
    exists_sorted_flag_basis_from_spanning_set flag hflag bounded htotal hbounded
  let w := fun i => min s (u i)
  have hw : Monotone w := fun i j hij => min_le_min le_rfl (hu hij)
  have hlayers (i : Fin (s + 1)) :
      F.layer (i.val + 1) = Submodule.span ℚ (b '' {j | i.val < w j}) := by
    by_cases hi : i.val < s
    · have h := hbf i
      simp only [flag, hi, ite_true] at h
      simpa only [w, lt_min_iff, hi, true_and] using h
    · have his : i.val = s := by omega
      rw [his, F.terminal]
      have hempty : {j | s < w j} = (∅ : Set (Fin (finrank ℚ L))) := by
        ext j
        simp [w]
      rw [hempty, Set.image_empty, Submodule.span_empty]
  have hlayer := F.layer_eq_span_of_weighted_flag b w (fun j =>
    (min_le_left s (u j)).trans (Nat.le_succ s)) hlayers
  refine ⟨b, w, {i | s < u i}, hw,
    centralLieBasis_of_sorted_filtration F b w hw hlayer, hbb, hlayer, ?_⟩
  simpa only [flag, lt_self_iff_false, ite_false] using hbf ⟨s, Nat.lt_succ_self s⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
