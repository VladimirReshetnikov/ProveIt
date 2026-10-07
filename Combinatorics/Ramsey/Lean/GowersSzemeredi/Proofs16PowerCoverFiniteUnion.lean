import GowersSzemeredi.Proofs16PowerCoverUnion

/-! A quantitative common refinement for a finite family of power covers.
The recursive threshold records every intermediate minimum-width condition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16PowerIterationThreshold (T e : Real) : Nat → Real
  | 0 => 1
  | n + 1 => section16PowerUnionThreshold (section16PowerIterationThreshold T e n) T (e ^ n)

theorem LargeBoxMultilinearCover.loss_mono {N k : Nat} [NeZero N]
    {Gamma : Finset (Point N k × ZMod N)} {rho sigma C e T : Real}
    (h : LargeBoxMultilinearCover Gamma rho C e T) (hrs : rho ≤ sigma) :
    LargeBoxMultilinearCover Gamma sigma C e T := by
  intro P hP hT
  obtain ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu, hc⟩ := h P hP hT
  refine ⟨M, q, H, Q, mu, hH, ?_, hp, hproper, hq, hw, hmu, hc⟩
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 - sigma ≤ 1 - rho)
    (Nat.cast_nonneg _)).trans hm

theorem section16_empty_power_cover {N k : Nat} [NeZero N] :
    LargeBoxMultilinearCover (∅ : Finset (Point N k × ZMod N)) 0 0 1 1 := by
  classical
  intro P hP _
  refine ⟨1, 0, P.carrier, fun _ => P, fun _ i => Fin.elim0 i,
    Finset.Subset.rfl, by simp, ?_, fun _ => hP, by simp, fun _ => by simp,
    fun _ i => Fin.elim0 i, ?_⟩
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · intro j x hx hh y hy
    simp at hy

/-- A common proper partition covers the entire union. Neither the number
of refinement cells nor graph multiplicity amplifies the exceptional loss. -/
theorem LargeBoxMultilinearCover.finsetUnion {N k r : Nat} [NeZero N]
    (Gamma : Fin r → Finset (Point N k × ZMod N)) {rho C e T : Real}
    (hG : ∀ i, LargeBoxMultilinearCover (Gamma i) rho C e T)
    (he : 0 < e) (hC : 0 ≤ C) :
    LargeBoxMultilinearCover (section16FinsetUnion Gamma) ((r : Real) * rho)
      ((r : Real) * C) (e ^ r) (section16PowerIterationThreshold T e r) := by
  classical
  induction r with
  | zero => simpa [section16FinsetUnion, section16PowerIterationThreshold]
      using (section16_empty_power_cover (N := N) (k := k))
  | succ r ih =>
    have hprev := ih (fun i => Gamma i.castSucc) (fun i => hG i.castSucc)
    have hnext := hprev.union (hG (Fin.last r)) (pow_pos he _) he.le hC
    have hsub : section16FinsetUnion Gamma ⊆
        section16FinsetUnion (fun i : Fin r => Gamma i.castSucc) ∪ Gamma (Fin.last r) := by
      intro z hz
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩)
      · exact Finset.mem_union_right _ hi
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, pow_succ,
      section16PowerIterationThreshold] using hnext.mono hsub

end LeanProofs.GowersSzemeredi
