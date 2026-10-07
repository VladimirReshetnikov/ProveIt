import GowersSzemeredi.Proofs16PowerCoverTransport
import GowersSzemeredi.Proofs16FiniteCoverPadding

/-! Sequential refinement of large-box covers. Graph budgets and exceptional
fractions add; width exponents multiply. The threshold ensures that every
intermediate cell is wide enough for the next cover. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The starting width needed to apply a second cover inside a first one. -/
def section16PowerUnionThreshold (T U e : Real) : Real :=
  max T ((max 1 U) ^ e⁻¹)

theorem LargeBoxMultilinearCover.union {N k : Nat} [NeZero N]
    {Gamma Delta : Finset (Point N k × ZMod N)} {rho sigma C D e f T U : Real}
    (hG : LargeBoxMultilinearCover Gamma rho C e T)
    (hD : LargeBoxMultilinearCover Delta sigma D f U)
    (he : 0 < e) (hf : 0 ≤ f) (hD0 : 0 ≤ D) :
    LargeBoxMultilinearCover (Gamma ∪ Delta) (rho + sigma) (C + D) (e * f)
      (section16PowerUnionThreshold T U e) := by
  classical
  intro P hP hT
  obtain ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu, hc⟩ :=
    hG P hP ((le_max_left _ _).trans hT)
  have hwide (j : Fin M) : U ≤ ((Q j).width : Real) := by
    have hpow := (Real.rpow_inv_le_iff_of_pos
      (show (0 : Real) ≤ max 1 U by positivity) (Nat.cast_nonneg P.width) he).mp
      ((le_max_right _ _).trans hT)
    exact (le_max_right 1 U).trans (hpow.trans (hw j))
  choose L p K R nu hK hKm hRp hRproper hpb hRw hnu hcov using
    fun j => hD (Q j) (hproper j) (hwide j)
  let pmax := Nat.floor D
  have hpm (j : Fin M) : p j ≤ pmax := Nat.le_floor (hpb j)
  have hgood := IsPartition.good_union hp K sigma hK hKm
  have hmass := good_intersection_mass P.carrier H (Finset.univ.biUnion K)
    rho sigma hH hgood.1 hm hgood.2
  let E := section5NatFlattenEquiv L
  let family (j : Fin (∑ u, L u)) : Fin q ⊕ Fin pmax → Point N k → ZMod N :=
    Sum.elim (mu (E.symm j).1)
      (padMultilinearFamily (nu (E.symm j).1 (E.symm j).2) pmax)
  refine ⟨∑ u, L u, q + pmax, H ∩ Finset.univ.biUnion K, boxFlatten L R,
    fun j i => family j (finSumFinEquiv.symm i),
    Finset.inter_subset_left.trans hH, ?_, boxFlatten_partition P Q L R hp hRp,
    fun j => hRproper _ _, ?_, ?_, ?_, ?_⟩
  · simpa only [sub_add_eq_sub_sub] using hmass
  · push_cast
    exact add_le_add hq (Nat.floor_le hD0)
  · intro j
    calc
      (P.width : Real) ^ (e * f) = ((P.width : Real) ^ e) ^ f :=
        Real.rpow_mul (Nat.cast_nonneg _) _ _
      _ ≤ (((Q (E.symm j).1).width : Real) ^ f) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hw _) hf
      _ ≤ (boxFlatten L R j).width := hRw _ _
  · intro j i
    change IsMultilinear (family j (finSumFinEquiv.symm i))
    cases finSumFinEquiv.symm i with
    | inl a => exact hmu _ a
    | inr a => exact padMultilinearFamily_isMultilinear _ (hnu _ _) a
  · intro j x hx hh y hxy
    obtain ⟨hxH, hxK⟩ := Finset.mem_inter.mp hh
    have hxQ := IsPartition.cell_subset (hRp (E.symm j).1) (E.symm j).2 hx
    rcases Finset.mem_union.mp hxy with hy | hy
    · obtain ⟨a, ha⟩ := hc _ x hxQ hxH y hy
      refine ⟨finSumFinEquiv (Sum.inl a), ?_⟩
      simpa only [Equiv.symm_apply_apply, family, Sum.elim_inl] using ha
    · have hxlocal := (IsPartition.good_union_mem_iff hp K hK (E.symm j).1 hxQ).mp hxK
      obtain ⟨a, ha⟩ := padMultilinearFamily_covers _ (hpm _) x y
        (hcov _ _ x hx hxlocal y hy)
      refine ⟨finSumFinEquiv (Sum.inr a), ?_⟩
      simpa only [Equiv.symm_apply_apply, family, Sum.elim_inr] using ha

end LeanProofs.GowersSzemeredi
