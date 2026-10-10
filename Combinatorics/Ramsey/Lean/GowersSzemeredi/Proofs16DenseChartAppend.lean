import GowersSzemeredi.Proofs16PropNineThreeTwelve

/-! Retain chart-domain density under the actual append operation.
Pair support of size delta*N^2 projects to at least delta*N domain points;
older chart domains are unchanged by a new chart's append. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Every value has at most N supporting pairs, so pair density supplies
the chart-domain density needed by the common Sanders construction. -/
theorem pair_support_second_density {N : Nat} [NeZero N]
    (P : Finset (ZMod N × ZMod N)) (B : Finset (ZMod N)) {delta : Real}
    (hPB : ∀ p ∈ P, p.2 ∈ B) (hP : delta*(N : Real)^2 ≤ (P.card : Real)) :
    delta*(N : Real) ≤ (B.card : Real) := by
  have hsub : P ⊆ (Finset.univ : Finset (ZMod N)) ×ˢ B := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,hPB p hp⟩
  have hc : (P.card : Real) ≤ (N : Real)*B.card := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_product,Finset.card_univ,ZMod.card] at h
    exact_mod_cast h
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right _ hN
  calc delta*N*N = delta*(N : Real)^2 := by ring
    _ ≤ P.card := hP
    _ ≤ (N : Real)*B.card := hc
    _ = _ := by ring

/-- Strong append preserves the invariant, each actual domain density,
and the exact potential increase. -/
theorem propNineThree_append_dense {N : Nat} [NeZero N] {Γ : ZMod N → Finset (ZMod N)} {R' m : Nat}
    {θ : Nat → ZMod N → ZMod N} {D : Nat → Finset (ZMod N)} {I : ZMod N → ZMod N → Finset Nat}
    (hinv : PropNineThreeInvariant Γ R' m θ D I) {delta : Real}
    (hdense : ∀ i < m, delta*(N : Real) ≤ ((D i).card : Real)) (Θ : ZMod N → ZMod N) (B : Finset (ZMod N))
    (P : Finset (ZMod N × ZMod N)) (hF : FreimanHom 8 B Θ)
    (hBmass : delta*(N : Real) ≤ (B.card : Real))
    (hP : ∀ p ∈ P, p.2 ∈ B ∧ Θ p.2 ∈ spanBall (Γ (p.1 + p.2) ∪ Γ p.1) R' ∧
      Θ p.2 ∉ spanBall ((I p.1 p.2).image fun i => θ i p.2) 1) :
    ∃ (θ' : Nat → ZMod N → ZMod N) (D' : Nat → Finset (ZMod N))
      (I' : ZMod N → ZMod N → Finset Nat),
      PropNineThreeInvariant Γ R' (m + 1) θ' D' I' ∧
      (∀ i < m+1, delta*(N : Real) ≤ ((D' i).card : Real)) ∧
      propNineThreePotential I' = propNineThreePotential I + P.card := by
  -- the updated state
  let θ' : Nat → ZMod N → ZMod N := fun i => if i = m then Θ else θ i
  let D' : Nat → Finset (ZMod N) := fun i => if i = m then B else D i
  let I' : ZMod N → ZMod N → Finset Nat := fun x a =>
    if (x, a) ∈ P then insert m (I x a) else I x a
  have hlt : ∀ x a, ∀ i ∈ I x a, i ≠ m := by
    intro x a i hi
    have := Finset.mem_range.mp ((hinv.2 x a).1 hi)
    omega
  have himage : ∀ x a, (I x a).image (fun i => θ' i a) = (I x a).image (fun i => θ i a) := by
    intro x a
    refine Finset.image_congr fun i hi => ?_
    simp only [θ', if_neg (hlt x a i hi)]
  refine ⟨θ', D', I', ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    by_cases him : i = m
    · simp only [θ', D', if_pos him]
      exact hF
    · simp only [θ', D', if_neg him]
      exact hinv.1 i (by omega)
  · intro x a
    obtain ⟨hsub, hI, hinj, hind⟩ := hinv.2 x a
    by_cases hp : (x, a) ∈ P
    · obtain ⟨haB, hΘspan, hΘnot⟩ := hP (x, a) hp
      simp only [I', if_pos hp]
      have hΘnotV : Θ a ∉ (I x a).image fun i => θ i a :=
        fun h => hΘnot (self_mem_spanBall_one h)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (hsub hi)))
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp only [θ', D', if_pos rfl]
          exact ⟨haB, hΘspan⟩
        · simp only [θ', D', if_neg (hlt x a i hi)]
          exact hI i hi
      · rw [Finset.coe_insert, Set.injOn_insert (fun h => hlt x a m h rfl)]
        refine ⟨?_, ?_⟩
        · intro i hi j hj hij
          simp only [θ', if_neg (hlt x a i hi), if_neg (hlt x a j hj)] at hij
          exact hinj hi hj hij
        · rintro ⟨i, hi, hij⟩
          simp only [θ', if_neg (hlt x a i hi), if_pos rfl] at hij
          exact hΘnotV (Finset.mem_image.mpr ⟨i, hi, hij⟩)
      · rw [Finset.image_insert, himage x a]
        simp only [θ', if_pos rfl]
        exact subsetSumInjective_insert hind hΘnot
    · simp only [I', if_neg hp]
      refine ⟨hsub.trans (Finset.range_mono (Nat.le_succ m)), ?_, ?_, ?_⟩
      · intro i hi
        simp only [θ', D', if_neg (hlt x a i hi)]
        exact hI i hi
      · intro i hi j hj hij
        simp only [θ', if_neg (hlt x a i hi), if_neg (hlt x a j hj)] at hij
        exact hinj hi hj hij
      · rw [himage x a]
        exact hind
  · -- domain density is preserved at every older index and added at the new one
    intro i hi
    by_cases him : i = m
    · simp only [D',if_pos him]
      exact hBmass
    · simp only [D',if_neg him]
      exact hdense i (by omega)
  · -- the potential rises by `|P|`
    show propNineThreePotential I' = propNineThreePotential I + P.card
    unfold propNineThreePotential
    have : ∀ p : ZMod N × ZMod N, (I' p.1 p.2).card =
        (I p.1 p.2).card + if p ∈ P then 1 else 0 := by
      intro p
      by_cases hp : p ∈ P
      · have hp' : (p.1, p.2) ∈ P := hp
        simp only [I', if_pos hp']
        exact Finset.card_insert_of_notMem fun h => hlt p.1 p.2 m h rfl
      · have hp' : (p.1, p.2) ∉ P := hp
        simp only [I', if_neg hp', add_zero]
    rw [Finset.sum_congr rfl fun p _ => this p, Finset.sum_add_distrib]
    congr 1
    simp


end LeanProofs.GowersSzemeredi
