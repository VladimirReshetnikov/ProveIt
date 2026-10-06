import GowersSzemeredi.Proofs16ShortParents
import GowersSzemeredi.Proofs16RetiledRecurrence

/-! # Uniform multilinear covers on a preliminary partition

Local multiple-linearity witnesses may have different graph counts. Pad them
by zero functions to the floor of their common real bound, and unite their
good sets. Disjointness makes the density loss additive without amplification.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Good subsets of disjoint cells retain their common density after union. -/
theorem IsPartition.good_union {X : Type*} [DecidableEq X] {M : Nat}
    {P : Fin M → Finset X} {S : Finset X} (hpart : IsPartition P S)
    (H : Fin M → Finset X) (eta : Real) (hsub : ∀ i, H i ⊆ P i)
    (hmass : ∀ i, (1 - eta) * ((P i).card : Real) ≤ (H i).card) :
    Finset.univ.biUnion H ⊆ S ∧
      (1 - eta) * (S.card : Real) ≤ (Finset.univ.biUnion H).card := by
  classical
  constructor
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact IsPartition.cell_subset hpart i (hsub i hi)
  · have hpair : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint H := by
      intro i _ j _ hij
      exact Disjoint.mono (hsub i) (hsub j) (hpart.2 i j (bne_iff_ne.mpr hij))
    rw [Finset.card_biUnion hpair, Nat.cast_sum]
    calc
      (1 - eta) * (S.card : Real) = ∑ i, (1 - eta) * ((P i).card : Real) := by
        rw [← Finset.mul_sum]
        congr 1
        exact_mod_cast (IsPartition.sum_card hpart).symm
      _ ≤ ∑ i, ((H i).card : Real) := Finset.sum_le_sum fun i _ => hmass i

/-- Inside a fixed partition cell, the global good union is exactly the
local good subset. This prevents coverage from using another cell's witness. -/
theorem IsPartition.good_union_mem_iff {X : Type*} [DecidableEq X] {M : Nat}
    {P : Fin M → Finset X} {S : Finset X} (hpart : IsPartition P S)
    (H : Fin M → Finset X) (hsub : ∀ i, H i ⊆ P i)
    (i : Fin M) {x : X} (hx : x ∈ P i) :
    x ∈ Finset.univ.biUnion H ↔ x ∈ H i := by
  classical
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp h
    by_cases hji : j = i
    · simpa only [hji] using hj
    · exact False.elim (Finset.disjoint_left.mp
        (hpart.2 j i (bne_iff_ne.mpr hji)) (hsub j hj) hx)
  · intro h
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩

/-- Zero-padding a family preserves all its functions and its multilinearity. -/
def padMultilinearFamily {N k p : Nat} (mu : Fin p → Point N k → ZMod N)
    (q : Nat) (i : Fin q) : Point N k → ZMod N :=
  if h : (i : Nat) < p then mu ⟨i, h⟩ else fun _ => 0

theorem padMultilinearFamily_isMultilinear {N k p q : Nat}
    (mu : Fin p → Point N k → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (i : Fin q) : IsMultilinear (padMultilinearFamily mu q i) := by
  classical
  unfold padMultilinearFamily
  split_ifs
  · exact hmu _
  · exact ⟨fun _ => 0, fun _ => by simp⟩

theorem padMultilinearFamily_covers {N k p q : Nat}
    (mu : Fin p → Point N k → ZMod N) (hpq : p ≤ q)
    (x : Point N k) (y : ZMod N) (hy : ∃ i, y = mu i x) :
    ∃ i, y = padMultilinearFamily mu q i x := by
  obtain ⟨i, hi⟩ := hy
  refine ⟨⟨i, i.isLt.trans_le hpq⟩, ?_⟩
  simpa only [padMultilinearFamily, dif_pos i.isLt] using hi

/-- Multiple multilinearity can be applied on every preliminary cell with
one graph count and one good set for the entire original box. Parent labels
are retained so subsequent retile arguments can use their short axes. -/
theorem MultiplyLinear.on_partition {N k J : Nat} [NeZero N]
    {gamma t : Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinear gamma t Gamma) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (P : Box N k)
    (B : Fin J → Box N k) (hBpart : IsBoxPartition B P) (hBproper : ∀ j, (B j).IsProper) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ M : Fin J → Nat,
      ∃ R : (j : Fin J) → Fin (M j) → Box N k,
      ∃ mu : (j : Fin J) → Fin (M j) → Fin q → Point N k → ZMod N,
      (q : Real) ≤ (multipleQ (t⁻¹ * sigma) gamma k) ^ t ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      (∀ j, IsBoxPartition (R j) (B j)) ∧
      (∀ j a, (R j a).IsProper) ∧
      (∀ j a, ((B j).width : Real) ^ ((multipleC (t⁻¹ * sigma) gamma k) ^ t) ≤ (R j a).width) ∧
      (∀ j a i, IsMultilinear (mu j a i)) ∧
      ∀ j a x, x ∈ (R j a).carrier → x ∈ G → ∀ y,
        (x, y) ∈ Gamma → ∃ i, y = mu j a i x := by
  classical
  choose M p H R nu hHsub hHmass hRpart hRproper hp hRwidth hnu hcover using
    fun j => hML sigma hs hs1 (B j) (hBproper j)
  let bound := (multipleQ (t⁻¹ * sigma) gamma k) ^ t
  have hc : 0 ≤ multipleC (t⁻¹ * sigma) gamma k :=
    (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 8) ≠ 0)).pow_nonneg _
  have hb : 0 ≤ bound := Real.rpow_nonneg (inv_nonneg.mpr hc) _
  let q := Nat.floor bound
  have hpq (j : Fin J) : p j ≤ q := Nat.le_floor (hp j)
  let G := Finset.univ.biUnion H
  have hG := IsPartition.good_union hBpart H sigma hHsub hHmass
  refine ⟨q, G, M, R, fun j a => padMultilinearFamily (nu j a) q,
    Nat.floor_le hb, hG.1, hG.2, hRpart, hRproper, hRwidth, ?_, ?_⟩
  · intro j a i
    exact padMultilinearFamily_isMultilinear (nu j a) (hnu j a) i
  · intro j a x hx hxG y hxy
    have hxB := IsPartition.cell_subset (hRpart j) a hx
    have hxH := (IsPartition.good_union_mem_iff hBpart H hHsub j hxB).mp hxG
    exact padMultilinearFamily_covers (nu j a) (hpq j) x y (hcover j a x hx hxH y hxy)

/-- The preliminary short-parent partition, uniform graph count, and global
good set are obtained directly from multiple multilinearity. Every refined
cell retains its short parent for the subsequent relative-step argument. -/
theorem MultiplyLinear.short_parent_cover {N k m : Nat} [NeZero N]
    {gamma t : Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinear gamma t Gamma) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1)
    (P : Box N k) (I : ModAP N) (hP : P.IsProper) (hI : I.IsProper)
    (hk : 0 < k) (hm : 4 ≤ m) (hmP : m ≤ P.width) (hmI : m ≤ I.length) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ J : Nat, ∃ B : Fin J → Box N k,
      ∃ M : Fin J → Nat, ∃ R : (j : Fin J) → Fin (M j) → Box N k,
      ∃ mu : (j : Fin J) → Fin (M j) → Fin q → Point N k → ZMod N,
      (q : Real) ≤ (multipleQ (t⁻¹ * sigma) gamma k) ^ t ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsBoxPartition B P ∧ (∀ j, (B j).IsProper) ∧
      (∀ j i, 0 < ((B j).axis i).length ∧
        2 * ((B j).axis i).length ≤ N ∧ ((B j).axis i).length ≤ I.length) ∧
      (∀ j, (B j).commonDiff = P.commonDiff) ∧
      (∀ j, IsBoxPartition (R j) (B j)) ∧ (∀ j a, (R j a).IsProper) ∧
      (∀ j a, ((m : Real) / 8) ^ ((multipleC (t⁻¹ * sigma) gamma k) ^ t) ≤ (R j a).width) ∧
      (∀ j a i, IsMultilinear (mu j a i)) ∧
      ∀ j a x, x ∈ (R j a).carrier → x ∈ G → ∀ y,
        (x, y) ∈ Gamma → ∃ i, y = mu j a i x := by
  obtain ⟨J, B, hBpart, hBproper, hBaxes, hBstep⟩ :=
    P.short_parent_partition I hP hI hk hm hmP hmI
  obtain ⟨q, G, M, R, mu, hq, hGsub, hGmass, hRpart, hRproper, hRwidth, hmu, hcover⟩ :=
    hML.on_partition sigma hs hs1 P B hBpart (fun j => (hBproper j).1)
  have hc : 0 ≤ multipleC (t⁻¹ * sigma) gamma k :=
    (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 8) ≠ 0)).pow_nonneg _
  have ha : 0 ≤ (multipleC (t⁻¹ * sigma) gamma k) ^ t := Real.rpow_nonneg hc _
  refine ⟨q, G, J, B, M, R, mu, hq, hGsub, hGmass, hBpart,
    (fun j => (hBproper j).1), hBaxes, hBstep, hRpart, hRproper, ?_, hmu, hcover⟩
  intro j a
  exact (Real.rpow_le_rpow (by positivity) (hBproper j).2 ha).trans (hRwidth j a)

end LeanProofs.GowersSzemeredi
