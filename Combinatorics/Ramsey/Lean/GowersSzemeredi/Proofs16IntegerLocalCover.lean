import GowersSzemeredi.Proofs16WithLemma6
import GowersSzemeredi.Proofs16IntegerShortParents

/-! Multiple multilinearity with genuine integer input and output boxes.
Localizing and combining covers retain the original graph counts and losses. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def IntegerMultiplyLinearWith {N k : Nat} [NeZero N] (Qb Eb : Real → Real)
    (Gamma : Finset (Point N k × ZMod N)) : Prop :=
  ∀ theta : Real, 0 < theta → theta ≤ 1 → ∀ P : Box N k, P.HasIntegerRepresentatives →
    ∃ M q : Nat, ∃ H : Finset (Point N k), ∃ Q : Fin M → Box N k,
      ∃ mu : Fin M → Fin q → Point N k → ZMod N,
        H ⊆ P.carrier ∧ (1 - theta) * P.carrier.card ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
        (q : Real) ≤ Qb theta ∧
        (∀ j, (P.width : Real) ^ (Eb theta) ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∀ y,
          (x, y) ∈ Gamma → ∃ i, y = mu j i x

theorem IntegerMultiplyLinearWith.mono {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma Gamma' : Finset (Point N k × ZMod N)}
    (h : IntegerMultiplyLinearWith Qb Eb Gamma) (hsub : Gamma' ⊆ Gamma) :
    IntegerMultiplyLinearWith Qb Eb Gamma' := by
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hmass, hpart, hQ, hq, hwidth, hmu, hcover⟩ := h theta ht ht1 P hP
  exact ⟨M, q, H, Q, mu, hH, hmass, hpart, hQ, hq, hwidth, hmu,
    fun j x hx hxH y hy => hcover j x hx hxH y (hsub hy)⟩

theorem IntegerMultiplyLinearWith.on_partition {N k J : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : IntegerMultiplyLinearWith Qb Eb Gamma) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hQ : 0 ≤ Qb sigma) (P : Box N k)
    (B : Fin J → Box N k) (hBpart : IsBoxPartition B P)
    (hB : ∀ j, (B j).HasIntegerRepresentatives) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ M : Fin J → Nat,
      ∃ R : (j : Fin J) → Fin (M j) → Box N k,
      ∃ mu : (j : Fin J) → Fin (M j) → Fin q → Point N k → ZMod N,
      (q : Real) ≤ Qb sigma ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      (∀ j, IsBoxPartition (R j) (B j)) ∧
      (∀ j a, (R j a).IsAscendingInteger) ∧
      (∀ j a, ((B j).width : Real) ^ Eb sigma ≤ (R j a).width) ∧
      (∀ j a i, IsMultilinear (mu j a i)) ∧
      ∀ j a x, x ∈ (R j a).carrier → x ∈ G → ∀ y,
        (x, y) ∈ Gamma → ∃ i, y = mu j a i x := by
  classical
  choose M p H R nu hHsub hHmass hRpart hR hp hRwidth hnu hcover using
    fun j => hML sigma hs hs1 (B j) (hB j)
  let q := Nat.floor (Qb sigma)
  have hpq (j : Fin J) : p j ≤ q := Nat.le_floor (hp j)
  let G := Finset.univ.biUnion H
  have hG := IsPartition.good_union hBpart H sigma hHsub hHmass
  refine ⟨q, G, M, R, fun j a => padMultilinearFamily (nu j a) q,
    Nat.floor_le hQ, hG.1, hG.2, hRpart, hR, hRwidth, ?_, ?_⟩
  · intro j a i
    exact padMultilinearFamily_isMultilinear (nu j a) (hnu j a) i
  · intro j a x hx hxG y hxy
    have hxB := IsPartition.cell_subset (hRpart j) a hx
    have hxH := (IsPartition.good_union_mem_iff hBpart H hHsub j hxB).mp hxG
    exact padMultilinearFamily_covers (nu j a) (hpq j) x y (hcover j a x hx hxH y hxy)

theorem IntegerMultiplyLinearWith.short_parent_cover {N k m : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : IntegerMultiplyLinearWith Qb Eb Gamma) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hQ : 0 ≤ Qb sigma) (hE : 0 ≤ Eb sigma)
    (P : Box N k) (I : ModAP N) (hP : P.IsAscendingInteger) (hI : I.IsProper)
    (hk : 0 < k) (hm : 4 ≤ m) (hmP : m ≤ P.width) (hmI : m ≤ I.length) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ J : Nat, ∃ B : Fin J → Box N k,
      ∃ M : Fin J → Nat, ∃ R : (j : Fin J) → Fin (M j) → Box N k,
      ∃ mu : (j : Fin J) → Fin (M j) → Fin q → Point N k → ZMod N,
      (q : Real) ≤ Qb sigma ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsBoxPartition B P ∧ (∀ j, (B j).IsAscendingInteger) ∧
      (∀ j i, 0 < ((B j).axis i).length ∧
        2 * ((B j).axis i).length ≤ N ∧ ((B j).axis i).length ≤ I.length) ∧
      (∀ j, (B j).commonDiff = P.commonDiff) ∧
      (∀ j, IsBoxPartition (R j) (B j)) ∧ (∀ j a, (R j a).IsAscendingInteger) ∧
      (∀ j a, ((m : Real) / 8) ^ Eb sigma ≤ (R j a).width) ∧
      (∀ j a i, IsMultilinear (mu j a i)) ∧
      ∀ j a x, x ∈ (R j a).carrier → x ∈ G → ∀ y,
        (x, y) ∈ Gamma → ∃ i, y = mu j a i x := by
  obtain ⟨J, B, hBpart, hB, hBaxes, hBstep⟩ :=
    P.ascending_short_parent_partition I hP hI hk hm hmP hmI
  obtain ⟨q, G, M, R, mu, hq, hGsub, hGmass, hRpart, hR, hRwidth, hmu, hcover⟩ :=
    hML.on_partition sigma hs hs1 hQ P B hBpart (fun j => (hB j).1.toGenuine)
  refine ⟨q, G, J, B, M, R, mu, hq, hGsub, hGmass, hBpart,
    (fun j => (hB j).1), hBaxes, hBstep, hRpart, hR, ?_, hmu, hcover⟩
  intro j a
  exact (Real.rpow_le_rpow (by positivity) (hB j).2 hE).trans (hRwidth j a)

end LeanProofs.GowersSzemeredi
