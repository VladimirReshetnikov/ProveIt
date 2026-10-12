import GowersSzemeredi.Proofs13DenseIntegerRectangle
import GowersSzemeredi.Proofs13CommonStepCover
import GowersSzemeredi.Proofs05Lemma9Induction

/-! Equal-length covers contained in ordinary progressions. The last block
is shifted left to the endpoint, so every cell retains integer representatives. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def clampedCoverIndex (L m : Nat) (j : Fin (L / m + 1)) : NatAP :=
  ⟨min (j.val * m) (L - m), 1, m⟩

theorem clampedCoverIndex_isProper (L m : Nat) (j : Fin (L / m + 1)) :
    (clampedCoverIndex L m j).IsProper := by
  classical
  refine ⟨by change 0 < (1 : Nat); decide, ?_⟩
  unfold NatAP.carrier
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_univ, clampedCoverIndex]
    exact Fintype.card_fin m
  · intro i k h
    apply Fin.ext
    simpa [clampedCoverIndex] using h

theorem clampedCoverIndex_subset {L m : Nat} (hfit : m ≤ L)
    (j : Fin (L / m + 1)) :
    (clampedCoverIndex L m j).carrier ⊆ Finset.range L := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_range.mpr
  change min (j.val * m) (L - m) + i.val * 1 < L
  have hmin := min_le_right (j.val * m) (L - m)
  have hi : i.val < m := i.isLt
  omega

theorem clampedCoverIndex_covers {L m : Nat} (hm : 0 < m) (hfit : m ≤ L)
    {x : Nat} (hx : x ∈ Finset.range L) :
    ∃ j, x ∈ (clampedCoverIndex L m j).carrier := by
  classical
  have hxL := Finset.mem_range.mp hx
  let j : Fin (L / m + 1) := ⟨x / m, Nat.lt_succ_of_le (Nat.div_le_div_right hxL.le)⟩
  let a := min (j.val * m) (L - m)
  have ha : a ≤ x := (min_le_left _ _).trans (Nat.div_mul_le_self x m)
  have hxm : x - a < m := by
    by_cases h : j.val * m ≤ L - m
    · have hxmod := Nat.mod_lt x hm
      have hdiv : x / m * m + x % m = x := by
        simpa only [Nat.mul_comm] using Nat.div_add_mod x m
      dsimp [a]
      rw [min_eq_left h]
      dsimp [j] at *
      omega
    · dsimp [a]
      rw [min_eq_right (le_of_not_ge h)]
      omega
  let i : Fin m := ⟨x - a, hxm⟩
  refine ⟨j, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩⟩
  change a + (x - a) * 1 = x
  omega

def NatAP.clampedCover (P : NatAP) (m : Nat) (j : Fin (P.length / m + 1)) : NatAP :=
  section5NatTransport P (clampedCoverIndex P.length m j)

theorem NatAP.clampedCover_properties (P : NatAP) (hP : P.IsProper)
    {m : Nat} (hfit : m ≤ P.length) (j : Fin (P.length / m + 1)) :
    (P.clampedCover m j).IsProper ∧ (P.clampedCover m j).length = m ∧
      (P.clampedCover m j).step = P.step ∧ (P.clampedCover m j).carrier ⊆ P.carrier := by
  refine ⟨section5NatTransport_isProper P _ hP (clampedCoverIndex_isProper _ _ _),
    rfl, ?_, section5NatTransport_subset P _ (clampedCoverIndex_subset hfit j)⟩
  change 1 * P.step = P.step
  exact one_mul _

theorem NatAP.clampedCover_covers (P : NatAP) {m : Nat} (hm : 0 < m)
    (hfit : m ≤ P.length) {x : Nat} (hx : x ∈ P.carrier) :
    ∃ j, x ∈ (P.clampedCover m j).carrier := by
  classical
  rw [section5Nat_carrier_eq_image_range] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj⟩ := clampedCoverIndex_covers hm hfit hi
  refine ⟨j, ?_⟩
  rw [NatAP.clampedCover, section5NatTransport_carrier]
  exact Finset.mem_image.mpr ⟨i, hj, rfl⟩

theorem NatAP.clampedCover_mod_covers {N : Nat} (P : NatAP) {m : Nat}
    (hm : 0 < m) (hfit : m ≤ P.length) {x : ZMod N} (hx : x ∈ (P.toModAP N).carrier) :
    ∃ j, x ∈ ((P.clampedCover m j).toModAP N).carrier := by
  classical
  rw [NatAP.toModAP_carrier] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj⟩ := P.clampedCover_covers hm hfit hi
  refine ⟨j, ?_⟩
  rw [NatAP.toModAP_carrier]
  exact Finset.mem_image.mpr ⟨i, hj, rfl⟩

theorem clampedCover_capacity (L m : Nat) (hfit : m ≤ L) :
    (L / m + 1) * m ≤ 2 * L := by
  have hdiv := Nat.div_mul_le_self L m
  nlinarith only [hdiv, hfit]

theorem dense_equal_integer_square {N : Nat} [NeZero N]
    (P R : NatAP) (hP : P.IsProper) (hR : R.IsProper) (hstep : P.step = R.step)
    (hPN : P.carrier ⊆ Finset.range N) (hRN : R.carrier ⊆ Finset.range N)
    (D : Finset (Pair N)) (delta : Real) (hd : 0 ≤ delta) (m : Nat)
    (hm : 0 < m) (hmP : m ≤ P.length) (hmR : m ≤ R.length)
    (hsub : D ⊆ (P.toModAP N).carrier.product (R.toModAP N).carrier)
    (hmass : delta * P.length * R.length ≤ D.card) :
    ∃ Q T : NatAP, ∃ E : Finset (Pair N),
      Q.IsProper ∧ T.IsProper ∧ Q.step = T.step ∧ Q.length = m ∧ T.length = m ∧
      Q.carrier ⊆ P.carrier ∧ T.carrier ⊆ R.carrier ∧
      E ⊆ D ∧ E ⊆ (Q.toModAP N).carrier.product (T.toModAP N).carrier ∧
      delta / 4 * m * m ≤ E.card := by
  classical
  let I := Fin (P.length / m + 1)
  let J := Fin (R.length / m + 1)
  letI : Nonempty I := ⟨⟨0, Nat.zero_lt_succ _⟩⟩
  letI : Nonempty J := ⟨⟨0, Nat.zero_lt_succ _⟩⟩
  have hPmod : (P.toModAP N).carrier.card = P.length :=
    (P.toModAP_hasIntegerRepresentatives hP hPN).isProper
  have hRmod : (R.toModAP N).carrier.card = R.length :=
    (R.toModAP_hasIntegerRepresentatives hR hRN).isProper
  have hcapP : Fintype.card I * m ≤ 2 * (P.toModAP N).carrier.card := by
    rw [hPmod]
    simpa only [I, Fintype.card_fin] using clampedCover_capacity P.length m hmP
  have hcapR : Fintype.card J * m ≤ 2 * (R.toModAP N).carrier.card := by
    rw [hRmod]
    simpa only [J, Fintype.card_fin] using clampedCover_capacity R.length m hmR
  obtain ⟨i, j, hij⟩ := exists_dense_equal_product_cover
    (P.toModAP N).carrier (R.toModAP N).carrier D
    (fun i : I => ((P.clampedCover m i).toModAP N).carrier)
    (fun j : J => ((R.clampedCover m j).toModAP N).carrier) m delta hd hsub
    (fun _ hx => P.clampedCover_mod_covers hm hmP hx)
    (fun _ hx => R.clampedCover_mod_covers hm hmR hx) hcapP hcapR
    (by simpa only [hPmod, hRmod] using hmass)
  obtain ⟨hQ, hQlen, hQstep, hQsub⟩ := P.clampedCover_properties hP hmP i
  obtain ⟨hT, hTlen, hTstep, hTsub⟩ := R.clampedCover_properties hR hmR j
  exact ⟨P.clampedCover m i, R.clampedCover m j, _, hQ, hT,
    hQstep.trans (hstep.trans hTstep.symm), hQlen, hTlen, hQsub, hTsub,
    Finset.inter_subset_left, Finset.inter_subset_right, hij⟩

end LeanProofs.GowersSzemeredi
