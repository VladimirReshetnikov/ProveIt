import OAI.Combinatorics.Progressions.Geometry.DenseRealBoxCell
import OAI.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def centeredScalarBlock (R k : ℕ) (x : ℤ) : ℕ :=
  (x + (R : ℤ)).toNat / (2 * (R / (2 * k)) + 1)

def centeredScalarCenter (R k c : ℕ) : ℤ :=
  (c : ℤ) * (2 * (R / (2 * k) : ℕ) + 1) - R + (R / (2 * k) : ℕ)

theorem centeredScalarBlock_lt (R k : ℕ) (hk : 0 < k) (x : ℤ)
    (hx : |x| ≤ (R : ℤ)) : centeredScalarBlock R k x < 4 * k := by
  have htwo : 0 < 2 * k := by omega
  have hR := Nat.lt_mul_div_succ R htwo
  have ht : (x + (R : ℤ)).toNat ≤ 2 * R := by
    have h := abs_le.mp hx
    omega
  have hku : 0 ≤ k * (R / (2 * k)) := Nat.zero_le _
  have hcover : 2 * R < 4 * k * (2 * (R / (2 * k)) + 1) := by
    nlinarith only [hR, hku]
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * (R / (2 * k)) + 1)).mpr
  exact ht.trans_lt hcover

theorem centeredScalarCenter_offset (R k : ℕ) (x : ℤ)
    (hx : |x| ≤ (R : ℤ)) :
    |x - centeredScalarCenter R k (centeredScalarBlock R k x)| ≤ (R / (2 * k) : ℕ) := by
  let t := (x + (R : ℤ)).toNat
  let L := 2 * (R / (2 * k)) + 1
  have ht : (t : ℤ) = x + R := by
    apply Int.toNat_of_nonneg
    have h := abs_le.mp hx
    omega
  have hmod : t % L < L := Nat.mod_lt t (by dsimp [L]; omega)
  have hrem : ((t % L : ℕ) : ℤ) + (L : ℤ) * (t / L : ℕ) = x + R := by
    rw [← ht]
    exact_mod_cast Nat.mod_add_div t L
  have hcancel : x - centeredScalarCenter R k (centeredScalarBlock R k x) =
      (t % L : ℕ) - (R / (2 * k) : ℕ) := by
    unfold centeredScalarCenter centeredScalarBlock
    change x - ((t / L : ℕ) * (2 * ((R / (2 * k) : ℕ) : ℤ) + 1) - R +
      ((R / (2 * k) : ℕ) : ℤ)) = ((t % L : ℕ) : ℤ) - ((R / (2 * k) : ℕ) : ℤ)
    have hL : (L : ℤ) = 2 * ((R / (2 * k) : ℕ) : ℤ) + 1 := by
      simp only [L, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [hL] at hrem
    nlinarith only [hrem]
  have hmod' : ((t % L : ℕ) : ℤ) ≤ 2 * ((R / (2 * k) : ℕ) : ℤ) := by
    have h : t % L ≤ 2 * (R / (2 * k)) := Nat.le_of_lt_succ hmod
    exact_mod_cast h
  rw [hcancel, abs_le]
  constructor <;> linarith only [hmod', Int.natCast_nonneg (t % L)]

theorem exists_dense_centered_box_block {ι α : Type*} [Fintype ι]
    (S : Finset α) (hS : S.Nonempty) (x : α → ι → ℤ) (R : ι → ℕ)
    (k : ℕ) (hk : 0 < k) (hbound : ∀ a ∈ S, ∀ i, |x a i| ≤ (R i : ℤ)) :
    ∃ T ⊆ S, T.Nonempty ∧ S.card ≤ (4 * k) ^ Fintype.card ι * T.card ∧
      ∃ c : ι → ℤ, ∀ a ∈ T, ∀ i, |x a i - c i| ≤ (R i / (2 * k) : ℕ) := by
  classical
  have hfour : 0 < 4 * k := by omega
  let : NeZero (4 * k) := ⟨hfour.ne'⟩
  let label (a : α) (i : ι) : Fin (4 * k) :=
    ⟨centeredScalarBlock (R i) k (x a i) % (4 * k), Nat.mod_lt _ hfour⟩
  obtain ⟨b, hT, hsize⟩ := FreimanModel.exists_nonempty_large_fiber S hS label
  let T := S.filter fun a => label a = b
  refine ⟨T, Finset.filter_subset _ _, hT, ?_,
    (fun i => centeredScalarCenter (R i) k (b i).val), ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hsize
  · intro a ha i
    have hmem := (Finset.mem_filter.mp ha).1
    have heq := congrArg Fin.val (congrFun (Finset.mem_filter.mp ha).2 i)
    have hlt := centeredScalarBlock_lt (R i) k hk (x a i) (hbound a hmem i)
    change centeredScalarBlock (R i) k (x a i) % (4 * k) = (b i).val at heq
    rw [Nat.mod_eq_of_lt hlt] at heq
    change |x a i - centeredScalarCenter (R i) k (b i).val| ≤ (R i / (2 * k) : ℕ)
    rw [← heq]
    exact centeredScalarCenter_offset (R i) k (x a i) (hbound a hmem i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_proper_coordinate_restriction
    {r : ℕ} {G : Type*} [AddCommGroup G] (J : Finset G) (hJ : J.Nonempty)
    (R : Fin r → ℕ) (η : (Fin r → ℤ) →+ G) (a : G)
    (x : {h // h ∈ J} → Fin r → ℤ)
    (hx : ∀ h i, |x h i| ≤ (R i : ℤ))
    (hrepr : ∀ h, h.val = a + η (x h)) :
    let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J.card + 1
    ∃ (T : Finset G) (hTJ : T ⊆ J), T.Nonempty ∧
      J.card ≤ (4 * k) ^ r * T.card ∧
      ∃ c : Fin r → ℤ,
        Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
        ∀ h : {h // h ∈ T}, ∀ i,
          |x ⟨h.val, hTJ h.property⟩ i - c i| ≤ (R i / (2 * k) : ℕ) := by
  intro k
  classical
  let : Nonempty {h // h ∈ J} := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  have hk : 0 < k := Nat.succ_pos _
  have hproper := injOn_shrunk_integer_box_of_distinct_points J hJ R η a
    (fun h hh => ⟨x ⟨h, hh⟩, hx ⟨h, hh⟩, hrepr ⟨h, hh⟩⟩)
  obtain ⟨U, _hUuniv, hU, hsize, c, hsmall⟩ :=
    exists_dense_centered_box_block (Finset.univ : Finset {h // h ∈ J})
      Finset.univ_nonempty x R k hk (fun h _ => hx h)
  let T := U.image Subtype.val
  have hTJ : T ⊆ J := by
    intro h hh
    obtain ⟨h', _, rfl⟩ := Finset.mem_image.mp hh
    exact h'.property
  have hcard : T.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨T, hTJ, hU.image _, ?_, c, hproper, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_coe, Fintype.card_fin, hcard] using hsize
  · intro h i
    obtain ⟨h', hh', heq⟩ := Finset.mem_image.mp h.property
    have hident : h' = ⟨h.val, hTJ h.property⟩ := Subtype.ext heq
    simpa only [hident] using hsmall h' hh' i

end Erdos3

end

end OAI
