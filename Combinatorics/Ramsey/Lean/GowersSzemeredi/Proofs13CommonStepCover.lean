import GowersSzemeredi.Proofs13QuadraticRecurrence
import GowersSzemeredi.Proofs05Downstream

/-! Equal-length common-step covers. Allowing the last cell to extend past
an endpoint avoids deleting points of the dense set. The total capacity
increases by at most a factor two in each coordinate.

`corollary_13_10_of_integer_step_fit` is in `Proofs13CommonStepCoverSide`,
outside the final route. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A nonzero step gives a proper progression up to the prime modulus. -/
theorem ModAP.isProper_of_prime_step {N : Nat} [Fact N.Prime]
    (P : ModAP N) (hd : P.step != 0) (hlen : P.length ≤ N) : P.IsProper := by
  unfold ModAP.IsProper ModAP.carrier
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    have hc : (i.val : ZMod N) = j.val :=
      mul_right_cancel₀ (bne_iff_ne.mp hd) (add_left_cancel hij)
    have hv := congrArg ZMod.val hc
    apply Fin.ext
    simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hlen),
      ZMod.val_natCast_of_lt (j.isLt.trans_le hlen)] using hv

/-- Cells indexed by a residue and a block, all with exactly m points. -/
def commonStepCoverCell {N : Nat} (P : ModAP N) (t m : Nat)
    (j : Fin t × Fin (P.length / (t * m) + 1)) : ModAP N where
  start := P.start + ((j.1.val + j.2.val * m * t : Nat) : ZMod N) * P.step
  step := (t : ZMod N) * P.step
  length := m

/-- Every original point lies in one of the padded cells. -/
theorem commonStepCoverCell_covers {N : Nat} (P : ModAP N) {t m : Nat}
    (ht : 0 < t) (hm : 0 < m) {x : ZMod N} (hx : x ∈ P.carrier) :
    ∃ j, x ∈ (commonStepCoverCell P t m j).carrier := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  let a : Fin t := ⟨i.val % t, Nat.mod_lt _ ht⟩
  have hb : i.val / t / m < P.length / (t * m) + 1 := by
    rw [Nat.div_div_eq_div_mul]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le)
  let b : Fin (P.length / (t * m) + 1) := ⟨i.val / t / m, hb⟩
  let k : Fin m := ⟨i.val / t % m, Nat.mod_lt _ hm⟩
  refine ⟨(a, b), Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩⟩
  have heq : a.val + b.val * m * t + k.val * t = i.val := by
    have h₁ := Nat.div_add_mod i.val t
    have h₂ := Nat.div_add_mod (i.val / t) m
    dsimp [a, b, k]
    nlinarith only [h₁, h₂]
  change P.start + ((a.val + b.val * m * t : Nat) : ZMod N) * P.step +
    (k.val : ZMod N) * ((t : ZMod N) * P.step) = _
  calc
    _ = P.start + ((a.val + b.val * m * t + k.val * t : Nat) : ZMod N) * P.step := by
      push_cast; ring
    _ = _ := by rw [heq]

/-- If one block fits inside the source length, the total padded capacity
is at most twice that length. -/
theorem commonStepCoverCell_capacity (L t m : Nat) (hfit : t * m ≤ L) :
    (t * (L / (t * m) + 1)) * m ≤ 2 * L := by
  have hdiv := Nat.div_mul_le_self L (t * m)
  nlinarith only [hdiv, hfit]

/-- Covering both coordinates with at most twice their original capacity
preserves one quarter of the density in an equal-size product cell. -/
theorem exists_dense_equal_product_cover {X Y I J : Type*}
    [DecidableEq X] [DecidableEq Y] [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (S : Finset X) (T : Finset Y) (D : Finset (X × Y))
    (V : I → Finset X) (W : J → Finset Y) (m : Nat) (delta : Real)
    (hδ : 0 ≤ delta) (hsub : D ⊆ S.product T)
    (hV : ∀ x ∈ S, ∃ i, x ∈ V i) (hW : ∀ y ∈ T, ∃ j, y ∈ W j)
    (hcapV : Fintype.card I * m ≤ 2 * S.card)
    (hcapW : Fintype.card J * m ≤ 2 * T.card)
    (hmass : delta * S.card * T.card ≤ D.card) :
    ∃ i j, delta / 4 * m * m ≤ (D ∩ (V i).product (W j)).card := by
  let C := fun z : I × J => D ∩ (V z.1).product (W z.2)
  have hcount : D.card ≤ ∑ z : I × J, (C z).card := by
    refine le_trans (Finset.card_le_card fun z hz => ?_) Finset.card_biUnion_le
    obtain ⟨⟨i, hi⟩, j, hj⟩ := And.imp (hV z.1) (hW z.2) (Finset.mem_product.mp (hsub hz))
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _,
      Finset.mem_inter.mpr ⟨hz, Finset.mem_product.mpr ⟨hi, hj⟩⟩⟩
  have hcap : ((Fintype.card I * m) * (Fintype.card J * m) : Real) ≤
      (2 * S.card) * (2 * T.card) := by exact_mod_cast Nat.mul_le_mul hcapV hcapW
  -- the `|I| |J|` cells carry at least `|D| ≥ δ |S| |T| ≥ |I| |J| δ m² / 4` in total
  obtain ⟨z, -, hz⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (show ∑ _z : I × J, delta / 4 * m * m ≤ ∑ z : I × J, ((C z).card : Real) by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
        Nat.cast_mul, ← Nat.cast_sum]
      linarith [mul_le_mul_of_nonneg_left hcap hδ, (Nat.cast_le (α := Real)).mpr hcount])
  exact ⟨z.1, z.2, hz⟩

/-- An integer step ratio and the displayed fit condition suffice for an
actual common-step square with the density claimed in Corollary 13.10.
The selected set is a subset of the original bilinear set. -/
theorem bilinear_square_of_integer_step_fit {N : Nat} [Fact N.Prime]
    (S T : ModAP N) (D : Finset (Pair N)) (phi : Pair N → ZMod N)
    (delta : Real) (t m : Nat)
    (hS : S.IsProper) (hT : T.IsProper) (hstep : T.step != 0)
    (hstepEq : T.step = (t : ZMod N) * S.step)
    (ht : 0 < t) (hm : 0 < m) (hfit : t * m ≤ S.length) (hmT : m ≤ T.length)
    (hδ : 0 ≤ delta) (hsupport : D ⊆ S.carrier.product T.carrier)
    (hmass : delta * S.length * T.length ≤ D.card) (hbilinear : BilinearOn D phi) :
    ∃ V W : ModAP N, ∃ E : Finset (Pair N),
      V.step = T.step ∧ W.step = T.step ∧ V.IsProper ∧ W.IsProper ∧
      V.length = m ∧ W.length = m ∧ E ⊆ D ∧ E ⊆ V.carrier.product W.carrier ∧
      delta / 4 * m * m ≤ E.card ∧ BilinearOn E phi := by
  let I := Fin t × Fin (S.length / (t * m) + 1)
  let J := Fin 1 × Fin (T.length / (1 * m) + 1)
  let V : I → ModAP N := commonStepCoverCell S t m
  let W : J → ModAP N := commonStepCoverCell T 1 m
  letI : Nonempty I := ⟨(⟨0, ht⟩, ⟨0, Nat.zero_lt_succ _⟩)⟩
  letI : Nonempty J := ⟨(⟨0, Nat.zero_lt_succ _⟩, ⟨0, Nat.zero_lt_succ _⟩)⟩
  obtain ⟨hS', hT'⟩ : S.carrier.card = S.length ∧ T.carrier.card = T.length := ⟨hS, hT⟩
  obtain ⟨i, j, hij⟩ := exists_dense_equal_product_cover S.carrier T.carrier D
    (fun i => (V i).carrier) (fun j => (W j).carrier) m delta hδ hsupport
    (fun _ hx => commonStepCoverCell_covers S ht hm hx)
    (fun _ hx => commonStepCoverCell_covers T Nat.one_pos hm hx)
    (by simpa [I, hS'] using commonStepCoverCell_capacity S.length t m hfit)
    (by simpa [J, hT'] using commonStepCoverCell_capacity T.length 1 m (by omega))
    (by rwa [hS', hT'])
  have hmN : m ≤ N := hmT.trans (hT'.symm.trans_le ((Finset.card_le_univ _).trans_eq (ZMod.card N)))
  have hVstep : (V i).step = T.step := hstepEq.symm
  have hWstep : (W j).step = T.step := by simp [W, commonStepCoverCell]
  refine ⟨V i, W j, D ∩ (V i).carrier.product (W j).carrier, hVstep, hWstep,
    (V i).isProper_of_prime_step (hVstep ▸ hstep) hmN,
    (W j).isProper_of_prime_step (hWstep ▸ hstep) hmN,
    rfl, rfl, Finset.inter_subset_left, Finset.inter_subset_right, hij, ?_⟩
  obtain ⟨mu, hmu, hagree⟩ := hbilinear
  exact ⟨mu, hmu, fun z hz => hagree z (Finset.mem_inter.mp hz).1⟩

/-- Translate the starting point without changing the indexed step or length. -/
def ModAP.translateBy {N : Nat} (P : ModAP N) (y : ZMod N) : ModAP N where
  start := y + P.start
  step := P.step
  length := P.length

theorem ModAP.translateBy_carrier {N : Nat} (P : ModAP N) (y : ZMod N) :
    (P.translateBy y).carrier = translateFinset P.carrier y := by
  unfold ModAP.carrier translateFinset
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  dsimp [ModAP.translateBy]
  ring

theorem ModAP.translateBy_isProper {N : Nat} (P : ModAP N) (y : ZMod N)
    (hP : P.IsProper) : (P.translateBy y).IsProper := by
  unfold ModAP.IsProper
  rw [P.translateBy_carrier, translateFinset,
    Finset.card_image_of_injective _ (add_right_injective y)]
  exact hP

end LeanProofs.GowersSzemeredi
