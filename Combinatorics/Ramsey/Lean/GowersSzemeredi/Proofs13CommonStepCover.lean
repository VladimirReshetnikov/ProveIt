import GowersSzemeredi.Proofs13BilinearRestriction
import GowersSzemeredi.Proofs05Downstream

/-! Equal-length common-step covers. Allowing the last cell to extend past
an endpoint avoids deleting points of the dense set. The total capacity
increases by at most a factor two in each coordinate. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A nonzero step gives a proper progression up to the prime modulus. -/
theorem ModAP.isProper_of_prime_step {N : Nat} [Fact N.Prime]
    (P : ModAP N) (hd : P.step != 0) (hlen : P.length ≤ N) : P.IsProper := by
  classical
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
  classical
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
      push_cast
      ring
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
  classical
  let C := fun z : I × J => D ∩ (V z.1).product (W z.2)
  have hcover : D ⊆ Finset.univ.biUnion C := by
    intro z hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hsub hz)
    obtain ⟨i, hi⟩ := hV z.1 hx
    obtain ⟨j, hj⟩ := hW z.2 hy
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _,
      Finset.mem_inter.mpr ⟨hz, Finset.mem_product.mpr ⟨hi, hj⟩⟩⟩
  have hcount : (D.card : Real) ≤ ∑ z : I × J, ((C z).card : Real) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcap : Fintype.card (I × J) * m * m ≤ 4 * S.card * T.card := by
    have h := Nat.mul_le_mul hcapV hcapW
    rw [Fintype.card_prod]
    nlinarith only [h]
  have hcapR : (Fintype.card (I × J) : Real) * m * m ≤ 4 * S.card * T.card := by
    exact_mod_cast hcap
  have hsum : ∑ _z : I × J, delta / 4 * m * m ≤ ∑ z : I × J, ((C z).card : Real) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_left hcapR (div_nonneg hδ (by norm_num : (0 : Real) ≤ 4))
    nlinarith only [h, hmass, hcount]
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty) hsum
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
  classical
  let I := Fin t × Fin (S.length / (t * m) + 1)
  let J := Fin 1 × Fin (T.length / (1 * m) + 1)
  let V : I → ModAP N := commonStepCoverCell S t m
  let W : J → ModAP N := commonStepCoverCell T 1 m
  letI : Nonempty I := ⟨(⟨0, ht⟩, ⟨0, Nat.zero_lt_succ _⟩)⟩
  letI : Nonempty J := ⟨(⟨0, Nat.zero_lt_succ _⟩, ⟨0, Nat.zero_lt_succ _⟩)⟩
  have hcapV : Fintype.card I * m ≤ 2 * S.carrier.card := by
    rw [show S.carrier.card = S.length from hS]
    simpa only [I, Fintype.card_prod, Fintype.card_fin] using commonStepCoverCell_capacity S.length t m hfit
  have hcapW : Fintype.card J * m ≤ 2 * T.carrier.card := by
    rw [show T.carrier.card = T.length from hT]
    simpa only [J, Fintype.card_prod, Fintype.card_fin] using
      commonStepCoverCell_capacity T.length 1 m (by simpa only [one_mul] using hmT)
  obtain ⟨i, j, hij⟩ := exists_dense_equal_product_cover S.carrier T.carrier D
    (fun i => (V i).carrier) (fun j => (W j).carrier) m delta hδ hsupport
    (fun _ hx => commonStepCoverCell_covers S ht hm hx)
    (fun _ hx => commonStepCoverCell_covers T (by omega) hm hx) hcapV hcapW
    (by simpa only [show S.carrier.card = S.length from hS,
      show T.carrier.card = T.length from hT] using hmass)
  have hmN : m ≤ N := hmT.trans (by
    rw [← hT]
    simpa only [ZMod.card] using Finset.card_le_univ T.carrier)
  have hVstep : (V i).step = T.step := hstepEq.symm
  have hWstep : (W j).step = T.step := by simp [W, commonStepCoverCell]
  let E := D ∩ (V i).carrier.product (W j).carrier
  refine ⟨V i, W j, E, hVstep, hWstep,
    (V i).isProper_of_prime_step (by rwa [hVstep]) hmN,
    (W j).isProper_of_prime_step (by rwa [hWstep]) hmN,
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
  classical
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

/-- Corollary 13.10 follows from a bounded integer step ratio. The actual
square is constructed by padded covers, without assuming a square-grid
partition or discarding endpoints of the dense set. -/
theorem corollary_13_10_of_integer_step_fit {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139Data S E G H J) (hS : G.S.IsProper)
    (hsupport : J.D ⊆ G.S.carrier.product (translateFinset J.U.carrier G.y))
    (hUpos : 0 < J.U.length) (t : Nat) (ht : 0 < t)
    (hstep : J.U.step = (t : ZMod N) * G.S.step)
    (hfit : t * Nat.sqrt J.U.length ≤ G.S.length) :
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧
      V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ J.D ∧ E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤ E'.card ∧
      BilinearOn E' S.phi := by
  let delta := (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704
  let T := J.U.translateBy G.y
  have hδ : 0 ≤ delta := mul_nonneg (zpow_nonneg (by norm_num) _) (pow_nonneg S.alpha_pos.le _)
  obtain ⟨V, W, E', hVstep, hWstep, hV, hW, hVl, hWl, hsub, hbox, hmass, hbilinear⟩ :=
    bilinear_square_of_integer_step_fit G.S T J.D S.phi delta t (Nat.sqrt J.U.length)
      hS (J.U.translateBy_isProper G.y h139.2.1) h139.1 hstep ht
      (Nat.sqrt_pos.mpr hUpos) hfit (Nat.sqrt_le_self _)
      hδ (by simpa only [T, J.U.translateBy_carrier] using hsupport)
      h139.2.2.2.2.2.2.1 h139.2.2.2.2.2.2.2
  refine ⟨V, W, E', ?_, hVstep.trans hWstep.symm, hV, hW, hVl.trans hWl.symm,
    ?_, hsub, hbox, ?_, hbilinear⟩
  · rw [hVstep]
    exact h139.1
  · rw [hVl, ← Real.sqrt_eq_rpow]
    have h := Real.real_sqrt_le_nat_sqrt_succ (a := J.U.length)
    linarith only [h]
  · rw [hVl, hWl]
    have hδeq : delta / 4 = (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 := by
      dsimp [delta]
      norm_num [zpow_neg]
      ring
    rwa [hδeq] at hmass

end LeanProofs.GowersSzemeredi
