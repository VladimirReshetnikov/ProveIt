import GowersSzemeredi.Sections01_03
import GowersSzemeredi.ProofInfrastructure
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Linear-phase progression partitions in Gowers's Section 2

This module proves the rounding-corrected Lemma 2.3.  The construction uses
Dirichlet approximation to find a short domain step whose image has small
centered residue, then divides every congruence class into consecutive blocks.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def residueClassLength (r u a : Nat) : Nat :=
  (r - 1 - a) / u + 1

private lemma quotient_lt_residueClassLength {r u a q : Nat}
    (hu : 0 < u) (hau : a < u) (hur : u ≤ r) :
    q < residueClassLength r u a ↔ a + q * u < r := by
  rw [residueClassLength, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hu]
  omega

private def residueChunkLength (c L n j : Nat) : Nat :=
  if j + 1 = n then L + c % L else L

private abbrev ResidueChunkIndex (r u L : Nat) :=
  Σ a : Fin u, Fin (residueClassLength r u a / L)

private def residueChunkAP (r u L : Nat) (z : ResidueChunkIndex r u L) : NatAP where
  start := z.1 + (z.2 * L) * u
  step := u
  length := residueChunkLength (residueClassLength r u z.1) L
    (residueClassLength r u z.1 / L) z.2

private lemma residueChunkLength_ge {c L n j : Nat} :
    L ≤ residueChunkLength c L n j := by
  unfold residueChunkLength
  split_ifs <;> omega

private lemma residueChunkLength_lt_two_mul {c L n j : Nat} (hL : 0 < L) :
    residueChunkLength c L n j < 2 * L := by
  unfold residueChunkLength
  split_ifs
  · have := Nat.mod_lt c hL
    omega
  · omega

private lemma chunk_quotient_lt {c L : Nat} (j : Fin (c / L)) (i : Nat)
    (hi : i < residueChunkLength c L (c / L) j) :
    j * L + i < c := by
  have hdiv := Nat.div_add_mod c L
  by_cases hj : (j : Nat) + 1 = c / L
  · simp only [residueChunkLength, if_pos hj] at hi
    rw [← hj, Nat.mul_add, Nat.mul_one, Nat.mul_comm L (j : Nat)] at hdiv
    omega
  · simp only [residueChunkLength, if_neg hj] at hi
    have hjlt : (j : Nat) + 1 < c / L := Nat.lt_of_le_of_ne j.isLt hj
    have hmul : ((j : Nat) + 1) * L ≤ (c / L) * L :=
      Nat.mul_le_mul_right L hjlt.le
    have hfloor : (c / L) * L ≤ c := Nat.div_mul_le_self c L
    rw [Nat.add_mul] at hmul
    omega

private lemma exists_chunk_for_quotient {c L q : Nat}
    (hL : 0 < L) (hLc : L ≤ c) (hq : q < c) :
    ∃ j : Fin (c / L), ∃ i : Nat,
      i < residueChunkLength c L (c / L) j ∧ q = j * L + i := by
  have hn : 1 ≤ c / L := Nat.div_pos hLc hL
  by_cases hfront : q / L < c / L
  · exact ⟨⟨q / L, hfront⟩, q % L, (Nat.mod_lt q hL).trans_le residueChunkLength_ge,
      (Nat.div_add_mod' q L).symm⟩
  -- otherwise `q` lies in the last chunk, which also absorbs the remainder `c % L`
  have hc := Nat.div_add_mod' c L
  have hqL := (Nat.le_div_iff_mul_le hL).1 (not_lt.1 hfront)
  have hstep : (c / L - 1) * L + L = c / L * L := by
    rw [← add_one_mul, Nat.sub_add_cancel hn]
  refine ⟨⟨c / L - 1, by omega⟩, q - (c / L - 1) * L, ?_, by dsimp only; omega⟩
  simp only [residueChunkLength, Nat.sub_add_cancel hn, if_true]
  omega

private lemma chunk_index_unique {c L q : Nat}
    (j j' : Fin (c / L)) (i i' : Nat)
    (hi : i < residueChunkLength c L (c / L) j)
    (hi' : i' < residueChunkLength c L (c / L) j')
    (hq : q = j * L + i) (hq' : q = j' * L + i') : j = j' := by
  apply Fin.ext
  by_contra hjne
  rcases lt_or_gt_of_ne hjne with hjlt | hjgt
  · have hjnotlast : (j : Nat) + 1 ≠ c / L := by omega
    simp only [residueChunkLength, if_neg hjnotlast] at hi
    have hstep : ((j : Nat) + 1) * L ≤ (j' : Nat) * L :=
      Nat.mul_le_mul_right L hjlt
    rw [Nat.add_mul] at hstep
    omega
  · have hjnotlast : (j' : Nat) + 1 ≠ c / L := by omega
    simp only [residueChunkLength, if_neg hjnotlast] at hi'
    have hstep : ((j' : Nat) + 1) * L ≤ (j : Nat) * L :=
      Nat.mul_le_mul_right L hjgt
    rw [Nat.add_mul] at hstep
    omega

private lemma residueChunkAP_mem_iff {r u L : Nat}
    (z : ResidueChunkIndex r u L) (x : Nat) :
    x ∈ (residueChunkAP r u L z).carrier ↔
      ∃ i, i < residueChunkLength (residueClassLength r u z.1) L
          (residueClassLength r u z.1 / L) z.2 ∧
        x = z.1 + (z.2 * L + i) * u := by
  rw [residueChunkAP, NatAP.carrier]
  constructor
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨i, i.isLt, ?_⟩
    simp [Nat.add_mul, Nat.add_assoc]
  · rintro ⟨i, hi, rfl⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i, hi⟩, ?_⟩
    simp [Nat.add_mul, Nat.add_assoc]

private lemma residueChunkAP_isProper {r u L : Nat}
    (hu : 0 < u) (z : ResidueChunkIndex r u L) :
    (residueChunkAP r u L z).IsProper := by
  constructor
  · exact hu
  · classical
    rw [NatAP.carrier]
    have hinj : Function.Injective
        (fun i : Fin (residueChunkAP r u L z).length =>
          (residueChunkAP r u L z).start + (i : Nat) *
            (residueChunkAP r u L z).step) := by
      intro i j hij
      simp only [residueChunkAP] at hij
      have hmul : (i : Nat) * u = (j : Nat) * u := Nat.add_left_cancel hij
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right hu hmul)
    rw [Finset.card_image_iff.mpr hinj.injOn, Finset.card_univ, Fintype.card_fin]

private noncomputable def residueChunkFamily (r u L : Nat) :
    Fin (Fintype.card (ResidueChunkIndex r u L)) → NatAP :=
  fun i => residueChunkAP r u L ((Fintype.equivFin _).symm i)

private lemma residueChunkFamily_partition {r u L : Nat}
    (hu : 0 < u) (hur : u ≤ r) (hL : 0 < L)
    (hclass : ∀ a : Fin u, L ≤ residueClassLength r u a) :
    IsNatAPPartition (residueChunkFamily r u L) (Finset.range r) := by
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun z z' hzz' => Finset.disjoint_left.2 fun x hx hx' => ?_⟩
  · -- `x` lies in chunk `j` of its residue class `a`
    let a : Fin u := ⟨x % u, Nat.mod_lt x hu⟩
    obtain ⟨j, i, hi, hq⟩ := exists_chunk_for_quotient hL (hclass a)
      ((quotient_lt_residueClassLength hu a.isLt hur).2
        ((Nat.mod_add_div' x u).trans_lt (Finset.mem_range.mp hx)))
    refine ⟨Fintype.equivFin (ResidueChunkIndex r u L) ⟨a, j⟩, ?_⟩
    simp only [residueChunkFamily, Equiv.symm_apply_apply, residueChunkAP_mem_iff]
    exact ⟨i, hi, by rw [← hq]; exact (Nat.mod_add_div' x u).symm⟩
  · rintro ⟨z, hz⟩
    simp only [residueChunkFamily, residueChunkAP_mem_iff] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    exact Finset.mem_range.2 ((quotient_lt_residueClassLength hu (Fin.isLt _) hur).1
      (chunk_quotient_lt _ i hi))
  · -- a common point has the same residue class and the same quotient in both chunks
    rcases hw : (Fintype.equivFin (ResidueChunkIndex r u L)).symm z with ⟨a, j⟩
    rcases hw' : (Fintype.equivFin (ResidueChunkIndex r u L)).symm z' with ⟨a', j'⟩
    simp only [residueChunkFamily, hw, hw', residueChunkAP_mem_iff] at hx hx'
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨i', hi', hxi'⟩ := hx'
    have h := hxi.symm.trans hxi'
    obtain rfl : a = a' := Fin.ext (by
      simpa only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt,
        Nat.mod_eq_of_lt a'.isLt] using congrArg (· % u) h)
    obtain rfl := chunk_index_unique j j' i i' hi hi' rfl
      (Nat.eq_of_mul_eq_mul_right hu (Nat.add_left_cancel h))
    exact bne_iff_ne.mp hzz' ((Fintype.equivFin _).symm.injective (hw.trans hw'.symm))

private lemma linear_image_diameter {N r s : Nat} [NeZero N]
    (phi : Nat → ZMod N) (a b : ZMod N)
    (hphi : ∀ x, x < r → phi x = a * (x : Nat) + b)
    (P : NatAP) (hP : P.carrier ⊆ Finset.range r)
    (hdiam : (P.length - 1) * centeredAbs (a * (P.step : ZMod N)) ≤ s) :
    diameterAtMost (P.carrier.image phi) s := by
  -- it suffices to write every image point as `c + k * |a * step|` with `k ≤ length - 1`
  suffices H : ∃ c : ZMod N, ∀ i < P.length, ∃ k ≤ P.length - 1,
      c + ((k * centeredAbs (a * (P.step : ZMod N)) : Nat) : ZMod N) =
        a * ((P.start + i * P.step : Nat) : ZMod N) + b by
    obtain ⟨c, hc⟩ := H
    refine ⟨c, fun y hy => ?_⟩
    obtain ⟨x, hxP, rfl⟩ := Finset.mem_image.1 hy
    have hxr := Finset.mem_range.1 (hP hxP)
    simp only [NatAP.carrier, Finset.mem_image, Finset.mem_univ, true_and] at hxP
    obtain ⟨i, rfl⟩ := hxP
    obtain ⟨k, hk, hck⟩ := hc i i.isLt
    simp only [ModAP.carrier, modInterval, Finset.mem_image, Finset.mem_univ, true_and, mul_one,
      hphi _ hxr]
    exact ⟨⟨_, Nat.lt_succ_of_le ((Nat.mul_le_mul_right _ hk).trans hdiam)⟩, hck⟩
  have hcast : (centeredAbs (a * (P.step : ZMod N)) : ZMod N) = _ :=
    ZMod.natCast_natAbs_valMinAbs (a * (P.step : ZMod N))
  split_ifs at hcast
  · exact ⟨a * P.start + b, fun i hi => ⟨i, by omega, by push_cast [hcast]; ring⟩⟩
  · refine ⟨a * P.start + b + ((P.length - 1 : Nat) : ZMod N) * (a * P.step),
      fun i hi => ⟨P.length - 1 - i, Nat.sub_le _ _, ?_⟩⟩
    rw [Nat.cast_mul, hcast, Nat.cast_sub (show i ≤ P.length - 1 by omega)]
    push_cast
    ring

private def partitionRatio (N r s : Nat) : Real :=
  Real.sqrt ((r : Real) * s / N)

private def approximationRatio (N r s : Nat) : Real :=
  Real.sqrt ((r : Real) * N / s)

private lemma ratio_product {N r s : Nat} (hN : 0 < N) (hs : 0 < s) :
    partitionRatio N r s * approximationRatio N r s = r := by
  have hA : 0 ≤ (r : Real) * s / N := by positivity
  rw [partitionRatio, approximationRatio, ← Real.sqrt_mul hA]
  have hprod : ((r : Real) * s / N) * ((r : Real) * N / s) = (r : Real) ^ 2 := by
    field_simp
  rw [hprod, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

private lemma partitionRatio_le_approximationRatio {N r s : Nat}
    (hN : 0 < N) (hs : 0 < s) (hsN : s ≤ N) :
    partitionRatio N r s ≤ approximationRatio N r s := by
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hsreal : (0 : Real) < s := by exact_mod_cast hs
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ hNreal hsreal).2
  have hsNreal : (s : Real) ≤ N := by exact_mod_cast hsN
  have hsq : (s : Real) ^ 2 ≤ (N : Real) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg r : (0 : Real) ≤ r)
  simpa only [pow_two, mul_assoc] using hmul

private lemma exists_small_image_step {N r s : Nat} (hN : 0 < N)
    (hs : 0 < s) (hsN : s ≤ N) (a : ZMod N)
    (hq : 4 ≤ partitionRatio N r s) :
    let t := Nat.ceil (approximationRatio N r s)
    ∃ u : Nat, 0 < u ∧ u ≤ t ∧
      (centeredAbs ((u : ZMod N) * a) : Real) ≤
        (N : Real) / (t + 1) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  intro t
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have ht : 0 < t :=
    Nat.ceil_pos.2 (by linarith [partitionRatio_le_approximationRatio (r := r) hN hs hsN])
  -- Dirichlet: `u * (a.val / N)` is within `1 / (t + 1)` of an integer `j`
  obtain ⟨u, hu, hut, happ⟩ := Real.exists_nat_abs_mul_sub_round_le ((a.val : Real) / N) ht
  generalize round ((u : Real) * (a.val / N)) = j at happ
  -- so `u * a` has the representative `u * a.val - j * N`, whose size is at most `N / (t + 1)`
  have hz : ((u * a.val - j * N : Int) : ZMod N) = (u : ZMod N) * a := by simp
  have hle := ZMod.natAbs_min_of_le_div_two N _ _ ((ZMod.coe_valMinAbs _).trans hz.symm)
    (ZMod.natAbs_valMinAbs_le _)
  refine ⟨u, hu, hut, (Nat.cast_le.2 hle).trans ?_⟩
  rw [Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [show (u * a.val - j * N : Real) = N * (u * (a.val / N) - j) by field_simp, abs_mul,
    abs_of_pos hNreal]
  exact (mul_le_mul_of_nonneg_left happ hNreal.le).trans_eq (mul_one_div _ _)

private lemma partitionRatio_sq {N r s : Nat} (hN : 0 < N) :
    partitionRatio N r s ^ 2 = (r : Real) * s / N := by
  rw [partitionRatio, Real.sq_sqrt]
  positivity

private lemma partitionRatio_pos {N r s : Nat} (hN : 0 < N)
    (hr : 0 < r) (hs : 0 < s) : 0 < partitionRatio N r s := by
  rw [partitionRatio]
  exact Real.sqrt_pos.2 (by positivity)

private lemma approximationRatio_pos {N r s : Nat} (hN : 0 < N)
    (hr : 0 < r) (hs : 0 < s) : 0 < approximationRatio N r s := by
  rw [approximationRatio]
  exact Real.sqrt_pos.2 (by positivity)

private lemma partitionRatio_quarter {N r s : Nat} (hN : 0 < N) :
    Real.sqrt ((r : Real) * s / (16 * N)) = partitionRatio N r s / 4 := by
  have hqnonneg : 0 ≤ partitionRatio N r s := Real.sqrt_nonneg _
  calc
    Real.sqrt ((r : Real) * s / (16 * N)) =
        Real.sqrt (partitionRatio N r s ^ 2 / 16) := by
      congr 1
      rw [partitionRatio_sq hN]
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp
    _ = Real.sqrt ((partitionRatio N r s / 4) ^ 2) := by ring
    _ = |partitionRatio N r s / 4| := Real.sqrt_sq_eq_abs _
    _ = partitionRatio N r s / 4 := abs_of_nonneg (by positivity)

private lemma ratio_scaled_quotient {N r s : Nat} (hN : 0 < N)
    (hr : 0 < r) (hs : 0 < s) :
    partitionRatio N r s * N / approximationRatio N r s = s := by
  let q := partitionRatio N r s
  let x := approximationRatio N r s
  have hqpos : 0 < q := partitionRatio_pos hN hr hs
  have hqx : q * x = r := ratio_product hN hs
  have hqSq : q ^ 2 = (r : Real) * s / N := partitionRatio_sq hN
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hqSqN : q ^ 2 * N = (r : Real) * s := by
    rw [hqSq]
    field_simp
  have hmul : q * (q * N) = q * ((s : Real) * x) := by
    calc
      q * (q * N) = q ^ 2 * N := by ring
      _ = (r : Real) * s := hqSqN
      _ = (s : Real) * (q * x) := by rw [hqx]; ring
      _ = q * ((s : Real) * x) := by ring
  have hbase : q * N = (s : Real) * x := mul_left_cancel₀ hqpos.ne' hmul
  have hxpos : 0 < x := approximationRatio_pos hN hr hs
  change q * N / x = s
  exact (div_eq_iff hxpos.ne').2 (by simpa only [mul_comm] using hbase)

/-- The rounding-corrected form of Gowers's Lemma 2.3. -/
theorem lemma_2_3_holds : lemma_2_3 := by
  intro N r s hN hr hs _ hsN hrs phi hlin
  rcases hlin with ⟨a, b, hphi⟩
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let q := partitionRatio N r s
  have hqnonneg : 0 ≤ q := Real.sqrt_nonneg _
  by_cases hqsmall : q < 4
  · -- small ratio: the singleton partition
    refine ⟨r, fun i => singletonNatAP i, singletonNatAP_partition r, fun j =>
      ⟨singletonNatAP_isProper j, linear_image_diameter phi a b hphi _ (by simp)
        (by simp [singletonNatAP]), ?_, ?_⟩⟩
    · rw [partitionRatio_quarter hN]
      simp only [singletonNatAP, Nat.cast_one]
      show q / 4 ≤ 1
      linarith
    · simp only [singletonNatAP, Nat.cast_one]
      exact Real.one_le_sqrt.2 ((one_le_div (by positivity)).2 (by exact_mod_cast hrs))
  -- large ratio: chunks of length `L = ⌊q / 2⌋` in the residue classes of a small step `u`
  have hq4 : (4 : Real) ≤ q := le_of_not_gt hqsmall
  let x := approximationRatio N r s
  let L := Nat.floor (q / 2)
  have hxpos : 0 < x := approximationRatio_pos hN hr hs
  have hqx : q ≤ x := partitionRatio_le_approximationRatio hN hs hsN
  have hLle : (L : Real) ≤ q / 2 := Nat.floor_le (by positivity)
  have hqL : q / 2 < (L : Real) + 1 := Nat.lt_floor_add_one (q / 2)
  have hLpos : 0 < L := Nat.floor_pos.2 (by linarith)
  obtain ⟨u, hu, hut, hsmall⟩ := exists_small_image_step hN hs hsN a hq4
  have hLu : L * u ≤ r := by
    have hu' : (u : Real) ≤ x + 1 :=
      (Nat.cast_le.2 hut).trans (Nat.ceil_lt_add_one hxpos.le).le
    have : (L : Real) * u ≤ q * x := by
      linarith [mul_le_mul hLle hu' (by positivity) (by positivity),
        mul_le_mul_of_nonneg_left (show (1 : Real) ≤ x by linarith) hqnonneg]
    exact_mod_cast this.trans_eq (ratio_product hN hs)
  have hur : u ≤ r := (Nat.le_mul_of_pos_left u hLpos).trans hLu
  have hsplit : (L - 1) * u + u = L * u := by
    rw [← add_one_mul, Nat.sub_add_cancel (show 1 ≤ L from hLpos)]
  have hclass : ∀ z : Fin u, L ≤ residueClassLength r u z := fun z => by
    have := z.isLt
    have := (quotient_lt_residueClassLength (q := L - 1) hu z.isLt hur).2 (by omega)
    omega
  have hpart := residueChunkFamily_partition hu hur hLpos hclass
  have hstep : (centeredAbs (a * (u : ZMod N)) : Real) ≤ N / x := by
    rw [mul_comm]
    exact hsmall.trans (div_le_div_of_nonneg_left (by positivity) hxpos
      ((Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le_one)))
  refine ⟨_, residueChunkFamily r u L, hpart, fun j => ?_⟩
  let P := residueChunkFamily r u L j
  have hPlen : L ≤ P.length ∧ P.length < 2 * L := by
    simp only [P, residueChunkFamily, residueChunkAP]
    exact ⟨residueChunkLength_ge, residueChunkLength_lt_two_mul hLpos⟩
  have hPq : (P.length : Real) ≤ q := by
    have : (P.length : Real) < 2 * L := by exact_mod_cast hPlen.2
    linarith
  -- the image of `P` has diameter at most `(length - 1) * |a * u| ≤ q * N / x = s`
  have hdiam : ((P.length - 1 : Nat) : Real) * centeredAbs (a * (u : ZMod N)) ≤ s :=
    (mul_le_mul ((Nat.cast_le.2 (Nat.sub_le _ 1)).trans hPq) hstep (by positivity)
      hqnonneg).trans_eq ((mul_div_assoc' _ _ _).trans (ratio_scaled_quotient hN hr hs))
  refine ⟨residueChunkAP_isProper hu _, linear_image_diameter phi a b hphi P
    (fun y hy => (hpart.1 y).2 ⟨j, hy⟩) (by exact_mod_cast hdiam),
    ?_, hPq⟩
  rw [partitionRatio_quarter hN]
  have : (L : Real) ≤ P.length := by exact_mod_cast hPlen.1
  have : (1 : Real) ≤ L := by exact_mod_cast hLpos
  show q / 4 ≤ (P.length : Real)
  linarith

end LeanProofs.GowersSzemeredi
