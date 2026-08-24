import GowersSzemeredi.Sections01_03
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


private def singletonNatAP (x : Nat) : NatAP where
  start := x
  step := 1
  length := 1

@[simp] private lemma singletonNatAP_carrier (x : Nat) :
    (singletonNatAP x).carrier = {x} := by
  classical
  ext y
  simp [singletonNatAP, NatAP.carrier]

private def residueClassLength (r u a : Nat) : Nat :=
  (r - 1 - a) / u + 1

private lemma quotient_lt_residueClassLength {r u a q : Nat}
    (hu : 0 < u) (hau : a < u) (hur : u ≤ r) :
    q < residueClassLength r u a ↔ a + q * u < r := by
  have har : a ≤ r - 1 := by omega
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

private lemma residueChunkLength_pos {c L n j : Nat} (hL : 0 < L) :
    0 < residueChunkLength c L n j := by
  unfold residueChunkLength
  split_ifs <;> omega

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

private lemma chunkCount_pos {c L : Nat} (hL : 0 < L) (hLc : L ≤ c) :
    0 < c / L := by
  exact Nat.div_pos hLc hL

private lemma chunk_quotient_lt {c L : Nat} (j : Fin (c / L)) (i : Nat)
    (hi : i < residueChunkLength c L (c / L) j) :
    j * L + i < c := by
  have hdiv := Nat.div_add_mod c L
  by_cases hj : (j : Nat) + 1 = c / L
  · simp only [residueChunkLength, if_pos hj] at hi
    rw [← hj] at hdiv
    rw [Nat.mul_add, Nat.mul_one] at hdiv
    rw [Nat.mul_comm L (j : Nat)] at hdiv
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
  let n := c / L
  have hn : 0 < n := chunkCount_pos hL hLc
  by_cases hfront : q < n * L
  · let j : Fin n := ⟨q / L, (Nat.div_lt_iff_lt_mul hL).2 hfront⟩
    refine ⟨j, q % L, ?_, ?_⟩
    · have hmod : q % L < L := Nat.mod_lt q hL
      exact lt_of_lt_of_le hmod (residueChunkLength_ge (c := c) (L := L)
        (n := n) (j := j))
    · dsimp only [j, n]
      calc
        q = q % L + L * (q / L) := (Nat.mod_add_div q L).symm
        _ = (q / L) * L + q % L := by ac_rfl
  · have hqfront : n * L ≤ q := Nat.le_of_not_gt hfront
    let j : Fin n := ⟨n - 1, by omega⟩
    let i := q - (n - 1) * L
    refine ⟨j, i, ?_, ?_⟩
    · have hjlast : (j : Nat) + 1 = n := by
        change n - 1 + 1 = n
        omega
      change i < residueChunkLength c L n j
      simp only [residueChunkLength, hjlast, if_true]
      have hdiv := Nat.div_add_mod c L
      change i < L + c % L
      dsimp only [i]
      rw [Nat.mul_comm L n] at hdiv
      have hnstep : n * L = (n - 1) * L + L := by
        calc
          n * L = ((n - 1) + 1) * L := by rw [Nat.sub_add_cancel hn]
          _ = (n - 1) * L + L := by rw [Nat.add_mul, one_mul]
      omega
    · have hpre : (n - 1) * L ≤ n * L :=
        Nat.mul_le_mul_right L (Nat.sub_le n 1)
      change q = (n - 1) * L + (q - (n - 1) * L)
      omega

private lemma chunk_index_unique {c L q : Nat}
    (j j' : Fin (c / L)) (i i' : Nat)
    (hi : i < residueChunkLength c L (c / L) j)
    (hi' : i' < residueChunkLength c L (c / L) j')
    (hq : q = j * L + i) (hq' : q = j' * L + i') : j = j' := by
  apply Fin.ext
  by_contra hjne
  rcases lt_or_gt_of_ne hjne with hjlt | hjgt
  · have hjnotlast : (j : Nat) + 1 ≠ c / L := by
      intro hj
      have := j'.isLt
      omega
    simp only [residueChunkLength, if_neg hjnotlast] at hi
    have hstep : ((j : Nat) + 1) * L ≤ (j' : Nat) * L :=
      Nat.mul_le_mul_right L hjlt
    rw [Nat.add_mul] at hstep
    omega
  · have hjnotlast : (j' : Nat) + 1 ≠ c / L := by
      intro hj
      have := j.isLt
      omega
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
  classical
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

private lemma singletonNatAP_partition (r : Nat) :
    IsNatAPPartition (fun i : Fin r => singletonNatAP i) (Finset.range r) := by
  classical
  constructor
  · intro x
    simp only [Finset.mem_range, singletonNatAP_carrier, Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  · intro i j hij
    change Disjoint (singletonNatAP (i : Nat)).carrier
      (singletonNatAP (j : Nat)).carrier
    rw [singletonNatAP_carrier, singletonNatAP_carrier]
    exact Finset.disjoint_singleton.mpr fun h =>
      bne_iff_ne.mp hij (Fin.ext h)

private lemma residueChunkFamily_partition {r u L : Nat}
    (hu : 0 < u) (hur : u ≤ r) (hL : 0 < L)
    (hclass : ∀ a : Fin u, L ≤ residueClassLength r u a) :
    IsNatAPPartition (residueChunkFamily r u L) (Finset.range r) := by
  classical
  let E := Fintype.equivFin (ResidueChunkIndex r u L)
  constructor
  · intro x
    constructor
    · intro hx
      have hxr : x < r := Finset.mem_range.mp hx
      let a : Fin u := ⟨x % u, Nat.mod_lt x hu⟩
      let q := x / u
      have hq : q < residueClassLength r u a := by
        rw [quotient_lt_residueClassLength hu a.isLt hur]
        dsimp only [a, q]
        calc
          x % u + (x / u) * u = x := by
            simpa only [Nat.mul_comm] using Nat.mod_add_div x u
          _ < r := hxr
      obtain ⟨j, i, hi, hqrep⟩ :=
        exists_chunk_for_quotient hL (hclass a) hq
      let z : ResidueChunkIndex r u L := ⟨a, j⟩
      refine ⟨E z, ?_⟩
      change x ∈ (residueChunkAP r u L
        ((Fintype.equivFin _).symm (E z))).carrier
      have hez : (Fintype.equivFin _).symm (E z) = z := by
        simp only [E, Equiv.symm_apply_apply]
      rw [hez, residueChunkAP_mem_iff]
      refine ⟨i, hi, ?_⟩
      dsimp only [z]
      calc
        x = x % u + u * (x / u) := (Nat.mod_add_div x u).symm
        _ = a + q * u := by simp only [a, q, Nat.mul_comm]
        _ = a + (j * L + i) * u := by rw [hqrep]
    · rintro ⟨z, hz⟩
      let w := E.symm z
      change x ∈ (residueChunkAP r u L ((Fintype.equivFin _).symm z)).carrier at hz
      have hzw : (Fintype.equivFin _).symm z = w := by rfl
      rw [hzw, residueChunkAP_mem_iff] at hz
      obtain ⟨i, hi, rfl⟩ := hz
      apply Finset.mem_range.mpr
      rw [← quotient_lt_residueClassLength hu w.1.isLt hur]
      exact chunk_quotient_lt w.2 i hi
  · intro z z' hzz'
    rw [Finset.disjoint_left]
    intro x hx hx'
    let w := E.symm z
    let w' := E.symm z'
    change x ∈ (residueChunkAP r u L ((Fintype.equivFin _).symm z)).carrier at hx
    change x ∈ (residueChunkAP r u L ((Fintype.equivFin _).symm z')).carrier at hx'
    have hzw : (Fintype.equivFin _).symm z = w := by rfl
    have hzw' : (Fintype.equivFin _).symm z' = w' := by rfl
    rw [hzw, residueChunkAP_mem_iff] at hx
    rw [hzw', residueChunkAP_mem_iff] at hx'
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨i', hi', hxi'⟩ := hx'
    have haVal : (w.1 : Nat) = (w'.1 : Nat) := by
      have hm := congrArg (fun y : Nat => y % u) (hxi.symm.trans hxi')
      simpa only [Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt w.1.isLt, Nat.mod_eq_of_lt w'.1.isLt] using hm
    have ha : w.1 = w'.1 := Fin.ext haVal
    rcases w with ⟨a, j⟩
    rcases w' with ⟨a', j'⟩
    dsimp only at ha
    subst a'
    have hqmul : (j * L + i) * u = (j' * L + i') * u := by
      exact Nat.add_left_cancel (hxi.symm.trans hxi')
    have hq : j * L + i = j' * L + i' :=
      Nat.eq_of_mul_eq_mul_right hu hqmul
    have hj : j = j' := chunk_index_unique j j' i i' hi hi' rfl hq
    subst j'
    have hzEq : z = z' := by
      apply E.symm.injective
      exact hzw.trans hzw'.symm
    exact bne_iff_ne.mp hzz' hzEq

private lemma residueChunkFamily_isProper {r u L : Nat} (hu : 0 < u)
    (z : Fin (Fintype.card (ResidueChunkIndex r u L))) :
    (residueChunkFamily r u L z).IsProper := by
  change (residueChunkAP r u L ((Fintype.equivFin _).symm z)).IsProper
  exact residueChunkAP_isProper hu _

private lemma residueChunkFamily_length_ge {r u L : Nat}
    (z : Fin (Fintype.card (ResidueChunkIndex r u L))) :
    L ≤ (residueChunkFamily r u L z).length := by
  change L ≤ residueChunkLength
    (residueClassLength r u ((Fintype.equivFin _).symm z).1) L
    (residueClassLength r u ((Fintype.equivFin _).symm z).1 / L)
    ((Fintype.equivFin _).symm z).2
  exact residueChunkLength_ge

private lemma residueChunkFamily_length_lt {r u L : Nat} (hL : 0 < L)
    (z : Fin (Fintype.card (ResidueChunkIndex r u L))) :
    (residueChunkFamily r u L z).length < 2 * L := by
  change residueChunkLength
    (residueClassLength r u ((Fintype.equivFin _).symm z).1) L
    (residueClassLength r u ((Fintype.equivFin _).symm z).1 / L)
    ((Fintype.equivFin _).symm z).2 < 2 * L
  exact residueChunkLength_lt_two_mul hL

private lemma linear_image_diameter {N r s : Nat} [NeZero N]
    (phi : Nat → ZMod N) (a b : ZMod N)
    (hphi : ∀ x, x < r → phi x = a * (x : Nat) + b)
    (P : NatAP) (hP : P.carrier ⊆ Finset.range r)
    (hPpos : 0 < P.length)
    (hdiam : (P.length - 1) * centeredAbs (a * (P.step : ZMod N)) ≤ s) :
    diameterAtMost (P.carrier.image phi) s := by
  classical
  let d : ZMod N := a * (P.step : ZMod N)
  let base : ZMod N := a * (P.start : ZMod N) + b
  let h : Nat := centeredAbs d
  have hcast := ZMod.natCast_natAbs_valMinAbs d
  by_cases hdval : d.val ≤ N / 2
  · have hhcast : (h : ZMod N) = d := by
      simpa only [h, centeredAbs, hdval, if_true] using hcast
    refine ⟨base, ?_⟩
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hxP, rfl⟩ := hy
    rw [NatAP.carrier] at hxP
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxP
    obtain ⟨i, rfl⟩ := hxP
    have hiLe : (i : Nat) ≤ P.length - 1 := by omega
    let j : Nat := (i : Nat) * h
    have hjLe : j ≤ s := by
      have hmul := Nat.mul_le_mul_right h hiLe
      change (i : Nat) * h ≤ s
      exact hmul.trans hdiam
    change phi (P.start + (i : Nat) * P.step) ∈
      (modInterval N base (s + 1)).carrier
    rw [ModAP.carrier]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨j, ?_⟩, ?_⟩
    · change j < s + 1
      omega
    have hxRange : P.start + (i : Nat) * P.step < r :=
      Finset.mem_range.mp (hP (by
        rw [NatAP.carrier]
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, rfl⟩))
    rw [hphi _ hxRange]
    change base + (j : ZMod N) * 1 =
      a * (↑(P.start + (i : Nat) * P.step) : ZMod N) + b
    push_cast
    rw [show (j : ZMod N) = (i : Nat) * d by
      simp only [j, Nat.cast_mul, hhcast]]
    simp only [mul_one, d, base]
    ring
  · have hhcast : (h : ZMod N) = -d := by
      simpa only [h, centeredAbs, hdval, if_false] using hcast
    let start : ZMod N := base + (P.length - 1 : Nat) * d
    refine ⟨start, ?_⟩
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hxP, rfl⟩ := hy
    rw [NatAP.carrier] at hxP
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxP
    obtain ⟨i, rfl⟩ := hxP
    have hiLe : (i : Nat) ≤ P.length - 1 := by omega
    let j : Nat := (P.length - 1 - (i : Nat)) * h
    have hjLe : j ≤ s := by
      have hsub : P.length - 1 - (i : Nat) ≤ P.length - 1 := Nat.sub_le _ _
      have hmul := Nat.mul_le_mul_right h hsub
      change (P.length - 1 - (i : Nat)) * h ≤ s
      exact hmul.trans hdiam
    change phi (P.start + (i : Nat) * P.step) ∈
      (modInterval N start (s + 1)).carrier
    rw [ModAP.carrier]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨j, ?_⟩, ?_⟩
    · change j < s + 1
      omega
    have hxRange : P.start + (i : Nat) * P.step < r :=
      Finset.mem_range.mp (hP (by
        rw [NatAP.carrier]
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, rfl⟩))
    rw [hphi _ hxRange]
    change start + (j : ZMod N) * 1 =
      a * (↑(P.start + (i : Nat) * P.step) : ZMod N) + b
    push_cast
    have hjcast : (j : ZMod N) =
        (P.length - 1 - (i : Nat) : Nat) * (-d) := by
      simp only [j, Nat.cast_mul, hhcast]
    rw [hjcast]
    simp only [mul_one, start, d, base]
    rw [Nat.cast_sub hiLe]
    ring

private def partitionRatio (N r s : Nat) : Real :=
  Real.sqrt ((r : Real) * s / N)

private def approximationRatio (N r s : Nat) : Real :=
  Real.sqrt ((r : Real) * N / s)

private lemma ratio_product {N r s : Nat} (hN : 0 < N) (hs : 0 < s) :
    partitionRatio N r s * approximationRatio N r s = r := by
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hsreal : (0 : Real) < s := by exact_mod_cast hs
  have hA : 0 ≤ (r : Real) * s / N := by positivity
  rw [partitionRatio, approximationRatio, ← Real.sqrt_mul hA]
  have hprod : ((r : Real) * s / N) * ((r : Real) * N / s) = (r : Real) ^ 2 := by
    field_simp
  rw [hprod, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

private lemma partitionRatio_one_le {N r s : Nat} (hN : 0 < N)
    (hrs : N ≤ r * s) : 1 ≤ partitionRatio N r s := by
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  rw [partitionRatio, Real.one_le_sqrt]
  apply (le_div_iff₀ hNreal).2
  have hrsReal : (N : Real) ≤ (r : Real) * s := by exact_mod_cast hrs
  simpa only [one_mul] using hrsReal

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
  let q := partitionRatio N r s
  let x := approximationRatio N r s
  let t := Nat.ceil x
  have hqx : q ≤ x := partitionRatio_le_approximationRatio hN hs hsN
  have hx4 : (4 : Real) ≤ x := hq.trans hqx
  have hxt : x ≤ (t : Real) := Nat.le_ceil x
  have ht4 : 4 ≤ t := by exact_mod_cast hx4.trans hxt
  have ht : 0 < t := by omega
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  let xi : Real := (a.val : Real) / N
  obtain ⟨j, k, hkpos, hkt, happ⟩ :=
    Real.exists_int_int_abs_mul_sub_le xi ht
  let u : Nat := k.toNat
  have hku : (u : Int) = k := Int.toNat_of_nonneg hkpos.le
  have hu : 0 < u := by
    have hkupos : (0 : Int) < (u : Int) := by simpa only [hku] using hkpos
    exact_mod_cast hkupos
  have hut : u ≤ t := by
    have : (u : Int) ≤ (t : Int) := by simpa only [hku] using hkt
    exact_mod_cast this
  let z : Int := k * (a.val : Int) - j * (N : Int)
  have hzcast : (z : ZMod N) = (u : ZMod N) * a := by
    dsimp only [z]
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul]
    simp only [hku.symm, Int.cast_natCast, ZMod.natCast_self, mul_zero, sub_zero]
    rw [ZMod.natCast_zmod_val]
  have hzdiv : (z : Real) / N = (k : Real) * xi - j := by
    dsimp only [z, xi]
    push_cast
    field_simp
  have hzabs : |(z : Real)| ≤ (N : Real) / (t + 1) := by
    rw [← hzdiv, abs_div, abs_of_pos hNreal] at happ
    rw [div_le_iff₀ hNreal] at happ
    calc
      |(z : Real)| ≤ 1 / ((t : Real) + 1) * N := happ
      _ = (N : Real) / (t + 1) := by ring
  have hzhalf : |(z : Real)| < (N : Real) / 2 := by
    refine hzabs.trans_lt ?_
    exact div_lt_div_of_pos_left hNreal (by norm_num) (by exact_mod_cast (show 2 < t + 1 by omega))
  have hzinterval : z * 2 ∈ Set.Ioc (-(N : Int)) N := by
    have hzreal := (abs_lt.mp hzhalf)
    have hlow : -(N : Real) < (z : Real) * 2 := by nlinarith [hzreal.1]
    have hupp : (z : Real) * 2 ≤ N := by nlinarith [hzreal.2]
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hupp
  have hzmin : ((u : ZMod N) * a).valMinAbs = z :=
    (ZMod.valMinAbs_spec _ _).2 ⟨hzcast.symm, hzinterval⟩
  refine ⟨u, hu, hut, ?_⟩
  rw [centeredAbs, hzmin]
  simpa only [x, t, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] using hzabs

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
    _ = Real.sqrt ((partitionRatio N r s / 4) ^ 2) := by
      congr 1
      ring
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
  intro N r s hN hr hs hrN hsN hrs phi hlin
  rcases hlin with ⟨a, b, hphi⟩
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let q := partitionRatio N r s
  have hqnonneg : 0 ≤ q := Real.sqrt_nonneg _
  have hqpos : 0 < q := partitionRatio_pos hN hr hs
  have hqone : 1 ≤ q := partitionRatio_one_le hN hrs
  by_cases hqsmall : q < 4
  · refine ⟨r, fun i => singletonNatAP i, singletonNatAP_partition r, ?_⟩
    intro j
    have hsubset : (singletonNatAP (j : Nat)).carrier ⊆ Finset.range r := by
      intro y hy
      rw [singletonNatAP_carrier, Finset.mem_singleton] at hy
      subst y
      exact Finset.mem_range.mpr j.isLt
    have hproper : (singletonNatAP (j : Nat)).IsProper := by
      constructor
      · simp [singletonNatAP]
      · rw [singletonNatAP_carrier]
        simp [singletonNatAP]
    have hdiam : diameterAtMost
        ((singletonNatAP (j : Nat)).carrier.image phi) s :=
      linear_image_diameter phi a b hphi _ hsubset (by simp [singletonNatAP])
        (by simp [singletonNatAP])
    have hlower : Real.sqrt ((r : Real) * s / (16 * N)) ≤
        (singletonNatAP (j : Nat)).length := by
      rw [partitionRatio_quarter hN]
      have : q / 4 ≤ (1 : Real) := by linarith
      simpa only [singletonNatAP, q, Nat.cast_one] using this
    have hupper : ((singletonNatAP (j : Nat)).length : Real) ≤
        Real.sqrt ((r : Real) * s / N) := by
      simpa only [singletonNatAP, q, partitionRatio, Nat.cast_one] using hqone
    exact ⟨hproper, hdiam, hlower, hupper⟩
  · have hqfour : (4 : Real) ≤ q := le_of_not_gt hqsmall
    let x := approximationRatio N r s
    let t := Nat.ceil x
    let L := Nat.floor (q / 2)
    have hxpos : 0 < x := approximationRatio_pos hN hr hs
    have hqx : q ≤ x := partitionRatio_le_approximationRatio hN hs hsN
    have hxfour : (4 : Real) ≤ x := hqfour.trans hqx
    have hxt : x ≤ (t : Real) := by
      simpa only [t] using Nat.le_ceil x
    have htlt : (t : Real) < x + 1 := by
      simpa only [t] using Nat.ceil_lt_add_one hxpos.le
    have hLle : (L : Real) ≤ q / 2 := by
      simpa only [L] using Nat.floor_le (show 0 ≤ q / 2 by positivity)
    have hqhalfLt : q / 2 < (L : Real) + 1 := by
      simpa only [L] using Nat.lt_floor_add_one (q / 2)
    have hLpos : 0 < L := by
      have hLone : 1 ≤ L := by
        dsimp only [L]
        apply Nat.le_floor
        norm_num
        linarith
      omega
    obtain ⟨u, hu, hut, hsmall⟩ :=
      exists_small_image_step hN hs hsN a hqfour
    have huReal : (u : Real) ≤ t := by exact_mod_cast hut
    have huX : (u : Real) ≤ x + 1 := huReal.trans htlt.le
    have hLuReal : (L : Real) * u ≤ r := by
      calc
        (L : Real) * u ≤ (q / 2) * (x + 1) := by
          exact mul_le_mul hLle huX (by positivity) (by positivity)
        _ ≤ q * x := by
          have hxone : (1 : Real) ≤ x := by linarith
          nlinarith [mul_nonneg hqnonneg (sub_nonneg.mpr hxone)]
        _ = r := ratio_product hN hs
    have hLu : L * u ≤ r := by exact_mod_cast hLuReal
    have hur : u ≤ r := by
      have : u ≤ L * u := by nlinarith
      exact this.trans hLu
    have hclass : ∀ z : Fin u, L ≤ residueClassLength r u z := by
      intro z
      have hzbound : (z : Nat) + (L - 1) * u < r := by
        have hzlt : (z : Nat) < u := z.isLt
        have hsplit : u + (L - 1) * u = L * u := by
          calc
            u + (L - 1) * u = (L - 1) * u + u := by ac_rfl
            _ = ((L - 1) + 1) * u := by rw [Nat.add_mul, one_mul]
            _ = L * u := by congr 1; omega
        calc
          (z : Nat) + (L - 1) * u < u + (L - 1) * u :=
            Nat.add_lt_add_right hzlt _
          _ = L * u := hsplit
          _ ≤ r := hLu
      have hquot : L - 1 < residueClassLength r u z :=
        (quotient_lt_residueClassLength hu z.isLt hur).2 hzbound
      omega
    have hpart := residueChunkFamily_partition hu hur hLpos hclass
    refine ⟨Fintype.card (ResidueChunkIndex r u L),
      residueChunkFamily r u L, hpart, ?_⟩
    intro j
    let P := residueChunkFamily r u L j
    have hPproper : P.IsProper := residueChunkFamily_isProper hu j
    have hPge : L ≤ P.length := residueChunkFamily_length_ge j
    have hPlt : P.length < 2 * L := residueChunkFamily_length_lt hLpos j
    have hqQuarterLeL : q / 4 ≤ (L : Real) := by
      nlinarith
    have hPgeReal : (L : Real) ≤ P.length := by exact_mod_cast hPge
    have hPltReal : (P.length : Real) < 2 * L := by exact_mod_cast hPlt
    have htwoLLe : (2 : Real) * L ≤ q := by nlinarith
    have hPleQ : (P.length : Real) ≤ q :=
      le_of_lt (hPltReal.trans_le htwoLLe)
    have hPsubset : P.carrier ⊆ Finset.range r := by
      intro y hy
      exact (hpart.1 y).2 ⟨j, hy⟩
    have hstep : (centeredAbs (a * (P.step : ZMod N)) : Real) ≤
        (N : Real) / (t + 1) := by
      simpa only [P, residueChunkFamily, residueChunkAP, mul_comm, t, x] using hsmall
    have hfrac : (N : Real) / (t + 1) ≤ (N : Real) / x := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg N) hxpos
      linarith
    have hdiamReal :
        (((P.length - 1) * centeredAbs (a * (P.step : ZMod N)) : Nat) : Real) ≤ s := by
      rw [Nat.cast_mul]
      calc
        ((P.length - 1 : Nat) : Real) *
              (centeredAbs (a * (P.step : ZMod N)) : Real) ≤
            (P.length : Real) * ((N : Real) / (t + 1)) := by
          exact mul_le_mul (by exact_mod_cast (Nat.sub_le P.length 1)) hstep
            (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ ≤ q * ((N : Real) / (t + 1)) :=
          mul_le_mul_of_nonneg_right hPleQ (by positivity)
        _ ≤ q * ((N : Real) / x) :=
          mul_le_mul_of_nonneg_left hfrac hqnonneg
        _ = q * N / x := by ring
        _ = s := ratio_scaled_quotient hN hr hs
    have hdiamNat :
        (P.length - 1) * centeredAbs (a * (P.step : ZMod N)) ≤ s := by
      exact_mod_cast hdiamReal
    have hPdiam : diameterAtMost (P.carrier.image phi) s :=
      linear_image_diameter phi a b hphi P hPsubset
        (lt_of_lt_of_le hLpos hPge) hdiamNat
    have hlower : Real.sqrt ((r : Real) * s / (16 * N)) ≤ P.length := by
      rw [partitionRatio_quarter hN]
      exact hqQuarterLeL.trans hPgeReal
    have hupper : (P.length : Real) ≤ Real.sqrt ((r : Real) * s / N) := by
      exact hPleQ
    exact ⟨hPproper, hPdiam, hlower, hupper⟩

end LeanProofs.GowersSzemeredi
