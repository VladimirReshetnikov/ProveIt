import GowersSzemeredi.Proofs07BohrHom
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Simultaneous affine-linearity on integer progressions

This module supplies the arithmetic-progression partition used in Gowers's
Corollary 7.11.  In contrast with the informal cyclic-group argument, the
partition is constructed in integer coordinates from residue classes of a
small centered representative.  Each residue class is divided into balanced
blocks, so every cell has exactly `m` or `m + 1` terms.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def intAPPoint (R : IntAP) (j : Nat) : Int :=
  R.start + (j * R.step : Nat)

private def residueClassLength (r d a : Nat) : Nat :=
  (r - 1 - a) / d + 1

private lemma quotient_lt_residueClassLength {r d a t : Nat}
    (hd : 0 < d) (had : a < d) (hdr : d <= r) :
    t < residueClassLength r d a ↔ a + t * d < r := by
  have har : a <= r - 1 := by omega
  rw [residueClassLength, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
  omega

private def balancedChunkStart (m b j : Nat) : Nat :=
  j * m + min j b

private def balancedChunkLength (m b j : Nat) : Nat :=
  if j < b then m + 1 else m

private lemma balancedChunkStart_of_lt {m b j : Nat} (hjb : j < b) :
    balancedChunkStart m b j = j * (m + 1) := by
  rw [balancedChunkStart, min_eq_left hjb.le]
  rw [Nat.mul_add, Nat.mul_one]

private lemma balancedChunkStart_of_ge {m b j : Nat} (hbj : b <= j) :
    balancedChunkStart m b j = j * m + b := by
  rw [balancedChunkStart, min_eq_right hbj]

private lemma balancedChunkLength_of_lt {m b j : Nat} (hjb : j < b) :
    balancedChunkLength m b j = m + 1 := by
  simp [balancedChunkLength, hjb]

private lemma balancedChunkLength_of_ge {m b j : Nat} (hbj : b <= j) :
    balancedChunkLength m b j = m := by
  simp [balancedChunkLength, Nat.not_lt.mpr hbj]

private lemma balancedChunk_end (m b j : Nat) :
    balancedChunkStart m b j + balancedChunkLength m b j =
      balancedChunkStart m b (j + 1) := by
  by_cases hjb : j < b
  · have hsucc : j + 1 <= b := by omega
    rw [balancedChunkStart_of_lt hjb, balancedChunkLength_of_lt hjb,
      balancedChunkStart, min_eq_left hsucc]
    ring
  · have hbj : b <= j := Nat.le_of_not_gt hjb
    have hsucc : b <= j + 1 := hbj.trans (Nat.le_succ _)
    rw [balancedChunkStart_of_ge hbj, balancedChunkLength_of_ge hbj,
      balancedChunkStart_of_ge hsucc]
    ring

private lemma balancedChunkStart_mono {m b j k : Nat} (hjk : j <= k) :
    balancedChunkStart m b j <= balancedChunkStart m b k := by
  unfold balancedChunkStart
  exact Nat.add_le_add (Nat.mul_le_mul_right m hjk) (min_le_min hjk le_rfl)

private lemma remainder_le_quotient {c m : Nat} (hm : 0 < m)
    (hcm : m * m <= c) : c % m <= c / m := by
  have hmq : m <= c / m := (Nat.le_div_iff_mul_le hm).2 hcm
  exact (Nat.mod_lt c hm).le.trans hmq

private lemma balancedChunk_quotient_lt {c m : Nat}
    (hm : 0 < m) (hcm : m * m <= c) (j : Fin (c / m)) (i : Nat)
    (hi : i < balancedChunkLength m (c % m) j) :
    balancedChunkStart m (c % m) j + i < c := by
  have hbq : c % m <= c / m := remainder_le_quotient hm hcm
  calc
    balancedChunkStart m (c % m) j + i <
        balancedChunkStart m (c % m) j +
          balancedChunkLength m (c % m) j := Nat.add_lt_add_left hi _
    _ = balancedChunkStart m (c % m) ((j : Nat) + 1) :=
      balancedChunk_end _ _ _
    _ <= balancedChunkStart m (c % m) (c / m) :=
      balancedChunkStart_mono j.isLt
    _ = (c / m) * m + c % m := balancedChunkStart_of_ge hbq
    _ = c := by simpa only [Nat.mul_comm] using Nat.div_add_mod c m

private lemma exists_balancedChunk_for_quotient {c m t : Nat}
    (hm : 0 < m) (hcm : m * m <= c) (ht : t < c) :
    exists j : Fin (c / m), exists i : Nat,
      i < balancedChunkLength m (c % m) j /\
      t = balancedChunkStart m (c % m) j + i := by
  let n := c / m
  let b := c % m
  have hdecomp : c = n * m + b := by
    simpa only [n, b, Nat.mul_comm] using (Nat.div_add_mod c m).symm
  have hbn : b <= n := remainder_le_quotient hm hcm
  by_cases hfront : t < b * (m + 1)
  · let j : Fin n := ⟨t / (m + 1), by
      have hmp : 0 < m + 1 := by omega
      have hjb : t / (m + 1) < b := (Nat.div_lt_iff_lt_mul hmp).2 hfront
      exact hjb.trans_le hbn⟩
    let i := t % (m + 1)
    have hjb : (j : Nat) < b := by
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).2 hfront
    refine ⟨j, i, ?_, ?_⟩
    · rw [balancedChunkLength_of_lt hjb]
      exact Nat.mod_lt _ (by omega)
    · rw [balancedChunkStart_of_lt hjb]
      dsimp only [i, j]
      calc
        t = t % (m + 1) + (m + 1) * (t / (m + 1)) :=
          (Nat.mod_add_div t (m + 1)).symm
        _ = (t / (m + 1)) * (m + 1) + t % (m + 1) := by ac_rfl
  · have hback : b * (m + 1) <= t := Nat.le_of_not_gt hfront
    let u := t - b * (m + 1)
    have hu : u < (n - b) * m := by
      have hrewrite : c = b * (m + 1) + (n - b) * m := by
        rw [hdecomp]
        calc
          n * m + b = (b + (n - b)) * m + b := by rw [Nat.add_sub_of_le hbn]
          _ = b * m + (n - b) * m + b := by rw [Nat.add_mul]
          _ = b * (m + 1) + (n - b) * m := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
      dsimp only [u]
      omega
    let j : Fin n := ⟨b + u / m, by
      have huq : u / m < n - b := (Nat.div_lt_iff_lt_mul hm).2 hu
      omega⟩
    let i := u % m
    have hbj : b <= (j : Nat) := by simp [j]
    refine ⟨j, i, ?_, ?_⟩
    · rw [balancedChunkLength_of_ge hbj]
      exact Nat.mod_lt _ hm
    · rw [balancedChunkStart_of_ge hbj]
      change t = (b + u / m) * m + b + u % m
      have htu : t = b * (m + 1) + u := by
        dsimp only [u]
        omega
      have hmod : u = u % m + m * (u / m) := (Nat.mod_add_div u m).symm
      calc
        t = b * (m + 1) + u := htu
        _ = b * (m + 1) + (u % m + m * (u / m)) :=
          congrArg (fun v => b * (m + 1) + v) hmod
        _ = (b + u / m) * m + b + u % m := by ring

private lemma balancedChunk_index_unique {c m t : Nat}
    (j j' : Fin (c / m)) (i i' : Nat)
    (hi : i < balancedChunkLength m (c % m) j)
    (hi' : i' < balancedChunkLength m (c % m) j')
    (ht : t = balancedChunkStart m (c % m) j + i)
    (ht' : t = balancedChunkStart m (c % m) j' + i') : j = j' := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjj' | hj'j
  · have hlt : t < balancedChunkStart m (c % m) j' := by
      calc
        t = balancedChunkStart m (c % m) j + i := ht
        _ < balancedChunkStart m (c % m) j +
            balancedChunkLength m (c % m) j := Nat.add_lt_add_left hi _
        _ = balancedChunkStart m (c % m) ((j : Nat) + 1) :=
          balancedChunk_end _ _ _
        _ <= balancedChunkStart m (c % m) j' :=
          balancedChunkStart_mono (Nat.succ_le_iff.mpr hjj')
    have hge : balancedChunkStart m (c % m) j' <= t := by
      rw [ht']
      omega
    omega
  · have hlt : t < balancedChunkStart m (c % m) j := by
      calc
        t = balancedChunkStart m (c % m) j' + i' := ht'
        _ < balancedChunkStart m (c % m) j' +
            balancedChunkLength m (c % m) j' := Nat.add_lt_add_left hi' _
        _ = balancedChunkStart m (c % m) ((j' : Nat) + 1) :=
          balancedChunk_end _ _ _
        _ <= balancedChunkStart m (c % m) j :=
          balancedChunkStart_mono (Nat.succ_le_iff.mpr hj'j)
    have hge : balancedChunkStart m (c % m) j <= t := by
      rw [ht]
      omega
    omega

private abbrev BalancedResidueChunkIndex (r d m : Nat) :=
  Sigma fun a : Fin d => Fin (residueClassLength r d a / m)

private def balancedResidueChunkAP (R : IntAP) (d m : Nat)
    (z : BalancedResidueChunkIndex R.length d m) : IntAP where
  start := intAPPoint R
    (z.1 + balancedChunkStart m (residueClassLength R.length d z.1 % m) z.2 * d)
  step := d * R.step
  length := balancedChunkLength m (residueClassLength R.length d z.1 % m) z.2

private noncomputable def balancedResidueChunkFamily (R : IntAP) (d m : Nat) :
    Fin (Fintype.card (BalancedResidueChunkIndex R.length d m)) -> IntAP :=
  fun j => balancedResidueChunkAP R d m ((Fintype.equivFin _).symm j)

private lemma intAPPoint_injective (R : IntAP) (hstep : 0 < R.step) :
    Function.Injective (intAPPoint R) := by
  intro i j hij
  unfold intAPPoint at hij
  have hmulInt : (i * R.step : Int) = (j * R.step : Int) :=
    add_left_cancel hij
  have hmul : i * R.step = j * R.step := by exact_mod_cast hmulInt
  exact Nat.eq_of_mul_eq_mul_right hstep hmul

private lemma balancedResidueChunkAP_mem_iff (R : IntAP) (d m : Nat)
    (z : BalancedResidueChunkIndex R.length d m) (x : Int) :
    x ∈ (balancedResidueChunkAP R d m z).carrier ↔
      exists i : Nat,
        i < balancedChunkLength m (residueClassLength R.length d z.1 % m) z.2 /\
        x = intAPPoint R
          (z.1 + (balancedChunkStart m
            (residueClassLength R.length d z.1 % m) z.2 + i) * d) := by
  classical
  rw [IntAP.carrier]
  constructor
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨i, i.isLt, ?_⟩
    simp only [balancedResidueChunkAP, intAPPoint]
    push_cast
    ring
  · rintro ⟨i, hi, rfl⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only [balancedResidueChunkAP, intAPPoint]
    push_cast
    ring

private lemma balancedResidueChunkAP_isProper (R : IntAP) (d m : Nat)
    (hRstep : 0 < R.step) (hd : 0 < d)
    (z : BalancedResidueChunkIndex R.length d m) :
    (balancedResidueChunkAP R d m z).IsProper := by
  constructor
  · simp only [balancedResidueChunkAP]
    positivity
  · classical
    rw [IntAP.carrier]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i _ j _ hij
      apply Fin.ext
      simp only [balancedResidueChunkAP] at hij
      have hmulInt : ((i : Nat) * (d * R.step) : Int) =
          ((j : Nat) * (d * R.step) : Int) := add_left_cancel hij
      have hmul : (i : Nat) * (d * R.step) = (j : Nat) * (d * R.step) := by
        exact_mod_cast hmulInt
      exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hd hRstep) hmul

private lemma balancedResidueChunkFamily_partition (R : IntAP) (d m : Nat)
    (hRstep : 0 < R.step) (hd : 0 < d) (hdl : d <= R.length)
    (hm : 0 < m)
    (hclass : forall a : Fin d,
      m * m <= residueClassLength R.length d a) :
    IsIntAPPartition (balancedResidueChunkFamily R d m) R := by
  classical
  let E := Fintype.equivFin (BalancedResidueChunkIndex R.length d m)
  constructor
  · intro x
    constructor
    · intro hx
      rw [IntAP.carrier] at hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨t, rfl⟩ := hx
      let a : Fin d := ⟨(t : Nat) % d, Nat.mod_lt _ hd⟩
      let u := (t : Nat) / d
      have hu : u < residueClassLength R.length d a := by
        rw [quotient_lt_residueClassLength hd a.isLt hdl]
        dsimp only [a, u]
        have htEq : (t : Nat) % d + ((t : Nat) / d) * d = t := by
          simpa only [Nat.mul_comm] using Nat.mod_add_div (t : Nat) d
        rw [htEq]
        exact t.isLt
      obtain ⟨j, i, hi, huRep⟩ :=
        exists_balancedChunk_for_quotient hm (hclass a) hu
      let z : BalancedResidueChunkIndex R.length d m := ⟨a, j⟩
      refine ⟨E z, ?_⟩
      change intAPPoint R t ∈
        (balancedResidueChunkAP R d m ((Fintype.equivFin _).symm (E z))).carrier
      have hEz : (Fintype.equivFin _).symm (E z) = z := by
        simp only [E, Equiv.symm_apply_apply]
      rw [hEz, balancedResidueChunkAP_mem_iff]
      refine ⟨i, hi, ?_⟩
      apply congrArg (intAPPoint R)
      dsimp only [z]
      calc
        (t : Nat) = (t : Nat) % d + d * ((t : Nat) / d) :=
          (Nat.mod_add_div (t : Nat) d).symm
        _ = a + u * d := by simp only [a, u, Nat.mul_comm]
        _ = a + (balancedChunkStart m
            (residueClassLength R.length d a % m) j + i) * d := by
          rw [huRep]
    · rintro ⟨j, hj⟩
      let z := E.symm j
      change x ∈ (balancedResidueChunkAP R d m
        ((Fintype.equivFin _).symm j)).carrier at hj
      have hz : (Fintype.equivFin _).symm j = z := rfl
      rw [hz, balancedResidueChunkAP_mem_iff] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [IntAP.carrier]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      let t := z.1 + (balancedChunkStart m
        (residueClassLength R.length d z.1 % m) z.2 + i) * d
      have hq : balancedChunkStart m
          (residueClassLength R.length d z.1 % m) z.2 + i <
          residueClassLength R.length d z.1 :=
        balancedChunk_quotient_lt hm (hclass z.1) z.2 i hi
      have ht : t < R.length := by
        dsimp only [t]
        exact (quotient_lt_residueClassLength hd z.1.isLt hdl).1 hq
      exact ⟨⟨t, ht⟩, rfl⟩
  · intro j j' hjj'
    rw [Finset.disjoint_left]
    intro x hx hx'
    let z := E.symm j
    let z' := E.symm j'
    change x ∈ (balancedResidueChunkAP R d m
      ((Fintype.equivFin _).symm j)).carrier at hx
    change x ∈ (balancedResidueChunkAP R d m
      ((Fintype.equivFin _).symm j')).carrier at hx'
    have hz : (Fintype.equivFin _).symm j = z := rfl
    have hz' : (Fintype.equivFin _).symm j' = z' := rfl
    rw [hz, balancedResidueChunkAP_mem_iff] at hx
    rw [hz', balancedResidueChunkAP_mem_iff] at hx'
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨i', hi', hxi'⟩ := hx'
    have hcoord := intAPPoint_injective R hRstep (hxi.symm.trans hxi')
    have haVal : (z.1 : Nat) = (z'.1 : Nat) := by
      have hmod := congrArg (fun y : Nat => y % d) hcoord
      simpa only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt z.1.isLt,
        Nat.mod_eq_of_lt z'.1.isLt] using hmod
    have ha : z.1 = z'.1 := Fin.ext haVal
    rcases z with ⟨a, k⟩
    rcases z' with ⟨a', k'⟩
    dsimp only at ha
    subst a'
    have hquotMul :
        (balancedChunkStart m (residueClassLength R.length d a % m) k + i) * d =
        (balancedChunkStart m (residueClassLength R.length d a % m) k' + i') * d :=
      Nat.add_left_cancel hcoord
    have hquot :
        balancedChunkStart m (residueClassLength R.length d a % m) k + i =
        balancedChunkStart m (residueClassLength R.length d a % m) k' + i' :=
      Nat.eq_of_mul_eq_mul_right hd hquotMul
    have hk : k = k' := balancedChunk_index_unique k k' i i' hi hi' rfl hquot
    subst k'
    have hzEq : j = j' := by
      apply E.symm.injective
      exact hz.trans hz'.symm
    exact bne_iff_ne.mp hjj' hzEq

private lemma balancedResidueChunkFamily_properties (R : IntAP) (d m : Nat)
    (hRstep : 0 < R.step) (hd : 0 < d) :
    (forall j, (balancedResidueChunkFamily R d m j).IsProper /\
      ((balancedResidueChunkFamily R d m j).length = m \/
        (balancedResidueChunkFamily R d m j).length = m + 1)) /\
    (exists step : Nat, 0 < step /\
      forall j, (balancedResidueChunkFamily R d m j).step = step) := by
  constructor
  · intro j
    let z := (Fintype.equivFin (BalancedResidueChunkIndex R.length d m)).symm j
    constructor
    · change (balancedResidueChunkAP R d m z).IsProper
      exact balancedResidueChunkAP_isProper R d m hRstep hd z
    · change balancedChunkLength m
          (residueClassLength R.length d z.1 % m) z.2 = m \/
        balancedChunkLength m
          (residueClassLength R.length d z.1 % m) z.2 = m + 1
      unfold balancedChunkLength
      split_ifs <;> simp_all
  · refine ⟨d * R.step, Nat.mul_pos hd hRstep, ?_⟩
    intro j
    rfl

private lemma generic_freiman_map_nat_multiple {p : Nat} {G : Type*}
    [NeZero p] [AddCommGroup G]
    (B : Finset (ZMod p)) (psi : ZMod p -> G)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod p) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (n : Nat) (hn : n <= m) :
    psi ((n : ZMod p) * d) = n • psi d := by
  have hzero : (0 : ZMod p) ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hd : d ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨1, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hpsi' : IsAddFreimanHom 2 (B : Set (ZMod p)) Set.univ psi := hpsi
  induction n with
  | zero => simpa using hpsiZero
  | succ n ih =>
      have hn' : n <= m := Nat.le_trans (Nat.le_succ n) hn
      have hnm : ((n : ZMod p) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hsucc : (((n + 1 : Nat) : ZMod p) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n + 1 : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hadd : ((n + 1 : Nat) : ZMod p) * d + 0 =
          (n : ZMod p) * d + d := by push_cast; ring
      have hmap := hpsi'.add_eq_add (hmem hsucc) (hmem hzero)
        (hmem hnm) (hmem hd) hadd
      rw [hpsiZero, add_zero, ih hn'] at hmap
      simpa only [add_nsmul, one_nsmul] using hmap

private lemma generic_freiman_map_int_multiple {p : Nat} {G : Type*}
    [NeZero p] [AddCommGroup G]
    (B : Finset (ZMod p)) (psi : ZMod p -> G)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod p) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (j : Int)
    (hj : j ∈ Finset.Icc (-(m : Int)) (m : Int)) :
    psi ((j : ZMod p) * d) = j • psi d := by
  have hzero : (0 : ZMod p) ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hpsi' : IsAddFreimanHom 2 (B : Set (ZMod p)) Set.univ psi := hpsi
  cases j with
  | ofNat n =>
      have hn : n <= m := by
        have := (Finset.mem_Icc.mp hj).2
        apply Int.ofNat_le.mp
        simpa only [Int.ofNat_eq_natCast] using this
      have h := generic_freiman_map_nat_multiple B psi hpsi hpsiZero d m hm hmem n hn
      simpa using h
  | negSucc n =>
      have hn : n + 1 <= m := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      have hpos : (((n + 1 : Nat) : ZMod p) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n + 1 : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hneg : (-(((n + 1 : Nat) : ZMod p) * d)) ∈
          symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨Int.negSucc n, Finset.mem_Icc.mpr ?_, ?_⟩
        · constructor <;> omega
        · push_cast
          ring
      have hadd : -(((n + 1 : Nat) : ZMod p) * d) +
          ((n + 1 : Nat) : ZMod p) * d = 0 + 0 := by ring
      have hmap := hpsi'.add_eq_add (hmem hneg) (hmem hpos)
        (hmem hzero) (hmem hzero) hadd
      have hnat := generic_freiman_map_nat_multiple B psi hpsi hpsiZero
        d m hm hmem (n + 1) hn
      rw [hpsiZero, add_zero, hnat] at hmap
      have hnegValue : psi (-(((n + 1 : Nat) : ZMod p) * d)) =
          -((n + 1) • psi d) := eq_neg_of_add_eq_zero_left hmap
      convert hnegValue using 1
      · push_cast
        ring_nf
      · simp [add_nsmul]

private def intAPCoordinateSet (R : IntAP) (A : Finset Int) : Finset Nat :=
  (Finset.range R.length).filter fun j => intAPPoint R j ∈ A

private def modularCoordinateSet (p : Nat) (R : IntAP)
    (A : Finset Int) : Finset (ZMod p) :=
  (intAPCoordinateSet R A).image fun j : Nat => (j : ZMod p)

private lemma intAPCoordinateSet_image (R : IntAP) (A : Finset Int)
    (hA : A ⊆ R.carrier) :
    (intAPCoordinateSet R A).image (intAPPoint R) = A := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact (Finset.mem_filter.mp hj).2
  · intro hx
    have hxR := hA hx
    rw [IntAP.carrier] at hxR
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxR
    obtain ⟨j, rfl⟩ := hxR
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hx⟩, rfl⟩

private lemma intAPCoordinateSet_card (R : IntAP) (A : Finset Int)
    (hRstep : 0 < R.step) (hA : A ⊆ R.carrier) :
    (intAPCoordinateSet R A).card = A.card := by
  calc
    (intAPCoordinateSet R A).card =
        ((intAPCoordinateSet R A).image (intAPPoint R)).card :=
      (Finset.card_image_iff.mpr (intAPPoint_injective R hRstep).injOn).symm
    _ = A.card := congrArg Finset.card (intAPCoordinateSet_image R A hA)

private lemma modularCoordinateSet_card {p : Nat} (R : IntAP)
    (A : Finset Int) (hRstep : 0 < R.step) (hA : A ⊆ R.carrier)
    (hlp : R.length < p) :
    (modularCoordinateSet p R A).card = A.card := by
  calc
    (modularCoordinateSet p R A).card = (intAPCoordinateSet R A).card := by
      rw [modularCoordinateSet, Finset.card_image_iff.mpr]
      intro x hx y hy hxy
      have hxp : x < p :=
        (Finset.mem_range.mp (Finset.mem_filter.mp hx).1).trans hlp
      have hyp : y < p :=
        (Finset.mem_range.mp (Finset.mem_filter.mp hy).1).trans hlp
      have hval := congrArg ZMod.val hxy
      simpa only [ZMod.val_natCast_of_lt hxp,
        ZMod.val_natCast_of_lt hyp] using hval
    _ = A.card := intAPCoordinateSet_card R A hRstep hA

private lemma mem_modularCoordinateSet_iff {p : Nat} [NeZero p]
    (R : IntAP) (A : Finset Int) (hlp : R.length < p) (x : ZMod p) :
    x ∈ modularCoordinateSet p R A ↔
      x.val < R.length /\ intAPPoint R x.val ∈ A := by
  classical
  rw [modularCoordinateSet]
  constructor
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    unfold intAPCoordinateSet at hj
    rw [Finset.mem_filter] at hj
    have hjp : j < p := (Finset.mem_range.mp hj.1).trans hlp
    rw [ZMod.val_natCast_of_lt hjp]
    exact ⟨Finset.mem_range.mp hj.1, hj.2⟩
  · rintro ⟨hxlt, hxA⟩
    rw [Finset.mem_image]
    refine ⟨x.val, ?_, ?_⟩
    · unfold intAPCoordinateSet
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxlt, hxA⟩
    exact ZMod.natCast_zmod_val x

private def modularCoordinateMap (p : Nat) (R : IntAP)
    {G : Type*} (phi : Int -> G) : ZMod p -> G :=
  fun x => phi (intAPPoint R x.val)

private lemma multiset_val_sum_lt {p l : Nat} [NeZero p]
    (s : Multiset (ZMod p)) (hl : 0 < l)
    (hs : forall x, x ∈ s -> x.val < l) (hcard : s.card = 8)
    (hlp : 8 * l < p) : (s.map fun x => x.val).sum < p := by
  have hle : (s.map fun x => x.val).sum <= s.card * (l - 1) := by
    have hbound := Multiset.sum_le_card_nsmul
      (s.map fun x => x.val) (l - 1) (by
      intro y hy
      rw [Multiset.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have := hs x hx
      omega)
    rw [Multiset.card_map] at hbound
    exact hbound
  have hlt : s.card * (l - 1) < 8 * l := by
    rw [hcard]
    exact (Nat.mul_lt_mul_left (by omega : 0 < 8)).2
      (Nat.sub_lt hl (by omega))
  exact hle.trans_lt (hlt.trans hlp)

private lemma multiset_val_sum_eq_of_sum_eq {p l : Nat} [NeZero p]
    (s t : Multiset (ZMod p)) (hl : 0 < l)
    (hs : forall x, x ∈ s -> x.val < l)
    (ht : forall x, x ∈ t -> x.val < l)
    (hscard : s.card = 8) (htcard : t.card = 8)
    (hlp : 8 * l < p) (hsum : s.sum = t.sum) :
    (s.map fun x => x.val).sum = (t.map fun x => x.val).sum := by
  have hslt := multiset_val_sum_lt s hl hs hscard hlp
  have htlt := multiset_val_sum_lt t hl ht htcard hlp
  have hcast :
      (((s.map fun x => x.val).sum : Nat) : ZMod p) =
        (((t.map fun x => x.val).sum : Nat) : ZMod p) := by
    simpa using hsum
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast_of_lt hslt,
    ZMod.val_natCast_of_lt htlt] using hval

private lemma multiset_intAPPoint_sum {p : Nat} (R : IntAP)
    (s : Multiset (ZMod p)) :
    (s.map fun x => intAPPoint R x.val).sum =
      s.card • R.start +
        (s.map fun x => (x.val : Int)).sum * (R.step : Int) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      rw [ih]
      simp [intAPPoint]
      ring_nf

private lemma modularCoordinateMap_freiman {p : Nat} {G : Type*}
    [NeZero p] [AddCommMonoid G]
    (R : IntAP) (A : Finset Int) (phi : Int -> G)
    (hl : 0 < R.length) (hlp : 8 * R.length < p)
    (hphi : FreimanHom 8 A phi) :
    FreimanHom 8 (modularCoordinateSet p R A)
      (modularCoordinateMap p R phi) := by
  rw [FreimanHom]
  constructor
  · intro x _
    exact Set.mem_univ _
  · intro s t hsA htA hscard htcard hsum
    have hsMem : forall x, x ∈ s -> x.val < R.length := by
      intro x hx
      exact (mem_modularCoordinateSet_iff R A (by omega) x).1 (hsA hx) |>.1
    have htMem : forall x, x ∈ t -> x.val < R.length := by
      intro x hx
      exact (mem_modularCoordinateSet_iff R A (by omega) x).1 (htA hx) |>.1
    have hvalSum := multiset_val_sum_eq_of_sum_eq s t hl hsMem htMem
      hscard htcard hlp hsum
    let sInt := s.map fun x => intAPPoint R x.val
    let tInt := t.map fun x => intAPPoint R x.val
    have hsIntA : forall x, x ∈ sInt -> x ∈ (A : Set Int) := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact (mem_modularCoordinateSet_iff R A (by omega) z).1 (hsA hz) |>.2
    have htIntA : forall x, x ∈ tInt -> x ∈ (A : Set Int) := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact (mem_modularCoordinateSet_iff R A (by omega) z).1 (htA hz) |>.2
    have hsIntCard : sInt.card = 8 := by simpa [sInt] using hscard
    have htIntCard : tInt.card = 8 := by simpa [tInt] using htcard
    have hvalSumInt :
        (s.map fun x => (x.val : Int)).sum =
          (t.map fun x => (x.val : Int)).sum := by
      simpa using congrArg (fun n : Nat => (n : Int)) hvalSum
    have hsIntSum : sInt.sum = tInt.sum := by
      dsimp only [sInt, tInt]
      rw [multiset_intAPPoint_sum, multiset_intAPPoint_sum, hscard, htcard,
        hvalSumInt]
    have himage := hphi.map_sum_eq_map_sum hsIntA htIntA hsIntCard htIntCard hsIntSum
    simpa only [sInt, tInt, modularCoordinateMap, Multiset.map_map,
      Function.comp_apply] using himage

private lemma zero_mem_symmetricMultiples {p m : Nat} (d : ZMod p) :
    (0 : ZMod p) ∈ symmetricMultiples d m := by
  rw [symmetricMultiples, Finset.mem_image]
  refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
  constructor <;> omega

private lemma balancedResidueChunkAP_linear {p N : Nat}
    [NeZero p] [NeZero N] (R : IntAP) (A : Finset Int)
    (phi : Int -> ZMod N) (d m : Nat)
    (z : BalancedResidueChunkIndex R.length d m)
    (hd : 0 < d) (hdl : d <= R.length)
    (hm : 0 < m) (hlp : R.length < p)
    (hclass : m * m <= residueClassLength R.length d z.1)
    (B : Finset (ZMod p)) (psi : ZMod p -> ZMod N)
    (hpsi : FreimanHom 2 B psi)
    (hagree : forall x, x ∈ modularCoordinateSet p R A ->
      forall y, y ∈ modularCoordinateSet p R A -> x - y ∈ B ->
        modularCoordinateMap p R phi x - modularCoordinateMap p R phi y =
          psi (x - y))
    (hshort : symmetricMultiples (d : ZMod p) m ⊆ B)
    (hAne : (modularCoordinateSet p R A).Nonempty) :
    IntAPLinearOn (balancedResidueChunkAP R d m z) A phi := by
  classical
  let P := balancedResidueChunkAP R d m z
  let base := z.1 + balancedChunkStart m
    (residueClassLength R.length d z.1 % m) z.2 * d
  let coord : Nat -> Nat := fun i => base + i * d
  have hcoord_eq (i : Nat) :
      P.start + (i * P.step : Nat) = intAPPoint R (coord i) := by
    simp only [P, balancedResidueChunkAP, coord, base, intAPPoint]
    push_cast
    ring
  have hcoord_lt (i : Fin P.length) : coord i < R.length := by
    have hi : (i : Nat) < balancedChunkLength m
        (residueClassLength R.length d z.1 % m) z.2 := i.isLt
    have hq : balancedChunkStart m
          (residueClassLength R.length d z.1 % m) z.2 + i <
        residueClassLength R.length d z.1 :=
      balancedChunk_quotient_lt hm hclass z.2 i hi
    dsimp only [coord, base]
    simpa only [Nat.add_mul, Nat.add_assoc] using
      (quotient_lt_residueClassLength hd z.1.isLt hdl).1 hq
  have hcoord_cast (i : Fin P.length) :
      (((coord i : Nat) : ZMod p).val) = coord i :=
    ZMod.val_natCast_of_lt ((hcoord_lt i).trans hlp)
  have hcoord_mem (i : Fin P.length)
      (hiA : P.start + ((i : Nat) * P.step : Nat) ∈ A) :
      (coord i : ZMod p) ∈ modularCoordinateSet p R A := by
    rw [mem_modularCoordinateSet_iff R A hlp]
    rw [hcoord_cast]
    exact ⟨hcoord_lt i, by simpa only [← hcoord_eq i] using hiA⟩
  have hlength : P.length = m ∨ P.length = m + 1 := by
    change balancedChunkLength m
      (residueClassLength R.length d z.1 % m) z.2 = m ∨
      balancedChunkLength m
      (residueClassLength R.length d z.1 % m) z.2 = m + 1
    unfold balancedChunkLength
    split_ifs <;> simp_all
  have hindex_le (i : Fin P.length) : (i : Nat) <= m := by
    rcases hlength with hlen | hlen <;> omega
  obtain ⟨a0, ha0⟩ := hAne
  have hpsiZero : psi 0 = 0 := by
    have hzeroB : a0 - a0 ∈ B := by
      apply hshort
      simpa using zero_mem_symmetricMultiples (p := p) (m := m) (d : ZMod p)
    have hag := hagree a0 ha0 a0 ha0 hzeroB
    simpa using hag.symm
  by_cases hnonempty : exists r : Fin P.length,
      P.start + ((r : Nat) * P.step : Nat) ∈ A
  · obtain ⟨r, hrA⟩ := hnonempty
    refine ⟨psi (d : ZMod p),
      phi (P.start + ((r : Nat) * P.step : Nat)) -
        (r : Nat) • psi (d : ZMod p), ?_⟩
    intro i
    dsimp only
    intro hiA
    have hiMem := hcoord_mem i hiA
    have hrMem := hcoord_mem r hrA
    let j : Int := (i : Int) - (r : Int)
    have hjBounds : j ∈ Finset.Icc (-(m : Int)) (m : Int) := by
      rw [Finset.mem_Icc]
      dsimp only [j]
      have hiLe : (i : Int) <= (m : Int) := by exact_mod_cast hindex_le i
      have hrLe : (r : Int) <= (m : Int) := by exact_mod_cast hindex_le r
      constructor <;> omega
    have hdiff :
        (coord i : ZMod p) - (coord r : ZMod p) =
          (j : ZMod p) * (d : ZMod p) := by
      dsimp only [coord, base, j]
      push_cast
      ring
    have hdiffMem : (coord i : ZMod p) - (coord r : ZMod p) ∈ B := by
      apply hshort
      rw [symmetricMultiples, Finset.mem_image]
      exact ⟨j, hjBounds, hdiff.symm⟩
    have hag := hagree (coord i : ZMod p) hiMem
      (coord r : ZMod p) hrMem hdiffMem
    have hlin := generic_freiman_map_int_multiple B psi hpsi hpsiZero
      (d : ZMod p) m hm hshort j hjBounds
    dsimp only [modularCoordinateMap] at hag
    rw [hcoord_cast i, hcoord_cast r, ← hcoord_eq i, ← hcoord_eq r,
      hdiff, hlin] at hag
    change phi (P.start + ↑i * P.step) =
      psi (d : ZMod p) * (i : Nat) +
        (phi (P.start + ↑r * P.step) - (r : Nat) • psi (d : ZMod p))
    have hjSmul : j • psi (d : ZMod p) =
        (i : Nat) • psi (d : ZMod p) - (r : Nat) • psi (d : ZMod p) := by
      dsimp only [j]
      rw [sub_zsmul]
      simp [sub_eq_add_neg]
    rw [hjSmul] at hag
    simp only [nsmul_eq_mul] at hag ⊢
    push_cast at hag ⊢
    linear_combination hag
  · refine ⟨0, 0, ?_⟩
    intro i
    dsimp only
    intro hiA
    exact (hnonempty ⟨i, hiA⟩).elim

private lemma centeredAbs_add_le {p : Nat} [NeZero p] (x y : ZMod p) :
    centeredAbs (x + y) <= centeredAbs x + centeredAbs y := by
  unfold centeredAbs
  calc
    (x + y).valMinAbs.natAbs <=
        (x.valMinAbs + y.valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le x y
    _ <= x.valMinAbs.natAbs + y.valMinAbs.natAbs := Int.natAbs_add_le _ _

@[simp] private lemma centeredAbs_neg {p : Nat} [NeZero p] (x : ZMod p) :
    centeredAbs (-x) = centeredAbs x := by
  unfold centeredAbs
  exact ZMod.natAbs_valMinAbs_neg x

private lemma centeredAbs_nsmul_le {p : Nat} [NeZero p]
    (n : Nat) (x : ZMod p) : centeredAbs (n • x) <= n * centeredAbs x := by
  induction n with
  | zero => simp [centeredAbs]
  | succ n ih =>
      rw [succ_nsmul, Nat.succ_mul]
      exact le_trans (centeredAbs_add_le (n • x) x) (Nat.add_le_add_right ih _)

private lemma bohr_neg_mem {p : Nat} [NeZero p] {K : Finset (ZMod p)}
    {rho : Real} {d : ZMod p} (hd : d ∈ bohr K rho) : -d ∈ bohr K rho := by
  rw [bohr, Finset.mem_filter] at hd ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  simpa only [mul_neg, centeredAbs_neg] using hd.2 r hr

private lemma bohr_mono {p : Nat} [NeZero p]
    {K L : Finset (ZMod p)} {rho sigma : Real}
    (hKL : K ⊆ L) (hrs : rho <= sigma) : bohr L rho ⊆ bohr K sigma := by
  intro d hd
  rw [bohr, Finset.mem_filter] at hd ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  exact (hd.2 r (hKL hr)).trans (mul_le_mul_of_nonneg_right hrs (by positivity))

private lemma bohr_symmetric_multiples_subset {p : Nat} [NeZero p]
    (K : Finset (ZMod p)) (rho : Real) (hrho : 0 < rho)
    (m : Nat) (hm : 0 < m) (d : ZMod p)
    (hd : d ∈ bohr K (rho / m)) :
    symmetricMultiples d m ⊆ bohr K rho := by
  classical
  intro z hz
  rw [symmetricMultiples, Finset.mem_image] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  rw [bohr, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  rw [bohr, Finset.mem_filter] at hd
  have hdr := hd.2 r hr
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hbase : 0 <= rho / (m : Real) * p := by positivity
  have hcollapse : (m : Real) * (rho / (m : Real) * p) = rho * p := by
    field_simp
  have hjBounds : -(m : Int) <= j ∧ j <= (m : Int) := Finset.mem_Icc.mp hj
  cases j with
  | ofNat n =>
      have hcastNat : ((Int.ofNat n : Int) : ZMod p) = (n : ZMod p) := by norm_num
      rw [hcastNat]
      have hn : n <= m := by
        apply Int.ofNat_le.mp
        simpa only [Int.ofNat_eq_natCast] using hjBounds.2
      have hcenter : centeredAbs (r * ((n : ZMod p) * d)) <=
          n * centeredAbs (r * d) := by
        have hmul : r * ((n : ZMod p) * d) = n • (r * d) := by
          simp [nsmul_eq_mul]
          ring
        rw [hmul]
        exact centeredAbs_nsmul_le n (r * d)
      calc
        (centeredAbs (r * ((n : ZMod p) * d)) : Real) <=
            n * centeredAbs (r * d) := by exact_mod_cast hcenter
        _ <= n * (rho / (m : Real) * p) := by gcongr
        _ <= m * (rho / (m : Real) * p) := by gcongr
        _ = rho * p := hcollapse
  | negSucc n =>
      have hn : n + 1 <= m := by
        have := hjBounds.1
        omega
      have hcast : ((Int.negSucc n : Int) : ZMod p) * d =
          -(((n + 1 : Nat) : ZMod p) * d) := by
        push_cast
        ring_nf
      rw [hcast, mul_neg, centeredAbs_neg]
      have hcenter : centeredAbs (r * (((n + 1 : Nat) : ZMod p) * d)) <=
          (n + 1) * centeredAbs (r * d) := by
        have hmul : r * (((n + 1 : Nat) : ZMod p) * d) =
            (n + 1) • (r * d) := by
          simp [nsmul_eq_mul]
          ring
        rw [hmul]
        exact centeredAbs_nsmul_le (n + 1) (r * d)
      calc
        (centeredAbs (r * (((n + 1 : Nat) : ZMod p) * d)) : Real) <=
            (n + 1) * centeredAbs (r * d) := by exact_mod_cast hcenter
        _ <= (n + 1) * (rho / (m : Real) * p) := by gcongr
        _ <= m * (rho / (m : Real) * p) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hbase
        _ = rho * p := hcollapse

private lemma centeredAbs_pos_of_ne_zero {p : Nat} [NeZero p]
    {d : ZMod p} (hd : d != 0) : 0 < centeredAbs d := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hvalMin : d.valMinAbs = 0 := Int.natAbs_eq_zero.mp hzero
  have hd0 : d = 0 := by simpa using (ZMod.valMinAbs_spec d 0).1 hvalMin |>.1
  exact (bne_iff_ne.mp hd) hd0

private lemma natCast_centeredAbs_eq_or_neg {p : Nat} [NeZero p]
    (d : ZMod p) : (centeredAbs d : ZMod p) = d ∨
      (centeredAbs d : ZMod p) = -d := by
  have hcast := ZMod.natCast_natAbs_valMinAbs d
  unfold centeredAbs
  split at hcast
  · exact Or.inl hcast
  · exact Or.inr hcast

private def cor711Density (p : Nat) (R : IntAP) (A : Finset Int) : Real :=
  (modularCoordinateSet p R A).card / (p : Real)

private def cor711Spectrum (p : Nat) [NeZero p] (R : IntAP)
    {q : Nat} (A : Fin q -> Finset Int) (i : Fin q) : Finset (ZMod p) :=
  section7Spectrum (modularCoordinateSet p R (A i))
    (cor711Density p R (A i))

private def cor711SpectrumUnion (p : Nat) [NeZero p] (R : IntAP)
    {q : Nat} (A : Fin q -> Finset Int) : Finset (ZMod p) :=
  {1} ∪ Finset.univ.biUnion (cor711Spectrum p R A)

private lemma cor711_alpha_le_one {q : Nat} (R : IntAP)
    (A : Fin q -> Finset Int) (alpha : Real)
    (hq : 0 < q) (hl : 0 < R.length) (hproper : R.IsProper)
    (hA : forall i, A i ⊆ R.carrier /\
      alpha * R.length <= (A i).card) : alpha <= 1 := by
  let i : Fin q := ⟨0, hq⟩
  have hcardA : (A i).card <= R.length := by
    calc
      (A i).card <= R.carrier.card := Finset.card_le_card (hA i).1
      _ = R.length := hproper.2
  have hlow := (hA i).2
  have hlReal : (0 : Real) < R.length := by exact_mod_cast hl
  have hcardAReal : ((A i).card : Real) <= R.length := by exact_mod_cast hcardA
  nlinarith

private lemma cor711_density_card {p : Nat} [NeZero p]
    (R : IntAP) (A : Finset Int) :
    ((modularCoordinateSet p R A).card : Real) =
      cor711Density p R A * p := by
  unfold cor711Density
  have hp : (0 : Real) < p := by exact_mod_cast NeZero.pos p
  exact (div_mul_cancel₀ _ hp.ne').symm

private lemma cor711_density_lower {p q : Nat} [NeZero p]
    (R : IntAP) (A : Fin q -> Finset Int) (alpha : Real)
    (halpha : 0 < alpha) (hRstep : 0 < R.step) (hlp : R.length < p)
    (hpUpper : p <= 16 * R.length)
    (hA : forall i, A i ⊆ R.carrier /\
      alpha * R.length <= (A i).card)
    (i : Fin q) : alpha <= 16 * cor711Density p R (A i) := by
  have hpReal : (0 : Real) < p := by exact_mod_cast NeZero.pos p
  have hpUpperReal : (p : Real) <= 16 * R.length := by exact_mod_cast hpUpper
  have hcardEq := modularCoordinateSet_card R (A i) hRstep (hA i).1 hlp
  have hcardLower : alpha * R.length <=
      (modularCoordinateSet p R (A i)).card := by
    simpa only [hcardEq] using (hA i).2
  unfold cor711Density
  rw [← show 16 * ((modularCoordinateSet p R (A i)).card : Real) / p =
      16 * (((modularCoordinateSet p R (A i)).card : Real) / p) by ring]
  rw [le_div_iff₀ hpReal]
  have hmulP := mul_le_mul_of_nonneg_left hpUpperReal halpha.le
  have hmulCard := mul_le_mul_of_nonneg_left hcardLower (by norm_num : (0 : Real) <= 16)
  nlinarith

private lemma rpow_neg_two_le_scaled {a b : Real}
    (ha : 0 < a) (hb : 0 < b) (h : a <= 16 * b) :
    b ^ (-(2 : Real)) <= 256 * a ^ (-(2 : Real)) := by
  rw [Real.rpow_neg hb.le, Real.rpow_neg ha.le,
    Real.rpow_two, Real.rpow_two]
  rw [inv_le_iff_one_le_mul₀' (sq_pos_of_pos hb)]
  rw [show b ^ 2 * (256 * (a ^ 2)⁻¹) = 256 * b ^ 2 / a ^ 2 by ring]
  rw [le_div_iff₀ (sq_pos_of_pos ha)]
  nlinarith [sq_nonneg (16 * b - a)]

private lemma cor711_one_partition {N q : Nat} [NeZero N]
    (R : IntAP) (A : Fin q -> Finset Int) (phi : Fin q -> Int -> ZMod N)
    (hl : 0 < R.length) (hproper : R.IsProper) :
    exists M : Nat, exists S : Fin M -> IntAP,
      IsIntAPPartition S R /\
      (forall j, (S j).IsProper /\
        ((S j).length = 1 \/ (S j).length = 1 + 1)) /\
      (exists d : Nat, 0 < d /\ forall j, (S j).step = d) /\
      (forall i j, IntAPLinearOn (S j) (A i) (phi i)) := by
  let d := R.length
  have hd : 0 < d := hl
  have hclass : forall a : Fin d,
      1 * 1 <= residueClassLength R.length d a := by
    intro a
    have : 0 < residueClassLength R.length d a :=
      (quotient_lt_residueClassLength hd a.isLt le_rfl).2 (by
        simpa only [zero_mul, add_zero] using a.isLt)
    omega
  let M := Fintype.card (BalancedResidueChunkIndex R.length d 1)
  let S := balancedResidueChunkFamily R d 1
  refine ⟨M, S, balancedResidueChunkFamily_partition R d 1
    hproper.1 hd le_rfl (by omega) hclass, ?_, ?_, ?_⟩
  · exact (balancedResidueChunkFamily_properties R d 1 hproper.1 hd).1
  · exact (balancedResidueChunkFamily_properties R d 1 hproper.1 hd).2
  · intro i j
    let z := (Fintype.equivFin (BalancedResidueChunkIndex R.length d 1)).symm j
    have hlen : (S j).length = 1 := by
      change balancedChunkLength 1
        (residueClassLength R.length d z.1 % 1) z.2 = 1
      rw [Nat.mod_one, balancedChunkLength_of_ge (Nat.zero_le _)]
    refine ⟨0, phi i (S j).start, ?_⟩
    intro k
    dsimp only
    intro _
    have hk : (k : Nat) = 0 := by omega
    simp [hk]

private lemma cor711_spectrum_bound {p N q : Nat} [NeZero p] [NeZero N]
    (R : IntAP) (A : Fin q -> Finset Int) (phi : Fin q -> Int -> ZMod N)
    (alpha : Real) (hl : 0 < R.length) (halpha : 0 < alpha)
    (hRstep : 0 < R.step) (h8lp : 8 * R.length < p)
    (hpUpper : p <= 16 * R.length)
    (hA : forall i, A i ⊆ R.carrier /\
      alpha * R.length <= (A i).card /\ FreimanHom 8 (A i) (phi i))
    (i : Fin q) :
    ((cor711Spectrum p R A i).card : Real) <=
        4096 * alpha ^ (-(2 : Real)) /\
      (modularCoordinateSet p R (A i)).Nonempty /\
      exists psi : ZMod p -> ZMod N,
        FreimanHom 2
          (bohr (cor711Spectrum p R A i)
            (cor711Density p R (A i) / (32 * Real.pi))) psi /\
        forall x, x ∈ modularCoordinateSet p R (A i) ->
          forall y, y ∈ modularCoordinateSet p R (A i) ->
            x - y ∈ bohr (cor711Spectrum p R A i)
              (cor711Density p R (A i) / (32 * Real.pi)) ->
            modularCoordinateMap p R (phi i) x -
                modularCoordinateMap p R (phi i) y = psi (x - y) := by
  have hlp : R.length < p := by omega
  have hbetaLower := cor711_density_lower R A alpha halpha hRstep hlp
    hpUpper (fun i => ⟨(hA i).1, (hA i).2.1⟩) i
  have hbeta : 0 < cor711Density p R (A i) := by nlinarith
  have hfreiman : FreimanHom 8 (modularCoordinateSet p R (A i))
      (modularCoordinateMap p R (phi i)) :=
    modularCoordinateMap_freiman R (A i) (phi i) hl h8lp (hA i).2.2
  have hmain := lemma_7_8_group_holds (G := ZMod N) p
    (modularCoordinateSet p R (A i)) (modularCoordinateMap p R (phi i))
    (cor711Density p R (A i)) hbeta (cor711_density_card R (A i)) hfreiman
  dsimp only [cor711Spectrum] at hmain ⊢
  refine ⟨hmain.1.trans ?_, ?_, hmain.2⟩
  · have hinv := rpow_neg_two_le_scaled halpha hbeta hbetaLower
    nlinarith
  · have hcardPosReal : (0 : Real) <
        (modularCoordinateSet p R (A i)).card := by
      rw [cor711_density_card R (A i)]
      exact mul_pos hbeta (by exact_mod_cast NeZero.pos p)
    have hcardPos : 0 < (modularCoordinateSet p R (A i)).card := by
      exact_mod_cast hcardPosReal
    exact Finset.card_pos.mp hcardPos

private lemma cor711_spectrumUnion_card {p q : Nat} [NeZero p]
    (R : IntAP) (A : Fin q -> Finset Int) (alpha : Real)
    (hq : 0 < q) (halpha : 0 < alpha) (halphaOne : alpha <= 1)
    (hK : forall i, ((cor711Spectrum p R A i).card : Real) <=
      4096 * alpha ^ (-(2 : Real))) :
    ((cor711SpectrumUnion p R A).card : Real) <=
      4097 * q * alpha ^ (-(2 : Real)) := by
  let U := Finset.univ.biUnion (cor711Spectrum p R A)
  have hunionNat : (cor711SpectrumUnion p R A).card <= 1 + U.card := by
    calc
      (cor711SpectrumUnion p R A).card <= ({1} : Finset (ZMod p)).card + U.card := by
        exact Finset.card_union_le _ _
      _ = 1 + U.card := by simp
  have hbiNat : U.card <= ∑ i : Fin q, (cor711Spectrum p R A i).card := by
    dsimp only [U]
    simpa only [Finset.sum_const_zero, Finset.sum_attach] using
      (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin q)))
        (t := cor711Spectrum p R A))
  have hunionReal : ((cor711SpectrumUnion p R A).card : Real) <=
      1 + (U.card : Real) := by exact_mod_cast hunionNat
  have hbiReal : (U.card : Real) <=
      ∑ i : Fin q, ((cor711Spectrum p R A i).card : Real) := by
    exact_mod_cast hbiNat
  have hsum : (∑ i : Fin q, ((cor711Spectrum p R A i).card : Real)) <=
      ∑ _i : Fin q, 4096 * alpha ^ (-(2 : Real)) := by
    exact Finset.sum_le_sum fun i _ => hK i
  have halphaPow : 1 <= alpha ^ (-(2 : Real)) := by
    rw [Real.rpow_neg halpha.le, Real.rpow_two]
    apply (one_le_inv₀ (sq_pos_of_pos halpha)).2
    nlinarith [sq_nonneg (1 - alpha)]
  calc
    ((cor711SpectrumUnion p R A).card : Real) <= 1 + (U.card : Real) :=
      hunionReal
    _ <= 1 + ∑ i : Fin q, ((cor711Spectrum p R A i).card : Real) := by
      gcongr
    _ <= 1 + ∑ _i : Fin q, 4096 * alpha ^ (-(2 : Real)) := by
      gcongr
    _ = 1 + (q : Real) * (4096 * alpha ^ (-(2 : Real))) := by simp
    _ <= 4097 * q * alpha ^ (-(2 : Real)) := by
      have hqReal : (1 : Real) <= q := by exact_mod_cast hq
      nlinarith [mul_le_mul hqReal halphaPow (by norm_num : (0 : Real) <= 1)
        (by positivity : (0 : Real) <= q)]

private def cor711Exponent (alpha : Real) (q : Nat) : Real :=
  (2 : Real) ^ (-(14 : Real)) * alpha ^ 2 * (q : Real)⁻¹

private lemma two_rpow_neg_fourteen :
    (2 : Real) ^ (-(14 : Real)) = 1 / 16384 := by
  rw [Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
  norm_num

private lemma cor711Exponent_pos {q : Nat} {alpha : Real}
    (hq : 0 < q) (halpha : 0 < alpha) : 0 < cor711Exponent alpha q := by
  unfold cor711Exponent
  positivity

private lemma cor711_three_exponent_lt_inv_card {q : Nat}
    {alpha Kcard : Real} (hq : 0 < q) (halpha : 0 < alpha)
    (hKpos : 0 < Kcard)
    (hKcard : Kcard <= 4097 * q * alpha ^ (-(2 : Real))) :
    3 * cor711Exponent alpha q < 1 / Kcard := by
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  apply (lt_div_iff₀ hKpos).2
  have hepos : 0 < 3 * cor711Exponent alpha q := by
    exact mul_pos (by norm_num) (cor711Exponent_pos hq halpha)
  calc
    3 * cor711Exponent alpha q * Kcard <=
        3 * cor711Exponent alpha q *
          (4097 * q * alpha ^ (-(2 : Real))) :=
      mul_le_mul_of_nonneg_left hKcard hepos.le
    _ = (12291 : Real) / 16384 := by
      rw [cor711Exponent, two_rpow_neg_fourteen,
        Real.rpow_neg halpha.le, Real.rpow_two]
      field_simp
      ring
    _ < 1 := by norm_num

private lemma cor711_bohr_nonzero_threshold {p q m l : Nat}
    {alpha Kcard : Real} (hq : 0 < q) (hmTwo : 2 <= m)
    (hl : 0 < l) (halpha : 0 < alpha) (hlp : l < p)
    (hKpos : 0 < Kcard)
    (hKcard : Kcard <= 4097 * q * alpha ^ (-(2 : Real)))
    (hmBound : (m : Real) <= (l : Real) ^ cor711Exponent alpha q)
    (hlarge : 1024 * Real.pi / alpha <
      (l : Real) ^ cor711Exponent alpha q) :
    2 * (p : Real) ^ (-(1 / Kcard)) <
      alpha / (512 * Real.pi * (m : Real) ^ 2) := by
  let e := cor711Exponent alpha q
  have he : 0 < e := cor711Exponent_pos hq halpha
  have hlReal : (0 : Real) < l := by exact_mod_cast hl
  have hpReal : (1 : Real) < p := by exact_mod_cast (show 1 < p by omega)
  have hlpReal : (l : Real) <= p := by exact_mod_cast hlp.le
  have hrecip : 3 * e < 1 / Kcard :=
    cor711_three_exponent_lt_inv_card hq halpha hKpos hKcard
  have hpExponent : (p : Real) ^ (-(1 / Kcard)) <
      (p : Real) ^ (-(3 * e)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hpReal
    linarith
  have hpToL : (p : Real) ^ (-(3 * e)) <=
      (l : Real) ^ (-(3 * e)) := by
    rw [Real.rpow_neg (by positivity : (0 : Real) <= p),
      Real.rpow_neg hlReal.le]
    apply (inv_le_inv₀
      (Real.rpow_pos_of_pos (zero_lt_one.trans hpReal) (3 * e))
      (Real.rpow_pos_of_pos hlReal (3 * e))).2
    exact Real.rpow_le_rpow hlReal.le hlpReal (by positivity)
  have hmNonneg : (0 : Real) <= m := by positivity
  have hmSq : (m : Real) ^ 2 <=
      ((l : Real) ^ e) ^ 2 := by
    nlinarith [sq_nonneg ((l : Real) ^ e - m)]
  have hlPower : (l : Real) ^ (-(3 * e)) * (m : Real) ^ 2 <=
      ((l : Real) ^ e)⁻¹ := by
    have hLe : 0 < (l : Real) ^ e := Real.rpow_pos_of_pos hlReal e
    calc
      (l : Real) ^ (-(3 * e)) * (m : Real) ^ 2 =
          ((l : Real) ^ e) ^ (-(3 : Real)) * (m : Real) ^ 2 := by
        rw [show -(3 * e) = e * (-3) by ring, Real.rpow_mul hlReal.le]
      _ <= ((l : Real) ^ e) ^ (-(3 : Real)) *
          ((l : Real) ^ e) ^ 2 := by gcongr
      _ = ((l : Real) ^ e)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hLe]
        norm_num [Real.rpow_neg_one]
  have hlargeInv : ((l : Real) ^ e)⁻¹ < alpha / (1024 * Real.pi) := by
    have hconstant : 0 < 1024 * Real.pi / alpha := by positivity
    have hinv := (inv_lt_inv₀ (Real.rpow_pos_of_pos hlReal e) hconstant).2 hlarge
    calc
      ((l : Real) ^ e)⁻¹ < (1024 * Real.pi / alpha)⁻¹ := hinv
      _ = alpha / (1024 * Real.pi) := by field_simp
  have hcore : (p : Real) ^ (-(1 / Kcard)) * (m : Real) ^ 2 <
      alpha / (1024 * Real.pi) := by
    calc
      (p : Real) ^ (-(1 / Kcard)) * (m : Real) ^ 2 <
          (p : Real) ^ (-(3 * e)) * (m : Real) ^ 2 := by
        exact mul_lt_mul_of_pos_right hpExponent (by positivity)
      _ <= (l : Real) ^ (-(3 * e)) * (m : Real) ^ 2 := by gcongr
      _ <= ((l : Real) ^ e)⁻¹ := hlPower
      _ < alpha / (1024 * Real.pi) := hlargeInv
  apply (lt_div_iff₀ (by positivity : 0 < 512 * Real.pi * (m : Real) ^ 2)).2
  have hcore' := (lt_div_iff₀ (by positivity : (0 : Real) < 1024 * Real.pi)).1 hcore
  nlinarith

private lemma cor711_centered_step_small {p m l : Nat} [NeZero p]
    {alpha : Real} (hm : 0 < m) (halpha : 0 < alpha)
    (halphaOne : alpha <= 1) (hpUpper : p <= 16 * l)
    (L : Finset (ZMod p)) (hone : (1 : ZMod p) ∈ L) (d : ZMod p)
    (hd : d ∈ bohr L (alpha / (512 * Real.pi * (m : Real) ^ 2))) :
    centeredAbs d * (m * m) < l := by
  rw [bohr, Finset.mem_filter] at hd
  have hdOne := hd.2 1 hone
  simp only [one_mul] at hdOne
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hpUpperReal : (p : Real) <= 16 * l := by exact_mod_cast hpUpper
  have hD : (centeredAbs d : Real) <=
      alpha / (512 * Real.pi * (m : Real) ^ 2) * p := hdOne
  have hDmul : (centeredAbs d : Real) * (m : Real) ^ 2 <=
      alpha * p / (512 * Real.pi) := by
    calc
      (centeredAbs d : Real) * (m : Real) ^ 2 <=
          (alpha / (512 * Real.pi * (m : Real) ^ 2) * p) *
            (m : Real) ^ 2 := by gcongr
      _ = alpha * p / (512 * Real.pi) := by field_simp
  have hlt : (centeredAbs d : Real) * (m : Real) ^ 2 < l := by
    calc
      (centeredAbs d : Real) * (m : Real) ^ 2 <=
          alpha * p / (512 * Real.pi) := hDmul
      _ <= 16 * l / (512 * Real.pi) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      _ < l := by
        have hlPos : (0 : Real) < l := by
          have : 0 < l := by have := NeZero.pos p; omega
          exact_mod_cast this
        have hpi := Real.pi_gt_three
        apply (div_lt_iff₀ (by positivity : (0 : Real) < 512 * Real.pi)).2
        nlinarith
  have hltNat : centeredAbs d * m ^ 2 < l := by exact_mod_cast hlt
  simpa only [pow_two] using hltNat

private lemma cor711_residueClass_large {l d m : Nat}
    (hm : 0 < m) (hd : 0 < d) (hsmall : d * (m * m) < l) :
    d <= l /\ forall a : Fin d, m * m <= residueClassLength l d a := by
  have hdl : d <= l := by
    have hmSq : 1 <= m * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have := Nat.mul_le_mul_left d hmSq
    omega
  refine ⟨hdl, ?_⟩
  intro a
  have hcoord : (a : Nat) + (m * m - 1) * d < l := by
    have ha : (a : Nat) < d := a.isLt
    have hmul : (m * m - 1) * d + d = (m * m) * d := by
      have hmSq : 0 < m * m := by positivity
      rw [← Nat.succ_mul]
      congr 1
      omega
    rw [Nat.mul_comm d (m * m)] at hsmall
    omega
  have hquot := (quotient_lt_residueClassLength hd a.isLt hdl).2 hcoord
  omega

private def Cor711Conclusion {N q : Nat} (m : Nat) (R : IntAP)
    (A : Fin q -> Finset Int) (phi : Fin q -> Int -> ZMod N) : Prop :=
  exists M : Nat, exists S : Fin M -> IntAP,
    IsIntAPPartition S R /\
    (forall j, (S j).IsProper /\
      ((S j).length = m \/ (S j).length = m + 1)) /\
    (exists d : Nat, 0 < d /\ forall j, (S j).step = d) /\
    (forall i j, IntAPLinearOn (S j) (A i) (phi i))

/-- The corrected finite form of Corollary 7.11, including the lower-size
hypothesis required by the nonzero Bohr-neighborhood argument. -/
theorem corollary_7_11_holds : corollary_7_11 := by
  intro N q m _ R A phi alpha hq hm halpha hl hproper hA hmBound hlarge
  by_cases hmOne : m = 1
  · subst m
    exact cor711_one_partition R A phi hl hproper
  have hmTwo : 2 <= m := by omega
  have halphaOne := cor711_alpha_le_one R A alpha hq hl hproper
    (fun i => ⟨(hA i).1, (hA i).2.1⟩)
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (8 * R.length) (by omega)
  have hpUpper' : p <= 16 * R.length := by omega
  letI : NeZero p := ⟨hpPrime.ne_zero⟩
  let L := cor711SpectrumUnion p R A
  have hspec (i : Fin q) := cor711_spectrum_bound R A phi alpha hl halpha
    hproper.1 hpLower hpUpper' hA i
  have hLcard : ((L.card : Nat) : Real) <=
      4097 * q * alpha ^ (-(2 : Real)) := by
    dsimp only [L]
    exact cor711_spectrumUnion_card R A alpha hq halpha halphaOne
      (fun i => (hspec i).1)
  have honeL : (1 : ZMod p) ∈ L := by
    simp [L, cor711SpectrumUnion]
  have hLne : L.Nonempty := ⟨1, honeL⟩
  have hLcardPosNat : 0 < L.card := Finset.card_pos.mpr hLne
  have hLcardPos : (0 : Real) < L.card := by exact_mod_cast hLcardPosNat
  let delta : Real := alpha / (512 * Real.pi * (m : Real) ^ 2)
  have hdelta : 0 < delta := by unfold delta; positivity
  have hdeltaOne : delta <= 1 := by
    unfold delta
    apply (div_le_one₀ (by positivity : (0 : Real) <
      512 * Real.pi * (m : Real) ^ 2)).2
    have hmReal : (2 : Real) <= m := by exact_mod_cast hmTwo
    have hpi := Real.pi_gt_three
    nlinarith
  have hthreshold :
      2 * (p : Real) ^ (-(1 / (L.card : Real))) < delta := by
    unfold delta
    exact cor711_bohr_nonzero_threshold hq hmTwo hl halpha (by omega)
      hLcardPos hLcard hmBound hlarge
  have hpTwo : 2 <= p := hpPrime.two_le
  obtain ⟨_hcardBohr, hnonzero⟩ :=
    lemma_7_7_holds p L delta hpTwo hdelta hdeltaOne
  obtain ⟨d, hdBohr, hdne⟩ := hnonzero hLne hthreshold
  let D := centeredAbs d
  have hDpos : 0 < D := centeredAbs_pos_of_ne_zero hdne
  have hDsmall : D * (m * m) < R.length := by
    dsimp only [D]
    exact cor711_centered_step_small hm halpha halphaOne hpUpper'
      L honeL d hdBohr
  obtain ⟨hDle, hclasses⟩ := cor711_residueClass_large hm hDpos hDsmall
  let M := Fintype.card (BalancedResidueChunkIndex R.length D m)
  let S := balancedResidueChunkFamily R D m
  refine ⟨M, S,
    balancedResidueChunkFamily_partition R D m hproper.1 hDpos hDle hm hclasses,
    (balancedResidueChunkFamily_properties R D m hproper.1 hDpos).1,
    (balancedResidueChunkFamily_properties R D m hproper.1 hDpos).2, ?_⟩
  intro i j
  let z := (Fintype.equivFin (BalancedResidueChunkIndex R.length D m)).symm j
  obtain ⟨_hKi, hAmodNe, psi, hpsi, hagree⟩ := hspec i
  let beta := cor711Density p R (A i)
  let K := cor711Spectrum p R A i
  have hbetaLower := cor711_density_lower R A alpha halpha hproper.1
    (by omega : R.length < p) hpUpper'
    (fun i => ⟨(hA i).1, (hA i).2.1⟩) i
  have hbeta : 0 < beta := by dsimp only [beta]; nlinarith
  have hKsub : K ⊆ L := by
    intro r hr
    simp only [L, cor711SpectrumUnion, Finset.mem_union, Finset.mem_singleton]
    right
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hr⟩
  have hdSigned : (D : ZMod p) ∈ bohr L delta := by
    rcases natCast_centeredAbs_eq_or_neg d with hdCast | hdCast
    · simpa only [D, hdCast] using hdBohr
    · rw [hdCast]
      exact bohr_neg_mem hdBohr
  have hradius : delta <= beta / (32 * Real.pi) / (m : Real) := by
    have hmReal : (1 : Real) <= m := by exact_mod_cast hm
    have hleft : alpha * (32 * Real.pi * (m : Real)) <=
        (16 * beta) * (32 * Real.pi * (m : Real)) := by gcongr
    have hright : (16 * beta) * (32 * Real.pi * (m : Real)) <=
        beta * (512 * Real.pi * (m : Real) ^ 2) := by
      have hnonneg : 0 <= beta * (512 * Real.pi * (m : Real)) := by positivity
      calc
        (16 * beta) * (32 * Real.pi * (m : Real)) =
            beta * (512 * Real.pi * (m : Real)) := by ring
        _ <= beta * (512 * Real.pi * (m : Real)) * m := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hmReal hnonneg
        _ = beta * (512 * Real.pi * (m : Real) ^ 2) := by ring
    unfold delta
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : (0 : Real) <
      512 * Real.pi * (m : Real) ^ 2)
      (by positivity : (0 : Real) < 32 * Real.pi * m)).2
    exact hleft.trans hright
  have hdKi : (D : ZMod p) ∈
      bohr K (beta / (32 * Real.pi) / (m : Real)) :=
    bohr_mono hKsub hradius hdSigned
  have hshort : symmetricMultiples (D : ZMod p) m ⊆
      bohr K (beta / (32 * Real.pi)) :=
    bohr_symmetric_multiples_subset K (beta / (32 * Real.pi))
      (by positivity) m hm (D : ZMod p) hdKi
  change IntAPLinearOn (balancedResidueChunkAP R D m z) (A i) (phi i)
  exact balancedResidueChunkAP_linear R (A i) (phi i) D m z hDpos hDle hm
    (by omega : R.length < p) (hclasses z.1)
    (bohr K (beta / (32 * Real.pi))) psi hpsi hagree hshort hAmodNe

end LeanProofs.GowersSzemeredi
