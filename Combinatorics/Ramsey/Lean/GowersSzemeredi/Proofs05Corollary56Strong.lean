import GowersSzemeredi.Proofs02Partition
import GowersSzemeredi.Proofs05PolynomialPartition
import GowersSzemeredi.Proofs05Lemma9Induction
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The strong diameter form of Corollary 5.6

This file proves the strengthened one-polynomial partition statement isolated
in `Proofs05Lemma9`.  The nonlinear step uses the square-root recurrence from
Lemma 5.5, splits the interval into balanced chunks in residue classes modulo
the recurrence step, and applies degree induction to the lower-degree part of
the affine pullback.  The linear base case is separate: its extra diameter
power comes from Lemma 2.3, followed by a balanced subdivision of each of its
cells.

The proof first keeps track of a modular centre and a radius.  Doubling that
radius produces the interval-diameter convention used in the statement.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Centred-radius bookkeeping -/

/-- A finite set lies in a symmetric modular ball of an integral radius, with
the cast of that radius bounded by the displayed real scale. -/
private def cor56CenteredRadiusAtMostReal {N : Nat}
    (A : Finset (ZMod N)) (s : Real) : Prop :=
  exists e : Nat, exists a : ZMod N,
    (forall x, x ∈ A -> centeredAbs (x - a) <= e) /\ (e : Real) <= s

private lemma cor56_centeredAbs_add_le {N : Nat} [NeZero N]
    (x y : ZMod N) :
    centeredAbs (x + y) <= centeredAbs x + centeredAbs y := by
  unfold centeredAbs
  calc
    (x + y).valMinAbs.natAbs <=
        (x.valMinAbs + y.valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le x y
    _ <= x.valMinAbs.natAbs + y.valMinAbs.natAbs := Int.natAbs_add_le _ _

private lemma cor56_centeredAbs_nsmul_le {N : Nat} [NeZero N]
    (n : Nat) (x : ZMod N) :
    centeredAbs (n • x) <= n * centeredAbs x := by
  induction n with
  | zero => simp [centeredAbs]
  | succ n ih =>
      rw [succ_nsmul, Nat.succ_mul]
      exact (cor56_centeredAbs_add_le (n • x) x).trans
        (Nat.add_le_add_right ih _)

private lemma cor56_centeredAbs_nat_mul_le {N : Nat} [NeZero N]
    (n : Nat) (x : ZMod N) :
    centeredAbs ((n : ZMod N) * x) <= n * centeredAbs x := by
  simpa only [nsmul_eq_mul] using cor56_centeredAbs_nsmul_le n x

private lemma cor56_mem_shifted_interval_of_centeredAbs_le
    {N e : Nat} [NeZero N] {a x : ZMod N}
    (hx : centeredAbs (x - a) <= e) :
    x ∈ (modInterval N (a - (e : ZMod N)) (2 * e + 1)).carrier := by
  classical
  generalize hzdef : (x - a).valMinAbs = z
  have hzcast : (z : ZMod N) = x - a := by
    rw [← hzdef]
    exact ZMod.coe_valMinAbs _
  have hzabs : z.natAbs <= e := by
    rw [← hzdef]
    simpa only [centeredAbs] using hx
  rw [modInterval, ModAP.carrier]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, mul_one]
  cases z with
  | ofNat n =>
      have hn : n <= e := by exact hzabs
      refine ⟨⟨e + n, by omega⟩, ?_⟩
      have hxn : x = a + (n : ZMod N) := by
        have hzcast' : (n : ZMod N) = x - a := by
          simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hzcast
        calc
          x = (x - a) + a := by ring
          _ = (n : ZMod N) + a := by rw [← hzcast']
          _ = a + (n : ZMod N) := by ring
      rw [hxn]
      rw [Nat.cast_add]
      ring
  | negSucc n =>
      have hn' : n < e := by exact hzabs
      have hn : n + 1 <= e := by omega
      refine ⟨⟨e - (n + 1), by omega⟩, ?_⟩
      have hxn : x = a - ((n + 1 : Nat) : ZMod N) := by
        have hzcast' : -((n + 1 : Nat) : ZMod N) = x - a := by
          simpa only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one] using hzcast
        calc
          x = (x - a) + a := by ring
          _ = -((n + 1 : Nat) : ZMod N) + a := by rw [← hzcast']
          _ = a - ((n + 1 : Nat) : ZMod N) := by ring
      rw [hxn]
      rw [Nat.cast_sub hn]
      ring

private lemma cor56_centeredRadius_to_diameter {N : Nat} [NeZero N]
    {A : Finset (ZMod N)} {s : Real}
    (hA : cor56CenteredRadiusAtMostReal A s) :
    diameterAtMostReal A (2 * s) := by
  obtain ⟨e, a, hcenter, hescale⟩ := hA
  refine ⟨2 * e, ⟨a - (e : ZMod N), ?_⟩, ?_⟩
  · intro x hx
    exact cor56_mem_shifted_interval_of_centeredAbs_le (hcenter x hx)
  · push_cast
    exact mul_le_mul_of_nonneg_left hescale (by norm_num)

private lemma cor56_centeredRadius_mono {N : Nat}
    {A B : Finset (ZMod N)} {s t : Real}
    (hAB : A ⊆ B) (hB : cor56CenteredRadiusAtMostReal B s)
    (hst : s <= t) : cor56CenteredRadiusAtMostReal A t := by
  obtain ⟨e, a, hcenter, hescale⟩ := hB
  exact ⟨e, a, fun x hx => hcenter x (hAB hx), hescale.trans hst⟩

private lemma cor56_centeredRadius_add_error {N : Nat} [NeZero N]
    {X : Type*} [DecidableEq X] (S : Finset X)
    (f g : X -> ZMod N) {s : Real}
    (hf : cor56CenteredRadiusAtMostReal (S.image f) s)
    (E : Nat) (hg : forall x, x ∈ S -> centeredAbs (g x) <= E) :
    cor56CenteredRadiusAtMostReal (S.image fun x => f x + g x)
      (s + E) := by
  obtain ⟨e, a, hfcenter, hescale⟩ := hf
  refine ⟨e + E, a, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hfx : f x ∈ S.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hadd : f x + g x - a = (f x - a) + g x := by ring
    rw [hadd]
    exact (cor56_centeredAbs_add_le (f x - a) (g x)).trans
      (Nat.add_le_add (hfcenter (f x) hfx) (hg x hx))
  · push_cast
    exact add_le_add hescale le_rfl

private lemma cor56_diameter_to_centeredRadius {N : Nat} [NeZero N]
    {A : Finset (ZMod N)} {d : Nat} (hA : diameterAtMost A d) :
    cor56CenteredRadiusAtMostReal A d := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨d, a, ?_, le_rfl⟩
  intro x hx
  have hmem := ha hx
  rw [modInterval, ModAP.carrier] at hmem
  simp only [Finset.mem_image, Finset.mem_univ, true_and, mul_one] at hmem
  obtain ⟨i, hxi⟩ := hmem
  have hi : (i : Nat) <= d := by omega
  have hdiff : x - a = (i : Nat) := by
    rw [← hxi]
    ring
  rw [hdiff]
  exact (by
    rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
    exact (Nat.min_le_left _ _).trans ((Nat.mod_le _ _).trans hi))

/-! ## Balanced chunks in residue classes -/

private def cor56ResidueClassLength (r d a : Nat) : Nat :=
  (r - 1 - a) / d + 1

private lemma cor56_quotient_lt_residueClassLength {r d a t : Nat}
    (hd : 0 < d) (had : a < d) (hdr : d <= r) :
    t < cor56ResidueClassLength r d a <-> a + t * d < r := by
  have har : a <= r - 1 := by omega
  rw [cor56ResidueClassLength, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
  omega

private def cor56BalancedChunkStart (m b j : Nat) : Nat :=
  j * m + min j b

private def cor56BalancedChunkLength (m b j : Nat) : Nat :=
  if j < b then m + 1 else m

private lemma cor56BalancedChunkStart_of_lt {m b j : Nat} (hjb : j < b) :
    cor56BalancedChunkStart m b j = j * (m + 1) := by
  rw [cor56BalancedChunkStart, min_eq_left hjb.le, Nat.mul_add, Nat.mul_one]

private lemma cor56BalancedChunkStart_of_ge {m b j : Nat} (hbj : b <= j) :
    cor56BalancedChunkStart m b j = j * m + b := by
  rw [cor56BalancedChunkStart, min_eq_right hbj]

private lemma cor56BalancedChunkLength_of_lt {m b j : Nat} (hjb : j < b) :
    cor56BalancedChunkLength m b j = m + 1 := by
  simp [cor56BalancedChunkLength, hjb]

private lemma cor56BalancedChunkLength_of_ge {m b j : Nat} (hbj : b <= j) :
    cor56BalancedChunkLength m b j = m := by
  simp [cor56BalancedChunkLength, Nat.not_lt.mpr hbj]

private lemma cor56BalancedChunk_end (m b j : Nat) :
    cor56BalancedChunkStart m b j + cor56BalancedChunkLength m b j =
      cor56BalancedChunkStart m b (j + 1) := by
  by_cases hjb : j < b
  · have hsucc : j + 1 <= b := by omega
    rw [cor56BalancedChunkStart_of_lt hjb,
      cor56BalancedChunkLength_of_lt hjb, cor56BalancedChunkStart,
      min_eq_left hsucc]
    ring
  · have hbj : b <= j := Nat.le_of_not_gt hjb
    have hsucc : b <= j + 1 := hbj.trans (Nat.le_succ _)
    rw [cor56BalancedChunkStart_of_ge hbj,
      cor56BalancedChunkLength_of_ge hbj,
      cor56BalancedChunkStart_of_ge hsucc]
    ring

private lemma cor56BalancedChunkStart_mono {m b j k : Nat} (hjk : j <= k) :
    cor56BalancedChunkStart m b j <= cor56BalancedChunkStart m b k := by
  unfold cor56BalancedChunkStart
  exact Nat.add_le_add (Nat.mul_le_mul_right m hjk) (min_le_min hjk le_rfl)

private lemma cor56_remainder_le_quotient {c m : Nat} (hm : 0 < m)
    (hcm : m * m <= c) : c % m <= c / m := by
  have hmq : m <= c / m := (Nat.le_div_iff_mul_le hm).2 hcm
  exact (Nat.mod_lt c hm).le.trans hmq

private lemma cor56BalancedChunk_quotient_lt {c m : Nat}
    (hm : 0 < m) (hcm : m * m <= c) (j : Fin (c / m)) (i : Nat)
    (hi : i < cor56BalancedChunkLength m (c % m) j) :
    cor56BalancedChunkStart m (c % m) j + i < c := by
  have hbq : c % m <= c / m := cor56_remainder_le_quotient hm hcm
  calc
    cor56BalancedChunkStart m (c % m) j + i <
        cor56BalancedChunkStart m (c % m) j +
          cor56BalancedChunkLength m (c % m) j := Nat.add_lt_add_left hi _
    _ = cor56BalancedChunkStart m (c % m) ((j : Nat) + 1) :=
      cor56BalancedChunk_end _ _ _
    _ <= cor56BalancedChunkStart m (c % m) (c / m) :=
      cor56BalancedChunkStart_mono j.isLt
    _ = (c / m) * m + c % m := cor56BalancedChunkStart_of_ge hbq
    _ = c := by simpa only [Nat.mul_comm] using Nat.div_add_mod c m

private lemma cor56_exists_balancedChunk_for_quotient {c m t : Nat}
    (hm : 0 < m) (hcm : m * m <= c) (ht : t < c) :
    exists j : Fin (c / m), exists i : Nat,
      i < cor56BalancedChunkLength m (c % m) j /\
      t = cor56BalancedChunkStart m (c % m) j + i := by
  let n := c / m
  let b := c % m
  have hdecomp : c = n * m + b := by
    simpa only [n, b, Nat.mul_comm] using (Nat.div_add_mod c m).symm
  have hbn : b <= n := cor56_remainder_le_quotient hm hcm
  by_cases hfront : t < b * (m + 1)
  · let j : Fin n := ⟨t / (m + 1), by
      have hmp : 0 < m + 1 := by omega
      have hjb : t / (m + 1) < b := (Nat.div_lt_iff_lt_mul hmp).2 hfront
      exact hjb.trans_le hbn⟩
    let i := t % (m + 1)
    have hjb : (j : Nat) < b := by
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).2 hfront
    refine ⟨j, i, ?_, ?_⟩
    · rw [cor56BalancedChunkLength_of_lt hjb]
      exact Nat.mod_lt _ (by omega)
    · rw [cor56BalancedChunkStart_of_lt hjb]
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
    · rw [cor56BalancedChunkLength_of_ge hbj]
      exact Nat.mod_lt _ hm
    · rw [cor56BalancedChunkStart_of_ge hbj]
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

private lemma cor56BalancedChunk_index_unique {c m t : Nat}
    (j j' : Fin (c / m)) (i i' : Nat)
    (hi : i < cor56BalancedChunkLength m (c % m) j)
    (hi' : i' < cor56BalancedChunkLength m (c % m) j')
    (ht : t = cor56BalancedChunkStart m (c % m) j + i)
    (ht' : t = cor56BalancedChunkStart m (c % m) j' + i') : j = j' := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjj' | hj'j
  · have hlt : t < cor56BalancedChunkStart m (c % m) j' := by
      calc
        t = cor56BalancedChunkStart m (c % m) j + i := ht
        _ < cor56BalancedChunkStart m (c % m) j +
            cor56BalancedChunkLength m (c % m) j := Nat.add_lt_add_left hi _
        _ = cor56BalancedChunkStart m (c % m) ((j : Nat) + 1) :=
          cor56BalancedChunk_end _ _ _
        _ <= cor56BalancedChunkStart m (c % m) j' :=
          cor56BalancedChunkStart_mono (Nat.succ_le_iff.mpr hjj')
    have hge : cor56BalancedChunkStart m (c % m) j' <= t := by
      rw [ht']
      omega
    omega
  · have hlt : t < cor56BalancedChunkStart m (c % m) j := by
      calc
        t = cor56BalancedChunkStart m (c % m) j' + i' := ht'
        _ < cor56BalancedChunkStart m (c % m) j' +
            cor56BalancedChunkLength m (c % m) j' := Nat.add_lt_add_left hi' _
        _ = cor56BalancedChunkStart m (c % m) ((j' : Nat) + 1) :=
          cor56BalancedChunk_end _ _ _
        _ <= cor56BalancedChunkStart m (c % m) j :=
          cor56BalancedChunkStart_mono (Nat.succ_le_iff.mpr hj'j)
    have hge : cor56BalancedChunkStart m (c % m) j <= t := by
      rw [ht]
      omega
    omega

private abbrev Cor56BalancedResidueChunkIndex (r d m : Nat) :=
  Sigma fun a : Fin d => Fin (cor56ResidueClassLength r d a / m)

private def cor56BalancedResidueChunkAP (r d m : Nat)
    (z : Cor56BalancedResidueChunkIndex r d m) : NatAP where
  start := z.1 + cor56BalancedChunkStart m
    (cor56ResidueClassLength r d z.1 % m) z.2 * d
  step := d
  length := cor56BalancedChunkLength m
    (cor56ResidueClassLength r d z.1 % m) z.2

private noncomputable def cor56BalancedResidueChunkFamily (r d m : Nat) :
    Fin (Fintype.card (Cor56BalancedResidueChunkIndex r d m)) -> NatAP :=
  fun j => cor56BalancedResidueChunkAP r d m ((Fintype.equivFin _).symm j)

private lemma cor56BalancedResidueChunkAP_mem_iff (r d m : Nat)
    (z : Cor56BalancedResidueChunkIndex r d m) (x : Nat) :
    x ∈ (cor56BalancedResidueChunkAP r d m z).carrier <->
      exists i : Nat,
        i < cor56BalancedChunkLength m
          (cor56ResidueClassLength r d z.1 % m) z.2 /\
        x = z.1 + (cor56BalancedChunkStart m
          (cor56ResidueClassLength r d z.1 % m) z.2 + i) * d := by
  classical
  rw [NatAP.carrier]
  constructor
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨i, i.isLt, ?_⟩
    simp only [cor56BalancedResidueChunkAP]
    ring
  · rintro ⟨i, hi, rfl⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only [cor56BalancedResidueChunkAP]
    ring

private lemma cor56BalancedResidueChunkAP_isProper (r d m : Nat)
    (hd : 0 < d) (z : Cor56BalancedResidueChunkIndex r d m) :
    (cor56BalancedResidueChunkAP r d m z).IsProper := by
  constructor
  · simpa only [cor56BalancedResidueChunkAP] using hd
  · classical
    rw [NatAP.carrier, Finset.card_image_iff.mpr]
    · simp
    · intro i _hi j _hj hij
      apply Fin.ext
      simp only [cor56BalancedResidueChunkAP] at hij
      have hmul : (i : Nat) * d = (j : Nat) * d := Nat.add_left_cancel hij
      exact Nat.eq_of_mul_eq_mul_right hd hmul

private lemma cor56BalancedResidueChunkFamily_partition (r d m : Nat)
    (hd : 0 < d) (hdr : d <= r) (hm : 0 < m)
    (hclass : forall a : Fin d,
      m * m <= cor56ResidueClassLength r d a) :
    IsNatAPPartition (cor56BalancedResidueChunkFamily r d m)
      (Finset.range r) := by
  classical
  let E := Fintype.equivFin (Cor56BalancedResidueChunkIndex r d m)
  constructor
  · intro x
    constructor
    · intro hx
      have hxr : x < r := Finset.mem_range.mp hx
      let a : Fin d := ⟨x % d, Nat.mod_lt x hd⟩
      let u := x / d
      have hu : u < cor56ResidueClassLength r d a := by
        rw [cor56_quotient_lt_residueClassLength hd a.isLt hdr]
        dsimp only [a, u]
        calc
          x % d + (x / d) * d = x := by
            simpa only [Nat.mul_comm] using Nat.mod_add_div x d
          _ < r := hxr
      obtain ⟨j, i, hi, huRep⟩ :=
        cor56_exists_balancedChunk_for_quotient hm (hclass a) hu
      let z : Cor56BalancedResidueChunkIndex r d m := ⟨a, j⟩
      refine ⟨E z, ?_⟩
      change x ∈ (cor56BalancedResidueChunkAP r d m
        ((Fintype.equivFin _).symm (E z))).carrier
      have hEz : (Fintype.equivFin _).symm (E z) = z := by
        simp only [E, Equiv.symm_apply_apply]
      rw [hEz, cor56BalancedResidueChunkAP_mem_iff]
      refine ⟨i, hi, ?_⟩
      dsimp only [z]
      calc
        x = x % d + d * (x / d) := (Nat.mod_add_div x d).symm
        _ = a + u * d := by simp only [a, u, Nat.mul_comm]
        _ = a + (cor56BalancedChunkStart m
            (cor56ResidueClassLength r d a % m) j + i) * d := by rw [huRep]
    · rintro ⟨j, hj⟩
      let z := E.symm j
      change x ∈ (cor56BalancedResidueChunkAP r d m
        ((Fintype.equivFin _).symm j)).carrier at hj
      have hz : (Fintype.equivFin _).symm j = z := rfl
      rw [hz, cor56BalancedResidueChunkAP_mem_iff] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      apply Finset.mem_range.mpr
      rw [← cor56_quotient_lt_residueClassLength hd z.1.isLt hdr]
      exact cor56BalancedChunk_quotient_lt hm (hclass z.1) z.2 i hi
  · intro j j' hjj'
    rw [Finset.disjoint_left]
    intro x hx hx'
    let z := E.symm j
    let z' := E.symm j'
    change x ∈ (cor56BalancedResidueChunkAP r d m
      ((Fintype.equivFin _).symm j)).carrier at hx
    change x ∈ (cor56BalancedResidueChunkAP r d m
      ((Fintype.equivFin _).symm j')).carrier at hx'
    have hz : (Fintype.equivFin _).symm j = z := rfl
    have hz' : (Fintype.equivFin _).symm j' = z' := rfl
    rw [hz, cor56BalancedResidueChunkAP_mem_iff] at hx
    rw [hz', cor56BalancedResidueChunkAP_mem_iff] at hx'
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨i', hi', hxi'⟩ := hx'
    have haVal : (z.1 : Nat) = (z'.1 : Nat) := by
      have hmod := congrArg (fun y : Nat => y % d) (hxi.symm.trans hxi')
      simpa only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt z.1.isLt,
        Nat.mod_eq_of_lt z'.1.isLt] using hmod
    have ha : z.1 = z'.1 := Fin.ext haVal
    rcases z with ⟨a, k⟩
    rcases z' with ⟨a', k'⟩
    dsimp only at ha
    subst a'
    have hquotMul :
        (cor56BalancedChunkStart m
            (cor56ResidueClassLength r d a % m) k + i) * d =
          (cor56BalancedChunkStart m
            (cor56ResidueClassLength r d a % m) k' + i') * d :=
      Nat.add_left_cancel (hxi.symm.trans hxi')
    have hquot :
        cor56BalancedChunkStart m
            (cor56ResidueClassLength r d a % m) k + i =
          cor56BalancedChunkStart m
            (cor56ResidueClassLength r d a % m) k' + i' :=
      Nat.eq_of_mul_eq_mul_right hd hquotMul
    have hk : k = k' :=
      cor56BalancedChunk_index_unique k k' i i' hi hi' rfl hquot
    subst k'
    have hzEq : j = j' := by
      apply E.symm.injective
      exact hz.trans hz'.symm
    exact bne_iff_ne.mp hjj' hzEq

private lemma cor56BalancedResidueChunkFamily_properties (r d m : Nat)
    (hd : 0 < d) :
    forall j, (cor56BalancedResidueChunkFamily r d m j).IsProper /\
      ((cor56BalancedResidueChunkFamily r d m j).length = m \/
        (cor56BalancedResidueChunkFamily r d m j).length = m + 1) := by
  intro j
  let z := (Fintype.equivFin (Cor56BalancedResidueChunkIndex r d m)).symm j
  constructor
  · change (cor56BalancedResidueChunkAP r d m z).IsProper
    exact cor56BalancedResidueChunkAP_isProper r d m hd z
  · change cor56BalancedChunkLength m
        (cor56ResidueClassLength r d z.1 % m) z.2 = m \/
      cor56BalancedChunkLength m
        (cor56ResidueClassLength r d z.1 % m) z.2 = m + 1
    unfold cor56BalancedChunkLength
    split_ifs <;> simp_all

private lemma cor56BalancedResidueChunkFamily_nonempty (r d m : Nat)
    (hd : 0 < d) (hm : 0 < m)
    (hclass : forall a : Fin d,
      m * m <= cor56ResidueClassLength r d a) :
    0 < Fintype.card (Cor56BalancedResidueChunkIndex r d m) := by
  let a : Fin d := ⟨0, hd⟩
  have hcm : m <= cor56ResidueClassLength r d a := by
    have hmm : m <= m * m := by
      simpa only [mul_one] using Nat.mul_le_mul_left m (show 1 <= m by omega)
    exact hmm.trans (hclass a)
  have hquot : 0 < cor56ResidueClassLength r d a / m :=
    Nat.div_pos hcm hm
  let z : Cor56BalancedResidueChunkIndex r d m :=
    ⟨a, ⟨0, hquot⟩⟩
  exact Fintype.card_pos_iff.mpr ⟨z⟩

/-! ## Removing the top coefficient after an affine pullback -/

private def cor56CoefficientPolynomial {N k : Nat}
    (c : Fin (k + 1) -> ZMod N) : Polynomial (ZMod N) :=
  Polynomial.ofFn (k + 1) c

private lemma cor56CoefficientPolynomial_natDegree_lt {N k : Nat}
    (c : Fin (k + 1) -> ZMod N) :
    (cor56CoefficientPolynomial c).natDegree < k + 1 := by
  exact Polynomial.ofFn_natDegree_lt (Nat.succ_pos k) c

private lemma cor56CoefficientPolynomial_eval {N k : Nat}
    (c : Fin (k + 1) -> ZMod N) (x : ZMod N) :
    (cor56CoefficientPolynomial c).eval x =
      ∑ i, c i * x ^ (i : Nat) := by
  let p : Polynomial (ZMod N) := cor56CoefficientPolynomial c
  have hpdeg : p.natDegree < k + 1 :=
    cor56CoefficientPolynomial_natDegree_lt c
  rw [Polynomial.eval_eq_sum_range' hpdeg]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _hi
  change (Polynomial.ofFn (k + 1) c).coeff (i : Nat) * x ^ (i : Nat) = _
  rw [Polynomial.ofFn_coeff_eq_val_of_lt c i.isLt]

private lemma cor56_taylor_coeff_of_natDegree_le {R : Type*} [CommRing R]
    (p : Polynomial R) (a : R) {k : Nat} (hp : p.natDegree <= k) :
    (p.taylor a).coeff k = p.coeff k := by
  rw [Polynomial.taylor_coeff]
  have hderiv : p.hasseDeriv k = Polynomial.C (p.coeff k) := by
    ext n
    rw [Polynomial.hasseDeriv_coeff]
    cases n with
    | zero => simp
    | succ n =>
        have hdeg : p.natDegree < Nat.succ n + k := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]
        simp
  rw [hderiv, Polynomial.eval_C]

private lemma cor56_affinePolynomial_natDegree_le {R : Type*} [CommRing R]
    (p : Polynomial R) (a d : R) {k : Nat} (hp : p.natDegree <= k) :
    ((p.taylor a).comp (Polynomial.C d * Polynomial.X)).natDegree <= k := by
  calc
    ((p.taylor a).comp (Polynomial.C d * Polynomial.X)).natDegree <=
        (p.taylor a).natDegree *
          (Polynomial.C d * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ <= k * 1 := by
      apply Nat.mul_le_mul
      · simpa only [Polynomial.natDegree_taylor] using hp
      · exact (Polynomial.natDegree_C_mul_le d Polynomial.X).trans
          Polynomial.natDegree_X_le
    _ = k := Nat.mul_one k

private lemma cor56_affinePolynomial_coeff_top {R : Type*} [CommRing R]
    (p : Polynomial R) (a d : R) {k : Nat} (hp : p.natDegree <= k) :
    ((p.taylor a).comp (Polynomial.C d * Polynomial.X)).coeff k =
      p.coeff k * d ^ k := by
  rw [Polynomial.comp_C_mul_X_coeff,
    cor56_taylor_coeff_of_natDegree_le p a hp]

private lemma cor56_erase_top_natDegree_le {R : Type*} [CommRing R]
    (q : Polynomial R) {k : Nat} (hk : 1 <= k) (hq : q.natDegree <= k) :
    (q - Polynomial.C (q.coeff k) * Polynomial.X ^ k).natDegree <= k - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
  by_cases hnk : n = k
  · subst n
    simp
  · have hkn : k < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hq.trans_lt hkn)]
    simp [hnk]

/-- After pulling a degree-`k` polynomial back along `x |-> a + d*x`, the
coefficient of `x^k` is the old top coefficient times `d^k`; subtracting that
term leaves degree at most `k-1`. -/
private lemma cor56_polynomialOn_affine_sub_top {N k : Nat} [NeZero N]
    (hk : 1 <= k) (phi : ZMod N -> ZMod N)
    (c : Fin (k + 1) -> ZMod N)
    (hc : forall x, phi x = ∑ i, c i * x ^ (i : Nat))
    (a d : ZMod N) :
    PolynomialOn (k - 1) Finset.univ
      (fun x => phi (a + x * d) -
        (c (Fin.last k) * d ^ k) * x ^ k) := by
  classical
  let p : Polynomial (ZMod N) := cor56CoefficientPolynomial c
  let q : Polynomial (ZMod N) :=
    (p.taylor a).comp (Polynomial.C d * Polynomial.X)
  let top : ZMod N := c (Fin.last k) * d ^ k
  let lower : Polynomial (ZMod N) :=
    q - Polynomial.C top * Polynomial.X ^ k
  have hpdeg : p.natDegree <= k :=
    Nat.lt_succ_iff.mp (cor56CoefficientPolynomial_natDegree_lt c)
  have hqdeg : q.natDegree <= k := by
    dsimp only [q]
    exact cor56_affinePolynomial_natDegree_le p a d hpdeg
  have hpcoeff : p.coeff k = c (Fin.last k) := by
    change (Polynomial.ofFn (k + 1) c).coeff k = c (Fin.last k)
    rw [Polynomial.ofFn_coeff_eq_val_of_lt c (by omega : k < k + 1)]
    apply congrArg c
    apply Fin.ext
    rfl
  have hqcoeff : q.coeff k = top := by
    dsimp only [q, top]
    rw [cor56_affinePolynomial_coeff_top p a d hpdeg, hpcoeff]
  have hlowerdeg : lower.natDegree < k := by
    have hle : lower.natDegree <= k - 1 := by
      dsimp only [lower]
      rw [← hqcoeff]
      exact cor56_erase_top_natDegree_le q hk hqdeg
    exact hle.trans_lt (by omega)
  change exists c' : Fin (k - 1 + 1) -> ZMod N,
    forall x, x ∈ Finset.univ ->
      phi (a + x * d) - (c (Fin.last k) * d ^ k) * x ^ k =
        ∑ i, c' i * x ^ (i : Nat)
  rw [Nat.sub_add_cancel hk]
  refine ⟨fun i : Fin k => lower.coeff i, ?_⟩
  intro x _hx
  have hpEval : phi (a + x * d) = p.eval (a + x * d) := by
    rw [hc]
    exact (cor56CoefficientPolynomial_eval c (a + x * d)).symm
  have hqEval : q.eval x = p.eval (a + x * d) := by
    dsimp only [q]
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.taylor_eval]
    congr 1
    ring
  calc
    phi (a + x * d) - (c (Fin.last k) * d ^ k) * x ^ k =
        lower.eval x := by
      dsimp only [lower, top]
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X_pow, hqEval, ← hpEval]
    _ = ∑ i : Fin k, lower.coeff (i : Nat) * x ^ (i : Nat) := by
      rw [Polynomial.eval_eq_sum_range' hlowerdeg]
      rw [← Fin.sum_univ_eq_sum_range]

private lemma cor56NatTransport_image {N : Nat} (P R : NatAP)
    (phi : ZMod N -> ZMod N) :
    (section5NatTransport P R).carrier.image
        (fun x : Nat => phi (x : ZMod N)) =
      R.carrier.image (fun t : Nat =>
        phi ((P.start : ZMod N) + (t : ZMod N) * (P.step : ZMod N))) := by
  classical
  rw [section5NatTransport_carrier, Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  change phi (section5NatIndexPoint P t : ZMod N) = _
  rw [section5NatIndexPoint_cast]

/-! ## Elementary singleton output -/

private def cor56SingletonNatAP (x : Nat) : NatAP where
  start := x
  step := 1
  length := 1

@[simp] private lemma cor56SingletonNatAP_carrier (x : Nat) :
    (cor56SingletonNatAP x).carrier = {x} := by
  classical
  ext y
  simp [cor56SingletonNatAP, NatAP.carrier]

private lemma cor56SingletonNatAP_isProper (x : Nat) :
    (cor56SingletonNatAP x).IsProper := by
  constructor
  · simp [cor56SingletonNatAP]
  · rw [cor56SingletonNatAP_carrier]
    simp [cor56SingletonNatAP]

private lemma cor56SingletonNatAP_partition (r : Nat) :
    IsNatAPPartition (fun i : Fin r => cor56SingletonNatAP i)
      (Finset.range r) := by
  classical
  constructor
  · intro x
    simp only [Finset.mem_range, cor56SingletonNatAP_carrier,
      Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  · intro i j hij
    change Disjoint (cor56SingletonNatAP (i : Nat)).carrier
      (cor56SingletonNatAP (j : Nat)).carrier
    rw [cor56SingletonNatAP_carrier, cor56SingletonNatAP_carrier]
    exact Finset.disjoint_singleton.mpr fun h =>
      bne_iff_ne.mp hij (Fin.ext h)

private lemma cor56_singleton_centeredRadius {N : Nat} [NeZero N]
    (phi : ZMod N -> ZMod N) (x : Nat) {s : Real} (hs : 0 <= s) :
    cor56CenteredRadiusAtMostReal
      ((cor56SingletonNatAP x).carrier.image
        (fun y : Nat => phi (y : ZMod N))) s := by
  refine ⟨0, phi (x : ZMod N), ?_, by simpa using hs⟩
  intro y hy
  rw [cor56SingletonNatAP_carrier] at hy
  simp only [Finset.image_singleton, Finset.mem_singleton] at hy
  subst y
  simp [centeredAbs]

/-! ## Quantitative constants -/

private def cor56DegreeScaleDenominator (k : Nat) : Nat :=
  k ^ 2 * 2 ^ (k + 2)

private lemma cor56_partitionConstant_pos (k : Nat) :
    0 < polynomialPartitionConstant k := by
  unfold polynomialPartitionConstant
  positivity

private lemma cor56_nat_succ_le_two_pow (e : Nat) : e + 1 <= 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [pow_succ]
      omega

private lemma cor56_nat_le_two_pow (k : Nat) : k <= 2 ^ k := by
  exact (Nat.le_succ k).trans (cor56_nat_succ_le_two_pow k)

/-- A non-evaluating way to extract a root from the double-exponential Weyl
threshold. -/
private lemma cor56_threshold_root {k t D E : Nat}
    (hD : 0 < D) (hDE : D * E <= 2 ^ (40 * k ^ 3))
    (ht : weylThreshold k <= t) :
    (2 : Real) ^ E <= (t : Real) ^ ((D : Real)⁻¹) := by
  let H := 2 ^ (40 * k ^ 3)
  have hDReal : (0 : Real) < D := by exact_mod_cast hD
  have hbase : ((2 ^ H : Nat) : Real) <= t := by
    dsimp only [H]
    exact_mod_cast (show 2 ^ (2 ^ (40 * k ^ 3)) <= t by
      simpa only [weylThreshold] using ht)
  calc
    (2 : Real) ^ E <=
        ((2 : Real) ^ H) ^ ((D : Real)⁻¹) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_natCast_mul (by norm_num : (0 : Real) <= 2)]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [mul_comm (H : Real) ((D : Real)⁻¹)]
      rw [le_inv_mul_iff₀ hDReal]
      exact_mod_cast hDE
    _ <= (t : Real) ^ ((D : Real)⁻¹) := by
      apply Real.rpow_le_rpow (by positivity)
      · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbase
      · positivity

private lemma cor56_degreeScaleDenominator_pos {k : Nat} (hk : 1 <= k) :
    0 < cor56DegreeScaleDenominator k := by
  unfold cor56DegreeScaleDenominator
  positivity

private lemma cor56_degreeScaleDenominator_four_le {k : Nat} (hk : 2 <= k) :
    4 <= cor56DegreeScaleDenominator k := by
  unfold cor56DegreeScaleDenominator
  have hkSq : 4 <= k ^ 2 := by nlinarith
  have hpow : 1 <= 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
  nlinarith

private lemma cor56_degreeScaleDenominator_le_two_pow {k : Nat} (hk : 2 <= k) :
    cor56DegreeScaleDenominator k <= 2 ^ (4 * k) := by
  have hkpow : k <= 2 ^ k := cor56_nat_le_two_pow k
  have hkSq : k ^ 2 <= 2 ^ (2 * k) := by
    calc
      k ^ 2 <= (2 ^ k) ^ 2 := Nat.pow_le_pow_left hkpow 2
      _ = 2 ^ (2 * k) := by rw [← pow_mul]; congr 1 <;> omega
  unfold cor56DegreeScaleDenominator
  calc
    k ^ 2 * 2 ^ (k + 2) <= 2 ^ (2 * k) * 2 ^ (k + 2) :=
      Nat.mul_le_mul_right _ hkSq
    _ = 2 ^ (3 * k + 2) := by rw [← pow_add]; congr 1 <;> omega
    _ <= 2 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)

private lemma cor56_factorial_le_two_pow_sq {k : Nat} :
    k.factorial <= 2 ^ (k ^ 2) := by
  calc
    k.factorial <= k ^ k := Nat.factorial_le_pow k
    _ <= (2 ^ k) ^ k := Nat.pow_le_pow_left (cor56_nat_le_two_pow k) k
    _ = 2 ^ (k ^ 2) := by rw [← pow_mul]; congr 1 <;> ring

private lemma cor56_partitionConstant_le_two_pow {k : Nat} (hk : 2 <= k) :
    polynomialPartitionConstant k <= 2 ^ (5 * k ^ 2) := by
  have hfac := cor56_factorial_le_two_pow_sq (k := k)
  unfold polynomialPartitionConstant
  calc
    k.factorial ^ 2 * 2 ^ ((k + 1) ^ 2) <=
        (2 ^ (k ^ 2)) ^ 2 * 2 ^ ((k + 1) ^ 2) := by gcongr
    _ = 2 ^ (2 * k ^ 2 + (k + 1) ^ 2) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ <= 2 ^ (5 * k ^ 2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith

private lemma cor56_cube_gap {k : Nat} (hk : 2 <= k) :
    4 * k + (40 * (k - 1) ^ 3 + 2) <= 40 * k ^ 3 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsub : 2 + j - 1 = j + 1 := by omega
  rw [hsub]
  nlinarith [show 0 <= j ^ 2 by positivity]

private lemma cor56_previousThreshold_root_bound {k r : Nat} (hk : 2 <= k)
    (hr : weylThreshold k <= r) :
    (4 : Real) * polynomialPartitionThreshold (k - 1) <=
      (r : Real) ^ ((cor56DegreeScaleDenominator k : Real)⁻¹) := by
  let D := cor56DegreeScaleDenominator k
  let A := 40 * (k - 1) ^ 3
  let E := 2 ^ (A + 1) + 2
  have hD : 0 < D := cor56_degreeScaleDenominator_pos (by omega)
  have hDpow : D <= 2 ^ (4 * k) :=
    cor56_degreeScaleDenominator_le_two_pow hk
  have hEpow : E <= 2 ^ (A + 2) := by
    have htwo : 2 <= 2 ^ (A + 1) := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ <= 2 ^ (A + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
    dsimp only [E]
    rw [show A + 2 = (A + 1) + 1 by omega, pow_succ]
    omega
  have hDE : D * E <= 2 ^ (40 * k ^ 3) := by
    calc
      D * E <= 2 ^ (4 * k) * 2 ^ (A + 2) := Nat.mul_le_mul hDpow hEpow
      _ = 2 ^ (4 * k + (A + 2)) := (pow_add _ _ _).symm
      _ <= 2 ^ (40 * k ^ 3) := by
        apply Nat.pow_le_pow_right (by norm_num)
        simpa only [A, Nat.add_assoc] using cor56_cube_gap hk
  have hroot := cor56_threshold_root hD hDE hr
  have hbase :
      (4 : Real) * polynomialPartitionThreshold (k - 1) = (2 : Real) ^ E := by
    have hNat :
        4 * polynomialPartitionThreshold (k - 1) = 2 ^ E := by
      unfold polynomialPartitionThreshold weylThreshold
      calc
        4 * (2 ^ (2 ^ (40 * (k - 1) ^ 3))) ^ 2 =
            2 ^ 2 * (2 ^ (2 ^ (40 * (k - 1) ^ 3))) ^ 2 := by norm_num
        _ = 2 ^ 2 * 2 ^ (2 ^ (40 * (k - 1) ^ 3) * 2) := by
          rw [← pow_mul]
        _ = 2 ^ (2 + 2 ^ (40 * (k - 1) ^ 3) * 2) := by
          rw [pow_add]
        _ = 2 ^ E := by
          congr 1
          dsimp only [E, A]
          rw [pow_succ]
          omega
    exact_mod_cast hNat
  rw [hbase]
  exact hroot

private lemma cor56_partitionConstant_times_small_le_tower {k : Nat}
    (hk : 2 <= k) :
    polynomialPartitionConstant k * (k + 2) <= 2 ^ (40 * k ^ 3) := by
  have hK := cor56_partitionConstant_le_two_pow hk
  have hsmall : k + 2 <= 2 ^ (k + 2) := by
    exact cor56_nat_le_two_pow (k + 2)
  calc
    polynomialPartitionConstant k * (k + 2) <=
        2 ^ (5 * k ^ 2) * 2 ^ (k + 2) := Nat.mul_le_mul hK hsmall
    _ = 2 ^ (5 * k ^ 2 + (k + 2)) := (pow_add _ _ _).symm
    _ <= 2 ^ (40 * k ^ 3) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith

private lemma cor56_global_root_absorbs_constant {k r : Nat} (hk : 2 <= k)
    (hr : weylThreshold k <= r) :
    (4 : Real) * 2 ^ k <=
      (r : Real) ^ ((polynomialPartitionConstant k : Real)⁻¹) := by
  have hroot := cor56_threshold_root
    (show 0 < polynomialPartitionConstant k by
      unfold polynomialPartitionConstant; positivity)
    (cor56_partitionConstant_times_small_le_tower hk) hr
  have hbase : (4 : Real) * 2 ^ k = (2 : Real) ^ (k + 2) := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1 <;> omega
  rw [hbase]
  exact hroot

private lemma cor56_global_root_two_le {k r : Nat} (hk : 2 <= k)
    (hr : weylThreshold k <= r) :
    (2 : Real) <=
      (r : Real) ^ ((polynomialPartitionConstant k : Real)⁻¹) := by
  have hpow : (1 : Real) <= 2 ^ k :=
    one_le_pow₀ (by norm_num : (1 : Real) <= 2)
  have htwo : (2 : Real) <= 4 * 2 ^ k := by nlinarith
  exact htwo.trans (cor56_global_root_absorbs_constant hk hr)

private lemma cor56_inductionDenominator_factor {k : Nat} (hk : 2 <= k) :
    polynomialPartitionInductionDenominator k =
      cor56DegreeScaleDenominator k * polynomialPartitionConstant (k - 1) := by
  have hkOne : 1 <= k := by omega
  have hkEq : k = (k - 1) + 1 := (Nat.sub_add_cancel hkOne).symm
  have hfac : k.factorial = k * (k - 1).factorial := by
    calc
      k.factorial = ((k - 1) + 1).factorial := by rw [← hkEq]
      _ = ((k - 1) + 1) * (k - 1).factorial := Nat.factorial_succ _
      _ = k * (k - 1).factorial := by rw [← hkEq]
  have hprevExponent : (k - 1 + 1) ^ 2 = k ^ 2 := by rw [Nat.sub_add_cancel hkOne]
  have hpow : 2 ^ (k ^ 2 + k + 2) = 2 ^ (k + 2) * 2 ^ (k ^ 2) := by
    rw [show k ^ 2 + k + 2 = (k + 2) + k ^ 2 by ring, pow_add]
  unfold polynomialPartitionInductionDenominator cor56DegreeScaleDenominator
    polynomialPartitionConstant
  rw [hfac, hprevExponent, hpow]
  ring

private lemma cor56_gamma_half_ge_three_over_K {k : Nat} (hk : 2 <= k) :
    3 * (polynomialPartitionConstant k : Real)⁻¹ <=
      (1 / 2 : Real) *
        (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by
  have hkpos : (0 : Real) < k := by positivity
  have hfac : (6 * k * (2 ^ (k + 1) : Nat)) <=
      polynomialPartitionConstant k := by
    unfold polynomialPartitionConstant
    have hkpow : k <= 2 ^ k := cor56_nat_le_two_pow k
    have hsmall : 6 * k <= 2 ^ (k * (k + 1)) := by
      calc
        6 * k <= 8 * k := by omega
        _ <= 8 * 2 ^ k := Nat.mul_le_mul_left 8 hkpow
        _ = 2 ^ (k + 3) := by
          rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]
          congr 1 <;> omega
        _ <= 2 ^ (k * (k + 1)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          nlinarith
    have hfacPos : 0 < k.factorial ^ 2 :=
      pow_pos (Nat.factorial_pos k) 2
    have hfacOne : 1 <= k.factorial ^ 2 := by omega
    calc
      6 * k * 2 ^ (k + 1) <=
          2 ^ (k * (k + 1)) * 2 ^ (k + 1) :=
        Nat.mul_le_mul_right _ hsmall
      _ = 2 ^ ((k + 1) ^ 2) := by
        rw [← pow_add]
        congr 1
        ring
      _ = 1 * 2 ^ ((k + 1) ^ 2) := by simp
      _ <= k.factorial ^ 2 * 2 ^ ((k + 1) ^ 2) :=
        Nat.mul_le_mul_right _ hfacOne
  have hfacReal :
      (6 : Real) * k * (2 : Real) ^ (k + 1) <=
        polynomialPartitionConstant k := by exact_mod_cast hfac
  have hKpos : (0 : Real) < polynomialPartitionConstant k := by
    unfold polynomialPartitionConstant
    positivity
  have hdenpos : (0 : Real) < (k : Real) * (2 : Real) ^ (k + 1) := by
    positivity
  have hright :
      (1 / 2 : Real) *
          (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) =
        1 / (2 * ((k : Real) * (2 : Real) ^ (k + 1))) := by
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [show 3 * (polynomialPartitionConstant k : Real)⁻¹ =
      3 / polynomialPartitionConstant k by simp [div_eq_mul_inv], hright]
  apply (div_le_div_iff₀ hKpos (mul_pos (by norm_num) hdenpos)).2
  nlinarith

private lemma cor56_recursive_exponent_gap {k : Nat} (hk : 2 <= k) :
    4 * (polynomialPartitionConstant k : Real)⁻¹ <=
      2 * ((cor56DegreeScaleDenominator k : Real)⁻¹) *
        (polynomialPartitionConstant (k - 1) : Real)⁻¹ := by
  have hfactor := cor56_inductionDenominator_factor hk
  have hDpos : (0 : Real) < cor56DegreeScaleDenominator k := by
    exact_mod_cast cor56_degreeScaleDenominator_pos (by omega : 1 <= k)
  have hKprev : (0 : Real) < polynomialPartitionConstant (k - 1) := by
    unfold polynomialPartitionConstant
    positivity
  have hind := polynomialPartition_two_mul_inverse_le_induction_exponent hk
  rw [hfactor] at hind
  push_cast at hind
  have hinv :
      ((cor56DegreeScaleDenominator k : Real) *
          polynomialPartitionConstant (k - 1))⁻¹ =
        (cor56DegreeScaleDenominator k : Real)⁻¹ *
          (polynomialPartitionConstant (k - 1) : Real)⁻¹ := by
    rw [mul_inv_rev]
    ring
  rw [hinv] at hind
  nlinarith

private lemma cor56_root_floor_bounds {k r : Nat} (hk : 2 <= k)
    (hr : weylThreshold k <= r) :
    let x : Real := (r : Real) ^
      ((cor56DegreeScaleDenominator k : Real)⁻¹)
    let m : Nat := Nat.floor x
    0 < m /\
      polynomialPartitionThreshold (k - 1) < m /\
      x / 2 <= m /\ (m : Real) <= x /\ (m + 1 : Nat) <= 2 * x /\
      m + 1 <= r := by
  let D := cor56DegreeScaleDenominator k
  let x : Real := (r : Real) ^ ((D : Real)⁻¹)
  let m : Nat := Nat.floor x
  have hrOneNat : 1 <= r := by
    have hWpos := weylThreshold_pos k
    omega
  have hrOne : (1 : Real) <= r := by exact_mod_cast hrOneNat
  have hxPrev : (4 : Real) * polynomialPartitionThreshold (k - 1) <= x := by
    simpa only [x, D] using cor56_previousThreshold_root_bound hk hr
  have hTpos : 0 < polynomialPartitionThreshold (k - 1) :=
    polynomialPartitionThreshold_positive _
  have hxFour : (4 : Real) <= x := by
    calc
      (4 : Real) <= 4 * polynomialPartitionThreshold (k - 1) := by
        exact_mod_cast Nat.mul_le_mul_left 4 (show 1 <= polynomialPartitionThreshold (k - 1) by omega)
      _ <= x := hxPrev
  have hxnonneg : 0 <= x :=
    le_trans (by norm_num : (0 : Real) <= 4) hxFour
  have hmle : (m : Real) <= x := by
    simpa only [m] using Nat.floor_le hxnonneg
  have hxlt : x < m + 1 := by
    simpa only [m] using Nat.lt_floor_add_one x
  have hmHalf : x / 2 <= m := by linarith
  have hmPosReal : (0 : Real) < m := by nlinarith
  have hmPos : 0 < m := by exact_mod_cast hmPosReal
  have hTm : polynomialPartitionThreshold (k - 1) < m := by
    have hfourTlt :
        (4 * polynomialPartitionThreshold (k - 1) : Nat) < m + 1 := by
      exact_mod_cast (lt_of_le_of_lt hxPrev hxlt)
    have hfourT :
        (4 * polynomialPartitionThreshold (k - 1) : Nat) <= m := by omega
    omega
  have hmSuccReal : ((m + 1 : Nat) : Real) <= 2 * x := by
    push_cast
    linarith
  have hDfour : (4 : Real) <= D := by
    exact_mod_cast cor56_degreeScaleDenominator_four_le hk
  have hDpos : (0 : Real) < D := lt_of_lt_of_le (by norm_num) hDfour
  have hinv : (D : Real)⁻¹ <= 1 := (inv_le_one₀ hDpos).2 (by linarith)
  have hrTwo : 2 <= r := by
    have hWtwo : 2 <= weylThreshold k := by
      unfold weylThreshold
      simpa only [pow_one] using
        pow_le_pow_right₀ (by norm_num : 1 <= (2 : Nat))
          (one_le_pow₀ (by norm_num : (1 : Nat) <= 2) :
            1 <= 2 ^ (40 * k ^ 3))
    exact hWtwo.trans hr
  have hrGtOne : (1 : Real) < r := by exact_mod_cast hrTwo
  have hinvLt : (D : Real)⁻¹ < 1 := by
    exact (inv_lt_one₀ hDpos).2 (by linarith)
  have hxltR : x < r := by
    dsimp only [x]
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hrGtOne hinvLt
  have hmSuccLeR : m + 1 <= r := by
    have hmLtR : (m : Real) < r := hmle.trans_lt hxltR
    exact_mod_cast hmLtR
  exact ⟨hmPos, hTm, hmHalf, hmle, by exact_mod_cast hmSuccReal, hmSuccLeR⟩

private lemma cor56_rootFloor_residue_classes_large {k r p : Nat}
    (hk : 2 <= k) (hr : weylThreshold k <= r)
    (hp : 1 <= p) (hpSq : p ^ 2 <= r) :
    let x : Real := (r : Real) ^
      ((cor56DegreeScaleDenominator k : Real)⁻¹)
    let m : Nat := Nat.floor x
    forall a : Fin p, m * m <= cor56ResidueClassLength r p a := by
  let D := cor56DegreeScaleDenominator k
  let x : Real := (r : Real) ^ ((D : Real)⁻¹)
  let m : Nat := Nat.floor x
  change forall a : Fin p, m * m <= cor56ResidueClassLength r p a
  intro a
  have hrOneNat : 1 <= r := by
    have hWpos := weylThreshold_pos k
    omega
  have hrPos : (0 : Real) < r := by exact_mod_cast hrOneNat
  have hrOne : (1 : Real) <= r := by exact_mod_cast hrOneNat
  have hmle : (m : Real) <= x :=
    (cor56_root_floor_bounds hk hr).2.2.2.1
  have hpRealSq : (p : Real) ^ 2 <= r := by exact_mod_cast hpSq
  have hpSqrt : (p : Real) <= Real.sqrt r := by
    exact (Real.le_sqrt (by positivity) (by positivity)).2 hpRealSq
  have hDfour : (4 : Real) <= D := by
    exact_mod_cast cor56_degreeScaleDenominator_four_le hk
  have hexp : 2 * (D : Real)⁻¹ + 1 / 2 <= 1 := by
    have hDpos : (0 : Real) < D :=
      lt_of_lt_of_le (by norm_num) hDfour
    have hinv : (D : Real)⁻¹ <= (4 : Real)⁻¹ := by
      exact (inv_le_inv₀ hDpos (by norm_num)).2 hDfour
    linarith
  have hprodReal : ((m * m * p : Nat) : Real) <= r := by
    push_cast
    have hmSq : (m : Real) * m <= x ^ 2 := by
      have hmNonneg : (0 : Real) <= m := by positivity
      have hxNonneg : (0 : Real) <= x := by positivity
      nlinarith
    have hxSquare : x ^ 2 =
        (r : Real) ^ (2 * (D : Real)⁻¹) := by
      dsimp only [x]
      rw [show ((r : Real) ^ (D : Real)⁻¹) ^ 2 =
          (r : Real) ^ (D : Real)⁻¹ *
            (r : Real) ^ (D : Real)⁻¹ by ring,
        ← Real.rpow_add hrPos]
      congr 1
      ring
    calc
      (m : Real) * m * p <= x ^ 2 * p :=
        mul_le_mul_of_nonneg_right hmSq (by positivity)
      _ <= x ^ 2 * Real.sqrt r :=
        mul_le_mul_of_nonneg_left hpSqrt (sq_nonneg x)
      _ = (r : Real) ^ (2 * (D : Real)⁻¹ + 1 / 2) := by
        rw [hxSquare, Real.sqrt_eq_rpow, ← Real.rpow_add hrPos]
      _ <= (r : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hrOne hexp
      _ = r := Real.rpow_one _
  have hprod : m * m * p <= r := by exact_mod_cast hprodReal
  have hpR : p <= r := by
    calc
      p <= p ^ 2 := by nlinarith
      _ <= r := hpSq
  by_cases hmm : m * m = 0
  · have hmZero : m = 0 := by nlinarith
    simp [hmZero]
  · have hmmp : a + (m * m - 1) * p < m * m * p := by
      have ha : (a : Nat) < p := a.isLt
      have hmOne : 1 <= m * m := Nat.one_le_iff_ne_zero.mpr hmm
      calc
        (a : Nat) + (m * m - 1) * p < p + (m * m - 1) * p :=
          Nat.add_lt_add_right ha _
        _ = (1 + (m * m - 1)) * p := by rw [Nat.add_mul, one_mul]
        _ = m * m * p := by rw [Nat.add_sub_of_le hmOne]
    have hpredLt : m * m - 1 < cor56ResidueClassLength r p a :=
      (cor56_quotient_lt_residueClassLength (t := m * m - 1)
        (by omega) a.isLt hpR).2 (lt_of_lt_of_le hmmp hprod)
    have hmOne : 1 <= m * m := Nat.one_le_iff_ne_zero.mpr hmm
    omega

private lemma cor56_rootFloor_target_bound {k r v ell : Nat}
    (hk : 2 <= k) (hr : weylThreshold k <= r)
    (hv : (v : Real) <=
      (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹)
    (hell : (r : Real) ^
        ((cor56DegreeScaleDenominator k : Real)⁻¹) / 2 <= ell) :
    (v : Real) <=
      (ell : Real) ^ (polynomialPartitionConstant (k - 1) : Real)⁻¹ := by
  have hrOneNat : 1 <= r := by
    have hWpos := weylThreshold_pos k
    omega
  have hrOne : (1 : Real) <= r := by exact_mod_cast hrOneNat
  have hrootTwo := cor56_global_root_two_le hk hr
  have hKprevPos : (0 : Real) < polynomialPartitionConstant (k - 1) := by
    unfold polynomialPartitionConstant
    positivity
  have hrootPos : (0 : Real) <
      (r : Real) ^ ((cor56DegreeScaleDenominator k : Real)⁻¹) := by
    positivity
  have hhalfPos : (0 : Real) <
      (r : Real) ^ ((cor56DegreeScaleDenominator k : Real)⁻¹) / 2 := by
    positivity
  have hbase :
      ((r : Real) ^ ((cor56DegreeScaleDenominator k : Real)⁻¹) / 2) ^
          (polynomialPartitionConstant (k - 1) : Real)⁻¹ =
        (r : Real) ^
            ((cor56DegreeScaleDenominator k : Real)⁻¹ *
              (polynomialPartitionConstant (k - 1) : Real)⁻¹) *
          (2 : Real) ^
            (-(polynomialPartitionConstant (k - 1) : Real)⁻¹) := by
    have htwoNeg :
        (2 : Real) ^ (-(polynomialPartitionConstant (k - 1) : Real)⁻¹) =
          ((2 : Real) ^
            (polynomialPartitionConstant (k - 1) : Real)⁻¹)⁻¹ :=
      Real.rpow_neg (x := (2 : Real)) (by norm_num)
        (polynomialPartitionConstant (k - 1) : Real)⁻¹
    rw [Real.div_rpow (by positivity) (by norm_num),
      ← Real.rpow_mul (le_trans (by norm_num : (0 : Real) <= 1) hrOne),
      div_eq_mul_inv, htwoNeg]
  have hexp :
      2 * (polynomialPartitionConstant k : Real)⁻¹ <=
        (cor56DegreeScaleDenominator k : Real)⁻¹ *
          (polynomialPartitionConstant (k - 1) : Real)⁻¹ := by
    have hgap := cor56_recursive_exponent_gap hk
    linarith
  have hpow :
      (r : Real) ^ (2 * (polynomialPartitionConstant k : Real)⁻¹) <=
        (r : Real) ^
          ((cor56DegreeScaleDenominator k : Real)⁻¹ *
            (polynomialPartitionConstant (k - 1) : Real)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hrOne hexp
  have htwoInv :
      (2 : Real)⁻¹ <=
        (2 : Real) ^
          (-(polynomialPartitionConstant (k - 1) : Real)⁻¹) := by
    have hInvLe : (polynomialPartitionConstant (k - 1) : Real)⁻¹ <= 1 := by
      have hKone : (1 : Real) <= polynomialPartitionConstant (k - 1) := by
        exact_mod_cast (show 1 <= polynomialPartitionConstant (k - 1) by
          have hpos := cor56_partitionConstant_pos (k - 1)
          omega)
      exact (inv_le_one₀ hKprevPos).2 hKone
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hmain :
      (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ <=
        ((r : Real) ^ ((cor56DegreeScaleDenominator k : Real)⁻¹) / 2) ^
          (polynomialPartitionConstant (k - 1) : Real)⁻¹ := by
    rw [hbase]
    have hrootEq :
        (r : Real) ^ (2 * (polynomialPartitionConstant k : Real)⁻¹) =
          ((r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹) ^ 2 := by
      rw [show 2 * (polynomialPartitionConstant k : Real)⁻¹ =
        (polynomialPartitionConstant k : Real)⁻¹ +
          (polynomialPartitionConstant k : Real)⁻¹ by ring,
        Real.rpow_add (lt_of_lt_of_le (by norm_num) hrOne)]
      ring
    have hrootOne : (1 : Real) <=
        (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ := by
      exact Real.one_le_rpow hrOne (by positivity)
    calc
      (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ <=
          (r : Real) ^ (2 * (polynomialPartitionConstant k : Real)⁻¹) / 2 := by
        rw [hrootEq]
        nlinarith
      _ <= (r : Real) ^
            ((cor56DegreeScaleDenominator k : Real)⁻¹ *
              (polynomialPartitionConstant (k - 1) : Real)⁻¹) / 2 := by
        gcongr
      _ <= (r : Real) ^
            ((cor56DegreeScaleDenominator k : Real)⁻¹ *
              (polynomialPartitionConstant (k - 1) : Real)⁻¹) *
            (2 : Real) ^
              (-(polynomialPartitionConstant (k - 1) : Real)⁻¹) := by
        change _ * (2 : Real)⁻¹ <= _
        gcongr
  exact hv.trans <| hmain.trans <|
    Real.rpow_le_rpow (le_of_lt hhalfPos) hell (by positivity)

private lemma cor56_leading_error_scale {k r N ell : Nat} (hk : 2 <= k)
    (hr : weylThreshold k <= r)
    (hell : (ell : Real) <= 2 *
      (r : Real) ^ ((cor56DegreeScaleDenominator k : Real)⁻¹))
    {top : ZMod N}
    (htop : (centeredAbs top : Real) <=
      (r : Real) ^
        (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N) :
    ((ell ^ k * centeredAbs top : Nat) : Real) <=
      (1 / 4 : Real) *
        ((r : Real) ^
          (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) := by
  have hrOneNat : 1 <= r := by
    have hWpos := weylThreshold_pos k
    omega
  have hrOne : (1 : Real) <= r := by exact_mod_cast hrOneNat
  have hrPos : (0 : Real) < r := by positivity
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  let K : Real := polynomialPartitionConstant k
  let D : Real := cor56DegreeScaleDenominator k
  have hDpos : 0 < D := by
    dsimp only [D]
    exact_mod_cast cor56_degreeScaleDenominator_pos (by omega : 1 <= k)
  have hkD : (k : Real) * D⁻¹ = gamma / 2 := by
    dsimp only [D, gamma, cor56DegreeScaleDenominator]
    push_cast
    have hkpos : (0 : Real) < k := by positivity
    have hpow : (2 : Real) ^ (k + 2) =
        2 * (2 : Real) ^ (k + 1) := by rw [pow_succ]; ring
    rw [hpow]
    field_simp [ne_of_gt hkpos]
  have hgap : K⁻¹ <= gamma / 2 - 2 * K⁻¹ := by
    have hgamma := cor56_gamma_half_ge_three_over_K hk
    change 3 * K⁻¹ <= (1 / 2 : Real) * gamma at hgamma
    linarith
  have habsorb : (4 : Real) * 2 ^ k <=
      (r : Real) ^ (gamma / 2 - 2 * K⁻¹) := by
    calc
      (4 : Real) * 2 ^ k <= (r : Real) ^ K⁻¹ := by
        simpa only [K] using cor56_global_root_absorbs_constant hk hr
      _ <= (r : Real) ^ (gamma / 2 - 2 * K⁻¹) :=
        Real.rpow_le_rpow_of_exponent_le hrOne hgap
  have hellPow : (ell : Real) ^ k <=
      (2 : Real) ^ k * (r : Real) ^ (gamma / 2) := by
    calc
      (ell : Real) ^ k <=
          (2 * (r : Real) ^ (D⁻¹)) ^ k := by
        exact pow_le_pow_left₀ (by positivity) hell k
      _ = (2 : Real) ^ k *
          ((r : Real) ^ D⁻¹) ^ k := by rw [mul_pow]
      _ = (2 : Real) ^ k * (r : Real) ^ (gamma / 2) := by
        have hinner : ((r : Real) ^ D⁻¹) ^ k =
            (r : Real) ^ (gamma / 2) := by
          calc
            ((r : Real) ^ D⁻¹) ^ k =
                ((r : Real) ^ D⁻¹) ^ (k : Real) :=
              (Real.rpow_natCast _ k).symm
            _ = (r : Real) ^ (D⁻¹ * k) :=
              (Real.rpow_mul (le_of_lt hrPos) D⁻¹ k).symm
            _ = (r : Real) ^ (gamma / 2) := by
              rw [show D⁻¹ * (k : Real) = (k : Real) * D⁻¹ by ring, hkD]
        rw [hinner]
  have hraw : ((ell ^ k * centeredAbs top : Nat) : Real) <=
      (2 : Real) ^ k * (r : Real) ^ (-gamma / 2) * N := by
    push_cast
    calc
      (ell : Real) ^ k * centeredAbs top <=
          ((2 : Real) ^ k * (r : Real) ^ (gamma / 2)) *
            ((r : Real) ^ (-gamma) * N) := by
        exact mul_le_mul hellPow (by simpa only [gamma] using htop)
          (by positivity) (by positivity)
      _ = (2 : Real) ^ k * (r : Real) ^ (-gamma / 2) * N := by
        have hpowAdd :
            (r : Real) ^ (gamma / 2) * (r : Real) ^ (-gamma) =
              (r : Real) ^ (gamma / 2 + -gamma) :=
          (Real.rpow_add hrPos (gamma / 2) (-gamma)).symm
        calc
          (2 : Real) ^ k * (r : Real) ^ (gamma / 2) *
                ((r : Real) ^ (-gamma) * N) =
              (2 : Real) ^ k *
                ((r : Real) ^ (gamma / 2) * (r : Real) ^ (-gamma)) * N := by
            ring
          _ = (2 : Real) ^ k *
                (r : Real) ^ (gamma / 2 + -gamma) * N := by rw [hpowAdd]
          _ = (2 : Real) ^ k * (r : Real) ^ (-gamma / 2) * N := by
            congr 2
            ring
  calc
    ((ell ^ k * centeredAbs top : Nat) : Real) <=
        (2 : Real) ^ k * (r : Real) ^ (-gamma / 2) * N := hraw
    _ <= (1 / 4 : Real) *
        ((r : Real) ^ (-(2 * K⁻¹)) * N) := by
      have hmul := mul_le_mul_of_nonneg_right habsorb
        (show 0 <= (r : Real) ^ (-gamma / 2) * N by positivity)
      have hid :
          (gamma / 2 - 2 * K⁻¹) + (-gamma / 2) = -(2 * K⁻¹) := by ring
      have hpowAdd :
          (r : Real) ^ (gamma / 2 - 2 * K⁻¹) *
              (r : Real) ^ (-gamma / 2) =
            (r : Real) ^ ((gamma / 2 - 2 * K⁻¹) + (-gamma / 2)) :=
        (Real.rpow_add hrPos (gamma / 2 - 2 * K⁻¹) (-gamma / 2)).symm
      have hmul' :
          (4 : Real) * 2 ^ k * (r : Real) ^ (-gamma / 2) * N <=
            (r : Real) ^ (-(2 * K⁻¹)) * N := by
        calc
          (4 : Real) * 2 ^ k * (r : Real) ^ (-gamma / 2) * N =
              ((4 : Real) * 2 ^ k) *
                ((r : Real) ^ (-gamma / 2) * N) := by ring
          _ <= (r : Real) ^ (gamma / 2 - 2 * K⁻¹) *
                ((r : Real) ^ (-gamma / 2) * N) := hmul
          _ = ((r : Real) ^ (gamma / 2 - 2 * K⁻¹) *
                (r : Real) ^ (-gamma / 2)) * N := by ring
          _ = (r : Real) ^ (-(2 * K⁻¹)) * N := by rw [hpowAdd, hid]
      nlinarith [hmul']

private lemma cor56_recursive_radius_scale {k r ell N : Nat} (hk : 2 <= k)
    (hr : weylThreshold k <= r)
    (hell : (r : Real) ^
        ((cor56DegreeScaleDenominator k : Real)⁻¹) / 2 <= ell) :
    (1 / 2 : Real) *
        ((ell : Real) ^
          (-(2 * (polynomialPartitionConstant (k - 1) : Real)⁻¹)) * N) <=
      (1 / 4 : Real) *
        ((r : Real) ^
          (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) := by
  have hrOneNat : 1 <= r := by
    have hWpos := weylThreshold_pos k
    omega
  have hrOne : (1 : Real) <= r := by exact_mod_cast hrOneNat
  have hrPos : (0 : Real) < r := by positivity
  let D : Real := cor56DegreeScaleDenominator k
  let a : Real := 2 * (polynomialPartitionConstant (k - 1) : Real)⁻¹
  let b : Real := 2 * (polynomialPartitionConstant k : Real)⁻¹
  have haNonneg : 0 <= a := by dsimp only [a]; positivity
  have haOne : a <= 1 := by
    have hKprev : (1 : Real) <= polynomialPartitionConstant (k - 1) := by
      exact_mod_cast (show 1 <= polynomialPartitionConstant (k - 1) by
        have hpos := cor56_partitionConstant_pos (k - 1)
        omega)
    have hKprevTwoNat : 2 <= polynomialPartitionConstant (k - 1) := by
      unfold polynomialPartitionConstant
      have hexp : 1 <= (k - 1 + 1) ^ 2 := by
        have : 1 <= k - 1 := by omega
        nlinarith
      have hp : 2 <= 2 ^ ((k - 1 + 1) ^ 2) := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ <= 2 ^ ((k - 1 + 1) ^ 2) :=
            Nat.pow_le_pow_right (by norm_num) hexp
      have hfacPos : 0 < (k - 1).factorial ^ 2 :=
        pow_pos (Nat.factorial_pos (k - 1)) 2
      have hfac : 1 <= (k - 1).factorial ^ 2 := by omega
      nlinarith
    have hKprevTwo : (2 : Real) <= polynomialPartitionConstant (k - 1) := by
      exact_mod_cast hKprevTwoNat
    have hInvHalf' :
        (polynomialPartitionConstant (k - 1) : Real)⁻¹ <= (2 : Real)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by norm_num)).2 hKprevTwo
    have hInvHalf :
        (polynomialPartitionConstant (k - 1) : Real)⁻¹ <= 1 / 2 := by
      simpa only [one_div] using hInvHalf'
    dsimp only [a]
    linarith
  have hhalfPos : (0 : Real) <
      (r : Real) ^ (D⁻¹) / 2 := by positivity
  have hellPos : (0 : Real) < ell := lt_of_lt_of_le hhalfPos hell
  have hmono :
      (ell : Real) ^ (-a) <=
        ((r : Real) ^ D⁻¹ / 2) ^ (-a) := by
    exact Real.rpow_le_rpow_of_nonpos hhalfPos hell (by linarith)
  have htwoPow : (2 : Real) ^ a <= 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num) haOne
  have hrewrite :
      ((r : Real) ^ D⁻¹ / 2) ^ (-a) =
        (r : Real) ^ (-(a * D⁻¹)) * (2 : Real) ^ a := by
    have htwoNeg : (2 : Real) ^ (-a) = ((2 : Real) ^ a)⁻¹ :=
      Real.rpow_neg (x := (2 : Real)) (by norm_num) a
    rw [Real.div_rpow (by positivity) (by norm_num),
      ← Real.rpow_mul (le_trans (by norm_num : (0 : Real) <= 1) hrOne)]
    rw [show D⁻¹ * (-a) = -(a * D⁻¹) by ring]
    rw [htwoNeg, div_inv_eq_mul]
  have hraw : (1 / 2 : Real) * (ell : Real) ^ (-a) <=
      (r : Real) ^ (-(a * D⁻¹)) := by
    calc
      (1 / 2 : Real) * (ell : Real) ^ (-a) <=
          (1 / 2 : Real) *
            ((r : Real) ^ D⁻¹ / 2) ^ (-a) := by gcongr
      _ = (1 / 2 : Real) *
          ((r : Real) ^ (-(a * D⁻¹)) * (2 : Real) ^ a) := by rw [hrewrite]
      _ <= (r : Real) ^ (-(a * D⁻¹)) := by
        nlinarith [Real.rpow_pos_of_pos hrPos (-(a * D⁻¹))]
  have hgap : 2 * b <= a * D⁻¹ := by
    dsimp only [a, b, D]
    convert cor56_recursive_exponent_gap hk using 1 <;> ring
  have hpowGap :
      (r : Real) ^ (-(a * D⁻¹)) <= (r : Real) ^ (-(2 * b)) :=
    Real.rpow_le_rpow_of_exponent_le hrOne (by linarith)
  have hrootTwo := cor56_global_root_two_le hk hr
  have hfour : (4 : Real) <= (r : Real) ^ b := by
    have hsquare := pow_le_pow_left₀ (by norm_num : (0 : Real) <= 2)
      hrootTwo 2
    have hpow :
        ((r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹) ^ 2 =
          (r : Real) ^ b := by
      dsimp only [b]
      rw [show 2 * (polynomialPartitionConstant k : Real)⁻¹ =
        (polynomialPartitionConstant k : Real)⁻¹ +
          (polynomialPartitionConstant k : Real)⁻¹ by ring,
        Real.rpow_add hrPos]
      ring
    rw [hpow] at hsquare
    norm_num at hsquare
    exact hsquare
  have habsorb :
      (r : Real) ^ (-(2 * b)) <=
        (1 / 4 : Real) * (r : Real) ^ (-b) := by
    have hmul := mul_le_mul_of_nonneg_right hfour
      (show 0 <= (r : Real) ^ (-(2 * b)) by positivity)
    have hid : b + -(2 * b) = -b := by ring
    have hpowAdd :
        (r : Real) ^ b * (r : Real) ^ (-(2 * b)) =
          (r : Real) ^ (b + -(2 * b)) :=
      (Real.rpow_add hrPos b (-(2 * b))).symm
    rw [hpowAdd, hid] at hmul
    nlinarith
  have hcoefficient :
      (1 / 2 : Real) * (ell : Real) ^ (-a) <=
        (1 / 4 : Real) * (r : Real) ^ (-b) :=
    hraw.trans (hpowGap.trans habsorb)
  have hNnonneg : (0 : Real) <= N := by positivity
  have := mul_le_mul_of_nonneg_right hcoefficient hNnonneg
  simpa only [a, b, mul_assoc] using this

/-! ## The strengthened induction statement -/

private def cor56StrongCenteredAtDegree (k : Nat) : Prop :=
  forall (N r v : Nat) [NeZero N] (phi : ZMod N -> ZMod N),
    PolynomialOn k Finset.univ phi ->
    polynomialPartitionThreshold k < r -> r <= N ->
    1 <= v -> (v : Real) <=
      (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ ->
    exists M : Nat, exists P : Fin M -> NatAP,
      0 < M /\ IsNatAPPartition P (Finset.range r) /\
      (forall j, (P j).IsProper /\ 0 < (P j).length /\
        ((P j).length = v - 1 \/ (P j).length = v)) /\
      forall j, cor56CenteredRadiusAtMostReal
        ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
        ((1 / 2 : Real) *
          ((r : Real) ^
            (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N))

private lemma cor56_polynomialOn_one_is_linear {N r : Nat} [NeZero N]
    (phi : ZMod N -> ZMod N) (hphi : PolynomialOn 1 Finset.univ phi) :
    NatToZModLinear r (fun x : Nat => phi (x : ZMod N)) := by
  obtain ⟨c, hc⟩ := hphi
  refine ⟨c 1, c 0, ?_⟩
  intro x _hx
  change phi (x : ZMod N) = c 1 * (x : ZMod N) + c 0
  rw [hc (x : ZMod N) (Finset.mem_univ _)]
  simpa [Fin.sum_univ_two, add_comm]

private lemma cor56_threshold_one_ge_4096 :
    4096 <= polynomialPartitionThreshold 1 := by
  calc
    4096 = 2 ^ 12 := by norm_num
    _ <= 2 ^ (2 ^ (40 * 1 ^ 3)) := by
      apply Nat.pow_le_pow_right (by norm_num)
      calc
        12 <= 2 ^ 4 := by norm_num
        _ <= 2 ^ (40 * 1 ^ 3) := by
          apply Nat.pow_le_pow_right (by norm_num)
          norm_num
    _ = weylThreshold 1 := by rfl
    _ <= polynomialPartitionThreshold 1 :=
      weylThreshold_le_polynomialPartitionThreshold 1

private lemma cor56_linear_quantitative_bounds {N r v : Nat} [NeZero N]
    (hrT : polynomialPartitionThreshold 1 < r) (hrN : r <= N)
    (hv : 2 <= v)
    (hvupper : (v : Real) <=
      (r : Real) ^ (polynomialPartitionConstant 1 : Real)⁻¹) :
    let target : Real := (r : Real) ^ (-(1 / 8 : Real)) * N
    let X : Real := 16 * (N : Real) * (v : Real) ^ 4 / r
    let s : Nat := Nat.ceil X
    0 < s /\ s <= N /\ N <= r * s /\
      (s : Real) <= target / 2 /\
      (v : Real) ^ 4 <= (r : Real) * s / (16 * N) := by
  let target : Real := (r : Real) ^ (-(1 / 8 : Real)) * N
  let X : Real := 16 * (N : Real) * (v : Real) ^ 4 / r
  let s : Nat := Nat.ceil X
  have hr4096 : 4096 <= r := (cor56_threshold_one_ge_4096.trans_lt hrT).le
  have hrPosNat : 0 < r := by omega
  have hrOne : (1 : Real) <= r := by exact_mod_cast (show 1 <= r by omega)
  have hrPos : (0 : Real) < r := by exact_mod_cast hrPosNat
  have hNPos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hvPos : (0 : Real) < v := by exact_mod_cast (show 0 < v by omega)
  have hKone : polynomialPartitionConstant 1 = 16 := by
    norm_num [polynomialPartitionConstant]
  have hvroot : (v : Real) <= (r : Real) ^ (1 / 16 : Real) := by
    norm_num [hKone] at hvupper ⊢
    exact hvupper
  have hvfour : (v : Real) ^ 4 <= (r : Real) ^ (1 / 4 : Real) := by
    calc
      (v : Real) ^ 4 <= ((r : Real) ^ (1 / 16 : Real)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hvroot 4
      _ = (r : Real) ^ (1 / 4 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hrPos)]
        norm_num
  have hsqrt64 : (64 : Real) <= (r : Real) ^ (1 / 2 : Real) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact hr4096
  have h64 : (64 : Real) <= (r : Real) ^ (5 / 8 : Real) := by
    exact hsqrt64.trans <|
      Real.rpow_le_rpow_of_exponent_le hrOne (by norm_num : (1 / 2 : Real) <= 5 / 8)
  have hsixtyfour : (64 : Real) * v ^ 4 <=
      (r : Real) ^ (7 / 8 : Real) := by
    calc
      (64 : Real) * v ^ 4 <=
          (r : Real) ^ (5 / 8 : Real) *
            (r : Real) ^ (1 / 4 : Real) := mul_le_mul h64 hvfour (by positivity) (by positivity)
      _ = (r : Real) ^ (7 / 8 : Real) := by
        rw [← Real.rpow_add hrPos]
        norm_num
  have hXPos : 0 < X := by dsimp only [X]; positivity
  have htargetPos : 0 < target := by dsimp only [target]; positivity
  have hXquarter : X <= target / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hsixtyfour
      (show 0 <= (N : Real) / (4 * r) by positivity)
    have hpow :
        (r : Real) ^ (7 / 8 : Real) / r =
          (r : Real) ^ (-(1 / 8 : Real)) := by
      calc
        (r : Real) ^ (7 / 8 : Real) / r =
            (r : Real) ^ (7 / 8 : Real) / (r : Real) ^ (1 : Real) := by
          rw [Real.rpow_one]
        _ = (r : Real) ^ ((7 / 8 : Real) - 1) :=
          (Real.rpow_sub hrPos (7 / 8 : Real) 1).symm
        _ = (r : Real) ^ (-(1 / 8 : Real)) := by
          congr 1
          ring
    calc
      X = (64 * (v : Real) ^ 4) * (N / (4 * r)) := by
        dsimp only [X]
        field_simp [ne_of_gt hrPos]
        ring
      _ <= (r : Real) ^ (7 / 8 : Real) * (N / (4 * r)) := hmul
      _ = ((r : Real) ^ (7 / 8 : Real) / r) * N / 4 := by
        field_simp [ne_of_gt hrPos]
      _ = target / 4 := by rw [hpow]
  have htargetFour : (4 : Real) <= target := by
    have hrNReal : (r : Real) <= N := by exact_mod_cast hrN
    have hpowFour : (4 : Real) <= (r : Real) ^ (7 / 8 : Real) := by
      calc
        (4 : Real) <= 64 := by norm_num
        _ <= (r : Real) ^ (5 / 8 : Real) := h64
        _ <= (r : Real) ^ (7 / 8 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hrOne (by norm_num)
    calc
      (4 : Real) <= (r : Real) ^ (7 / 8 : Real) := hpowFour
      _ = (r : Real) ^ (-(1 / 8 : Real)) * r := by
        calc
          (r : Real) ^ (7 / 8 : Real) =
              (r : Real) ^ (-(1 / 8 : Real) + 1) := by
            congr 1
            ring
          _ = (r : Real) ^ (-(1 / 8 : Real)) *
              (r : Real) ^ (1 : Real) :=
            Real.rpow_add hrPos (-(1 / 8 : Real)) 1
          _ = (r : Real) ^ (-(1 / 8 : Real)) * r := by
            rw [Real.rpow_one]
      _ <= (r : Real) ^ (-(1 / 8 : Real)) * N := by gcongr
      _ = target := rfl
  have hsPos : 0 < s := Nat.ceil_pos.mpr hXPos
  have hXs : X <= s := by simpa only [s] using Nat.le_ceil X
  have hsLt : (s : Real) < X + 1 := by
    simpa only [s] using Nat.ceil_lt_add_one (le_of_lt hXPos)
  have hsTargetHalf : (s : Real) <= target / 2 := by
    calc
      (s : Real) <= X + 1 := le_of_lt hsLt
      _ <= target / 4 + 1 := by linarith only [hXquarter]
      _ <= target / 2 := by linarith only [htargetFour]
  have htargetN : target <= N := by
    dsimp only [target]
    have hpow : (r : Real) ^ (-(1 / 8 : Real)) <= 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hrOne (by norm_num)
    calc
      (r : Real) ^ (-(1 / 8 : Real)) * N <= 1 * N :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = N := one_mul _
  have hsNReal : (s : Real) <= N :=
    hsTargetHalf.trans <|
      (div_le_self (le_of_lt htargetPos) (by norm_num)).trans htargetN
  have hsN : s <= N := by exact_mod_cast hsNReal
  have hrsReal : (N : Real) <= r * s := by
    calc
      (N : Real) <= 16 * N * v ^ 4 := by
        have hvOneReal : (1 : Real) <= v := by exact_mod_cast (show 1 <= v by omega)
        have hvPow : (1 : Real) <= v ^ 4 := one_le_pow₀ hvOneReal
        have hscale : (v : Real) ^ 4 <= 16 * v ^ 4 := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right (by norm_num : (1 : Real) <= 16)
              (le_trans (by norm_num : (0 : Real) <= 1) hvPow))
        have hfactor : (1 : Real) <= 16 * v ^ 4 := by
          exact hvPow.trans hscale
        calc
          (N : Real) = N * 1 := by ring
          _ <= N * (16 * v ^ 4) :=
            mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg N)
          _ = 16 * N * v ^ 4 := by ring
      _ = (r : Real) * X := by
        dsimp only [X]
        field_simp [ne_of_gt hrPos]
        <;> ring
      _ <= (r : Real) * s :=
        mul_le_mul_of_nonneg_left hXs (le_of_lt hrPos)
  have hrs : N <= r * s := by exact_mod_cast hrsReal
  have hvRad : (v : Real) ^ 4 <= (r : Real) * s / (16 * N) := by
    have hmul := mul_le_mul_of_nonneg_left hXs (le_of_lt hrPos)
    have hleft : (r : Real) * X = 16 * N * v ^ 4 := by
      dsimp only [X]
      field_simp [ne_of_gt hrPos]
      <;> ring
    rw [hleft] at hmul
    apply (le_div_iff₀ (by positivity : (0 : Real) < 16 * N)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  exact ⟨hsPos, hsN, hrs, hsTargetHalf, hvRad⟩

private theorem cor56_strong_centered_degree_one :
    cor56StrongCenteredAtDegree 1 := by
  intro N r v _ phi hphi hrT hrN hv hvupper
  classical
  by_cases hvOne : v = 1
  · subst v
    have hrPos : 0 < r := by
      have hTpos := polynomialPartitionThreshold_positive 1
      omega
    refine ⟨r, fun i : Fin r => cor56SingletonNatAP i, hrPos,
      cor56SingletonNatAP_partition r, ?_, ?_⟩
    · intro j
      exact ⟨cor56SingletonNatAP_isProper j, by simp [cor56SingletonNatAP],
        Or.inr (by simp [cor56SingletonNatAP])⟩
    · intro j
      apply cor56_singleton_centeredRadius
      positivity
  · have hvTwo : 2 <= v := by omega
    let target : Real := (r : Real) ^ (-(1 / 8 : Real)) * N
    let X : Real := 16 * (N : Real) * (v : Real) ^ 4 / r
    let s : Nat := Nat.ceil X
    obtain ⟨hsPos, hsN, hrs, hsTarget, hvRad⟩ :=
      cor56_linear_quantitative_bounds hrT hrN hvTwo hvupper
    have hrPos : 0 < r := by omega
    have hlinear : NatToZModLinear r (fun x : Nat => phi (x : ZMod N)) :=
      cor56_polynomialOn_one_is_linear phi hphi
    obtain ⟨M, P, hPpartition, hPcells⟩ :=
      lemma_2_3_holds N r s (NeZero.pos N) hrPos hsPos hrN hsN hrs
        (fun x : Nat => phi (x : ZMod N)) hlinear
    let m : Nat := v - 1
    have hmPos : 0 < m := by dsimp only [m]; omega
    have hParentLengthPos (i : Fin M) : 0 < (P i).length := by
      have hinside : (0 : Real) < (r : Real) * s / (16 * N) := by
        have hrPosReal : (0 : Real) < r := by exact_mod_cast hrPos
        have hsPosNat : 0 < s := by simpa only [s] using hsPos
        have hsPosReal : (0 : Real) < s := by exact_mod_cast hsPosNat
        have hNPosReal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
        exact div_pos (mul_pos hrPosReal hsPosReal)
          (mul_pos (by norm_num) hNPosReal)
      have hsqrtPos : (0 : Real) <
          Real.sqrt ((r : Real) * s / (16 * N)) := Real.sqrt_pos.2 hinside
      have hlengthReal : (0 : Real) < (P i).length :=
        lt_of_lt_of_le hsqrtPos (hPcells i).2.2.1
      exact_mod_cast hlengthReal
    have hclass (i : Fin M) (a : Fin 1) :
        m * m <= cor56ResidueClassLength (P i).length 1 a := by
      have hvSq : (v : Real) ^ 2 <=
          Real.sqrt ((r : Real) * s / (16 * N)) := by
        apply Real.le_sqrt_of_sq_le
        have hvPow : ((v : Real) ^ 2) ^ 2 = (v : Real) ^ 4 := by ring
        rw [hvPow]
        exact hvRad
      have hvLength : (v : Real) ^ 2 <= (P i).length :=
        hvSq.trans (hPcells i).2.2.1
      have hmSq : m * m <= (P i).length := by
        have hmle : m <= v := by dsimp only [m]; omega
        have hmSqNat : m * m <= v * v := Nat.mul_le_mul hmle hmle
        have hmSqReal : ((m * m : Nat) : Real) <= ((v * v : Nat) : Real) := by
          exact_mod_cast hmSqNat
        exact_mod_cast (calc
          ((m * m : Nat) : Real) <= ((v * v : Nat) : Real) := hmSqReal
          _ = (v : Real) ^ 2 := by push_cast; ring
          _ <= (P i).length := hvLength)
      have haZero : (a : Nat) = 0 := by
        exact congrArg Fin.val (Fin.eq_zero a)
      have hlenOne : 1 <= (P i).length := hParentLengthPos i
      rw [cor56ResidueClassLength, haZero, Nat.sub_zero, Nat.div_one,
        Nat.sub_add_cancel hlenOne]
      exact hmSq
    let L : Fin M -> Nat := fun i =>
      Fintype.card (Cor56BalancedResidueChunkIndex (P i).length 1 m)
    let R : (i : Fin M) -> Fin (L i) -> NatAP := fun i j =>
      cor56BalancedResidueChunkFamily (P i).length 1 m j
    let Q : (i : Fin M) -> Fin (L i) -> NatAP := fun i j =>
      section5NatTransport (P i) (R i j)
    have hL (i : Fin M) : 0 < L i := by
      dsimp only [L]
      exact cor56BalancedResidueChunkFamily_nonempty _ 1 m
        (by norm_num) hmPos (hclass i)
    have hRpartition (i : Fin M) :
        IsNatAPPartition (R i) (Finset.range (P i).length) := by
      dsimp only [R]
      exact cor56BalancedResidueChunkFamily_partition _ 1 m
        (by norm_num) (hParentLengthPos i) hmPos (hclass i)
    have hRcells (i : Fin M) (j : Fin (L i)) :
        (R i j).IsProper /\
          ((R i j).length = v - 1 \/ (R i j).length = v) := by
      have hprop := cor56BalancedResidueChunkFamily_properties
        (P i).length 1 m (by norm_num) j
      rcases hprop.2 with hlen | hlen
      · exact ⟨hprop.1, Or.inl (by simpa only [m] using hlen)⟩
      · exact ⟨hprop.1, Or.inr (by simpa only [m, Nat.sub_add_cancel (by omega : 1 <= v)] using hlen)⟩
    have hQpartition (i : Fin M) : IsNatAPPartition (Q i) (P i).carrier := by
      dsimp only [Q]
      exact section5NatTransport_partition (P i) (R i) (hPcells i).1
        (hRpartition i)
    have hQcells (i : Fin M) (j : Fin (L i)) :
        (Q i j).IsProper /\ 0 < (Q i j).length /\
          ((Q i j).length = v - 1 \/ (Q i j).length = v) := by
      have hproper := section5NatTransport_isProper (P i) (R i j)
        (hPcells i).1 (hRcells i j).1
      have hlen := (hRcells i j).2
      refine ⟨hproper, ?_, ?_⟩
      · rw [section5NatTransport_length]
        rcases hlen with hlen | hlen <;> omega
      · simpa only [Q, section5NatTransport_length] using hlen
    have hQradius (i : Fin M) (j : Fin (L i)) :
        cor56CenteredRadiusAtMostReal
          ((Q i j).carrier.image fun x : Nat => phi (x : ZMod N))
          ((1 / 2 : Real) *
            ((r : Real) ^
              (-(2 * (polynomialPartitionConstant 1 : Real)⁻¹)) * N)) := by
      have hsubsetR : (R i j).carrier ⊆ Finset.range (P i).length :=
        IsPartition.cell_subset (hRpartition i) j
      have hsubsetQ : (Q i j).carrier ⊆ (P i).carrier := by
        dsimp only [Q]
        exact section5NatTransport_subset (P i) (R i j) hsubsetR
      have hparent : cor56CenteredRadiusAtMostReal
          ((P i).carrier.image fun x : Nat => phi (x : ZMod N)) s :=
        cor56_diameter_to_centeredRadius (hPcells i).2.1
      apply cor56_centeredRadius_mono
        (Finset.image_mono _ hsubsetQ) hparent
      have hKone : polynomialPartitionConstant 1 = 16 := by
        norm_num [polynomialPartitionConstant]
      have hscale :
          (1 / 2 : Real) *
              ((r : Real) ^
                (-(2 * (polynomialPartitionConstant 1 : Real)⁻¹)) * N) =
            target / 2 := by
        rw [hKone]
        dsimp only [target]
        norm_num
        ring
      rw [hscale]
      exact hsTarget
    let F : Fin (∑ i, L i) -> NatAP := section5NatFlatten L Q
    have hFpartition : IsNatAPPartition F (Finset.range r) :=
      section5NatFlatten_partition P (Finset.range r) L Q hPpartition hQpartition
    have hFproper : forall j, (F j).IsProper :=
      section5NatFlatten_isProper L Q (fun i j => (hQcells i j).1)
    have hsumPos : 0 < ∑ i, L i := by
      have hMPos : 0 < M := by
        by_contra hMZero
        have hMzero : M = 0 := Nat.eq_zero_of_not_pos hMZero
        have hx := (hPpartition.1 0).mp (Finset.mem_range.mpr hrPos)
        obtain ⟨i, _hi⟩ := hx
        have hi : (i : Nat) < 0 := by simpa only [hMzero] using i.isLt
        omega
      let i : Fin M := ⟨0, hMPos⟩
      exact lt_of_lt_of_le (hL i)
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    refine ⟨∑ i, L i, F, hsumPos, hFpartition, ?_, ?_⟩
    · intro j
      let z := (section5NatFlattenEquiv L).symm j
      simpa only [F, section5NatFlatten, z] using hQcells z.1 z.2
    · intro j
      let z := (section5NatFlattenEquiv L).symm j
      simpa only [F, section5NatFlatten, z] using hQradius z.1 z.2

private theorem cor56_strong_centered_step {k : Nat} (hk : 2 <= k)
    (ih : cor56StrongCenteredAtDegree (k - 1)) :
    cor56StrongCenteredAtDegree k := by
  intro N r v _ phi hphi hrT hrN hv hvupper
  classical
  obtain ⟨c, hc⟩ := hphi
  have hcAll : forall x, phi x = ∑ i, c i * x ^ (i : Nat) :=
    fun x => hc x (Finset.mem_univ x)
  let lead : ZMod N := c (Fin.last k)
  have hrW : weylThreshold k <= r :=
    (weylThreshold_le_polynomialPartitionThreshold k).trans
      (Nat.le_of_lt hrT)
  have hrSq : weylThreshold k ^ 2 <= r := by
    simpa only [polynomialPartitionThreshold] using Nat.le_of_lt hrT
  obtain ⟨p, hp, hpSq, hlead⟩ :=
    lemma_5_5_square_root_auxiliary_holds k r N hk hrSq hrN lead
  let D : Nat := cor56DegreeScaleDenominator k
  let x : Real := (r : Real) ^ ((D : Real)⁻¹)
  let m : Nat := Nat.floor x
  obtain ⟨hmPos, hprevT, hxHalf, hmle, hmSuccReal, hmSuccR⟩ :=
    cor56_root_floor_bounds hk hrW
  have hpR : p <= r := by
    calc
      p <= p ^ 2 := by nlinarith
      _ <= r := hpSq
  have hclass : forall a : Fin p,
      m * m <= cor56ResidueClassLength r p a := by
    simpa only [x, m, D] using
      cor56_rootFloor_residue_classes_large hk hrW hp hpSq
  let M₀ : Nat := Fintype.card (Cor56BalancedResidueChunkIndex r p m)
  let P : Fin M₀ -> NatAP := cor56BalancedResidueChunkFamily r p m
  have hM₀ : 0 < M₀ := by
    dsimp only [M₀]
    exact cor56BalancedResidueChunkFamily_nonempty r p m (by omega) hmPos hclass
  have hPpartition : IsNatAPPartition P (Finset.range r) := by
    dsimp only [P]
    exact cor56BalancedResidueChunkFamily_partition r p m
      (by omega) hpR hmPos hclass
  have hPcells (i : Fin M₀) :
      (P i).IsProper /\ ((P i).length = m \/ (P i).length = m + 1) := by
    dsimp only [P]
    exact cor56BalancedResidueChunkFamily_properties r p m (by omega) i
  have hPlower (i : Fin M₀) : x / 2 <= (P i).length := by
    have hmP : m <= (P i).length := by
      rcases (hPcells i).2 with h | h <;> omega
    have hmPReal : (m : Real) <= (P i).length := by exact_mod_cast hmP
    exact le_trans hxHalf hmPReal
  have hPupper (i : Fin M₀) : ((P i).length : Real) <= 2 * x := by
    have hPm : (P i).length <= m + 1 := by
      rcases (hPcells i).2 with h | h <;> omega
    have hPmReal : ((P i).length : Real) <= m + 1 := by exact_mod_cast hPm
    have hmSuccReal' : (m : Real) + 1 <= 2 * x := by
      simpa only [m, x, D, Nat.cast_add, Nat.cast_one] using hmSuccReal
    exact le_trans hPmReal hmSuccReal'
  have hPthreshold (i : Fin M₀) :
      polynomialPartitionThreshold (k - 1) < (P i).length := by
    have hmP : m <= (P i).length := by
      rcases (hPcells i).2 with h | h <;> omega
    exact lt_of_lt_of_le hprevT hmP
  have hPN (i : Fin M₀) : (P i).length <= N := by
    have hPm : (P i).length <= m + 1 := by
      rcases (hPcells i).2 with h | h <;> omega
    exact hPm.trans (hmSuccR.trans hrN)
  have hPpos (i : Fin M₀) : 0 < (P i).length := by
    have hmP : m <= (P i).length := by
      rcases (hPcells i).2 with h | h <;> omega
    exact lt_of_lt_of_le hmPos hmP
  let top : ZMod N := ((p : ZMod N) ^ k) * lead
  have htop : (centeredAbs top : Real) <=
      (r : Real) ^
        (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N := by
    simpa only [top, mul_comm] using hlead
  let psi (i : Fin M₀) : ZMod N -> ZMod N := fun z =>
    phi ((P i).start + z * (P i).step) - top * z ^ k
  have hPstep (i : Fin M₀) : (P i).step = p := rfl
  have hpsi (i : Fin M₀) :
      PolynomialOn (k - 1) Finset.univ (psi i) := by
    have h := cor56_polynomialOn_affine_sub_top (N := N)
      (by omega : 1 <= k) phi c hcAll
      ((P i).start : ZMod N) ((P i).step : ZMod N)
    simpa only [psi, top, lead, hPstep, mul_comm] using h
  have hvLocal (i : Fin M₀) :
      (v : Real) <= ((P i).length : Real) ^
        (polynomialPartitionConstant (k - 1) : Real)⁻¹ := by
    exact cor56_rootFloor_target_bound hk hrW hvupper (hPlower i)
  choose L R hL hRpartition hRcells hRradius using
    fun i : Fin M₀ =>
      ih N (P i).length v (psi i) (hpsi i) (hPthreshold i) (hPN i)
        hv (hvLocal i)
  let Q : (i : Fin M₀) -> Fin (L i) -> NatAP := fun i j =>
    section5NatTransport (P i) (R i j)
  have hQpartition (i : Fin M₀) : IsNatAPPartition (Q i) (P i).carrier := by
    dsimp only [Q]
    exact section5NatTransport_partition (P i) (R i) (hPcells i).1
      (hRpartition i)
  have hQcells (i : Fin M₀) (j : Fin (L i)) :
      (Q i j).IsProper /\ 0 < (Q i j).length /\
        ((Q i j).length = v - 1 \/ (Q i j).length = v) := by
    refine ⟨section5NatTransport_isProper (P i) (R i j)
      (hPcells i).1 (hRcells i j).1, ?_, ?_⟩
    · simpa only [Q, section5NatTransport_length] using (hRcells i j).2.1
    · simpa only [Q, section5NatTransport_length] using (hRcells i j).2.2
  have hQradius (i : Fin M₀) (j : Fin (L i)) :
      cor56CenteredRadiusAtMostReal
        ((Q i j).carrier.image fun y : Nat => phi (y : ZMod N))
        ((1 / 2 : Real) *
          ((r : Real) ^
            (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N)) := by
    have hRsubset : (R i j).carrier ⊆ Finset.range (P i).length :=
      IsPartition.cell_subset (hRpartition i) j
    let E : Nat := (P i).length ^ k * centeredAbs top
    have herr (t : Nat) (ht : t ∈ (R i j).carrier) :
        centeredAbs (top * (t : ZMod N) ^ k) <= E := by
      have htlt : t < (P i).length := Finset.mem_range.mp (hRsubset ht)
      have htPow : t ^ k <= (P i).length ^ k :=
        Nat.pow_le_pow_left htlt.le k
      have hcast : (top * (t : ZMod N) ^ k) =
          ((t ^ k : Nat) : ZMod N) * top := by
        push_cast
        ring
      rw [hcast]
      exact (cor56_centeredAbs_nat_mul_le (t ^ k) top).trans
        (Nat.mul_le_mul_right (centeredAbs top) htPow)
    have hadd := cor56_centeredRadius_add_error (R i j).carrier
      (fun z : Nat => psi i (z : ZMod N))
      (fun z : Nat => top * (z : ZMod N) ^ k)
      (hRradius i j) E herr
    have hrecScale :
        (1 / 2 : Real) *
            (((P i).length : Real) ^
              (-(2 * (polynomialPartitionConstant (k - 1) : Real)⁻¹)) * N) <=
          (1 / 4 : Real) *
            ((r : Real) ^
              (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) :=
      cor56_recursive_radius_scale hk hrW (hPlower i)
    have herrScale : (E : Real) <=
        (1 / 4 : Real) *
          ((r : Real) ^
            (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) := by
      dsimp only [E]
      exact cor56_leading_error_scale hk hrW (hPupper i) htop
    have hscale :
        (1 / 2 : Real) *
              (((P i).length : Real) ^
                (-(2 * (polynomialPartitionConstant (k - 1) : Real)⁻¹)) * N) +
            E <=
          (1 / 2 : Real) *
            ((r : Real) ^
              (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) := by
      calc
        (1 / 2 : Real) *
                (((P i).length : Real) ^
                  (-(2 * (polynomialPartitionConstant (k - 1) : Real)⁻¹)) * N) +
              E <=
            (1 / 4 : Real) *
                ((r : Real) ^
                  (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) +
              (1 / 4 : Real) *
                ((r : Real) ^
                  (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) :=
          add_le_add hrecScale herrScale
        _ = (1 / 2 : Real) *
            ((r : Real) ^
              (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) := by
          ring
    have hadd' := cor56_centeredRadius_mono (fun _ h => h) hadd hscale
    rw [cor56NatTransport_image]
    convert hadd' using 1
    apply Finset.image_congr
    intro t ht
    dsimp only [psi]
    have hstep : ((P i).step : ZMod N) = p := by rw [hPstep]
    rw [hstep]
    dsimp only [top]
    ring
  let F : Fin (∑ i, L i) -> NatAP := section5NatFlatten L Q
  have hFpartition : IsNatAPPartition F (Finset.range r) :=
    section5NatFlatten_partition P (Finset.range r) L Q hPpartition hQpartition
  have hFproper : forall j, (F j).IsProper :=
    section5NatFlatten_isProper L Q (fun i j => (hQcells i j).1)
  have hsumPos : 0 < ∑ i, L i := by
    let i : Fin M₀ := ⟨0, hM₀⟩
    exact lt_of_lt_of_le (hL i)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  refine ⟨∑ i, L i, F, hsumPos, hFpartition, ?_, ?_⟩
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    simpa only [F, section5NatFlatten, z] using hQcells z.1 z.2
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    simpa only [F, section5NatFlatten, z] using hQradius z.1 z.2

private theorem cor56_strong_centered_all_degrees :
    forall k : Nat, 1 <= k -> cor56StrongCenteredAtDegree k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      by_cases hkOne : k = 1
      · simpa only [hkOne] using cor56_strong_centered_degree_one
      · have hkTwo : 2 <= k := by omega
        exact cor56_strong_centered_step hkTwo (ih (k - 1) (by omega) (by omega))

/-- The actual degree induction gives twice the diameter exponent advertised
in Corollary 5.6.  The linear base uses Lemma 2.3 rather than the nonlinear
recurrence. -/
theorem corollary_5_6_strong_diameter_holds :
    corollary_5_6_strong_diameter := by
  intro N k r v _ phi hk hphi hrT hrN hv hvupper
  obtain ⟨M, P, hM, hpartition, hcells, hradius⟩ :=
    cor56_strong_centered_all_degrees k hk N r v phi hphi hrT hrN hv hvupper
  refine ⟨M, P, hM, hpartition, hcells, ?_⟩
  intro j
  have hdiam := cor56_centeredRadius_to_diameter (hradius j)
  have hscale :
      (2 : Real) *
          ((1 / 2 : Real) *
            ((r : Real) ^
              (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N)) =
        (r : Real) ^
            (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N := by
    ring
  rw [hscale] at hdiam
  exact hdiam

end LeanProofs.GowersSzemeredi
