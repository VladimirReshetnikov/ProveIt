import DavisEntringerGrahamSimmons1977.Statements
import Mathlib

/-!
# Nathanson's modular progression theorem

This module proves the two results quoted in concluding remark 2 of
Davis--Entringer--Graham--Simmons (1977).  A parity-block recursion constructs
three-term-free modular permutations at powers of two.  For every other
modulus, its odd factor supplies a coset whose first two displayed residues
force a later third term.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.DavisEntringerGrahamSimmons1977

private def modularParityPermutationFun (n : Nat) (p : FinitePermutation n)
    (i : Fin (2 * n)) : Fin (2 * n) :=
  if hi : (i : Nat) < n then
    ⟨2 * (p ⟨i, hi⟩ : Nat), by have := (p ⟨i, hi⟩).isLt; omega⟩
  else
    let j : Fin n := ⟨(i : Nat) - n, by omega⟩
    ⟨2 * (p j : Nat) + 1, by have := (p j).isLt; omega⟩

private theorem modularParityPermutationFun_injective (n : Nat)
    (p : FinitePermutation n) :
    Function.Injective (modularParityPermutationFun n p) := by
  intro i j hij
  have hijv := congrArg Fin.val hij
  by_cases hi : (i : Nat) < n <;> by_cases hj : (j : Nat) < n
  · simp only [modularParityPermutationFun, dif_pos hi, dif_pos hj] at hijv
    have hp : p ⟨i, hi⟩ = p ⟨j, hj⟩ := by
      apply Fin.ext
      omega
    have hval : (i : Nat) = (j : Nat) := by
      simpa using congrArg Fin.val (p.injective hp)
    exact Fin.ext hval
  · simp only [modularParityPermutationFun, dif_pos hi, dif_neg hj] at hijv
    omega
  · simp only [modularParityPermutationFun, dif_neg hi, dif_pos hj] at hijv
    omega
  · simp only [modularParityPermutationFun, dif_neg hi, dif_neg hj] at hijv
    have hp : p ⟨(i : Nat) - n, by omega⟩ =
        p ⟨(j : Nat) - n, by omega⟩ := by
      apply Fin.ext
      omega
    have hsub : (i : Nat) - n = (j : Nat) - n :=
      congrArg Fin.val (p.injective hp)
    apply Fin.ext
    omega

private def modularParityPermutation (n : Nat) (p : FinitePermutation n) :
    FinitePermutation (2 * n) :=
  Equiv.ofBijective (modularParityPermutationFun n p)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨modularParityPermutationFun_injective n p, rfl⟩)

private theorem modularParityPermutation_apply (n : Nat)
    (p : FinitePermutation n) (i : Fin (2 * n)) :
    modularParityPermutation n p i = modularParityPermutationFun n p i := by
  rfl

private theorem modularParityPermutation_value_first (n : Nat)
    (p : FinitePermutation n) (i : Fin (2 * n)) (hi : (i : Nat) < n) :
    finiteModValue (modularParityPermutation n p) i =
      ((2 * (p ⟨i, hi⟩ : Nat) + 1 : Nat) : ZMod (2 * n)) := by
  simp [finiteModValue, modularParityPermutation_apply,
    modularParityPermutationFun, hi]

private theorem modularParityPermutation_value_second (n : Nat)
    (p : FinitePermutation n) (i : Fin (2 * n)) (hi : ¬(i : Nat) < n) :
    finiteModValue (modularParityPermutation n p) i =
      ((2 * ((p ⟨(i : Nat) - n, by
          apply (Nat.sub_lt_iff_lt_add (le_of_not_gt hi)).2
          simpa [Nat.two_mul] using i.isLt⟩ : Nat) + 1) : Nat) :
        ZMod (2 * n)) := by
  have hi_lt : (i : Nat) < 2 * n := i.isLt
  simp [finiteModValue, modularParityPermutation_apply,
    modularParityPermutationFun, hi]
  ring

@[simp] private theorem cast_even_to_two (n x : Nat) :
    (ZMod.cast ((2 * x : Nat) : ZMod (2 * n)) : ZMod 2) = 0 := by
  rw [ZMod.cast_natCast (R := ZMod 2) (show 2 ∣ 2 * n from ⟨n, rfl⟩)]
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

@[simp] private theorem cast_odd_to_two (n x : Nat) :
    (ZMod.cast ((2 * x + 1 : Nat) : ZMod (2 * n)) : ZMod 2) = 1 := by
  rw [ZMod.cast_natCast (R := ZMod 2) (show 2 ∣ 2 * n from ⟨n, rfl⟩)]
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]

private theorem cancel_two_zmod (n : Nat) (x y : Int)
    (h : ((2 * x : Int) : ZMod (2 * n)) =
      ((2 * y : Int) : ZMod (2 * n))) :
    (x : ZMod n) = (y : ZMod n) := by
  rw [ZMod.intCast_eq_intCast_iff] at h ⊢
  rw [Int.modEq_iff_dvd] at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  push_cast at hk
  apply (mul_left_cancel₀ (show (2 : Int) ≠ 0 by norm_num))
  linear_combination hk

private theorem finiteModValue_injective {n : Nat} (_hn : 0 < n)
    (p : FinitePermutation n) : Function.Injective (finiteModValue p) := by
  letI : NeZero n := ⟨_hn.ne'⟩
  intro i j hij
  have hcast : ((p i : Nat) : ZMod n) = ((p j : Nat) : ZMod n) := by
    have hsub := congrArg (fun z : ZMod n => z - 1) hij
    simpa [finiteModValue, Nat.cast_add] using hsub
  have hval := congrArg ZMod.val hcast
  simp only [ZMod.val_natCast_of_lt (p i).isLt,
    ZMod.val_natCast_of_lt (p j).isLt] at hval
  exact p.injective (Fin.ext hval)

private theorem modularParityPermutation_free {n : Nat} (hn : 0 < n)
    (p : FinitePermutation n) (hp : ModularAPFree p 3) :
    ModularAPFree (modularParityPermutation n p) 3 := by
  intro hap
  obtain ⟨pos, hpos, a, d, hd, hvalues⟩ := hap
  have hp01 : (pos (0 : Fin 3) : Nat) < pos 1 := hpos (by decide)
  have hp12 : (pos (1 : Fin 3) : Nat) < pos 2 := hpos (by decide)
  have hrelation :
      finiteModValue (modularParityPermutation n p) (pos 0) +
          finiteModValue (modularParityPermutation n p) (pos 2) =
        2 * finiteModValue (modularParityPermutation n p) (pos 1) := by
    rw [hvalues 0, hvalues 1, hvalues 2]
    norm_num
    ring
  let castToTwo : ZMod (2 * n) →+* ZMod 2 :=
    ZMod.castHom (by exact ⟨n, by omega⟩) (ZMod 2)
  have hcastEven (x : Nat) :
      castToTwo ((2 * x : Nat) : ZMod (2 * n)) = 0 := by
    change (ZMod.cast ((2 * x : Nat) : ZMod (2 * n)) : ZMod 2) = 0
    exact cast_even_to_two n x
  have hcastOdd (x : Nat) :
      castToTwo ((2 * x + 1 : Nat) : ZMod (2 * n)) = 1 := by
    change (ZMod.cast ((2 * x + 1 : Nat) : ZMod (2 * n)) : ZMod 2) = 1
    exact cast_odd_to_two n x
  have hparity :
      castToTwo (finiteModValue (modularParityPermutation n p) (pos 0)) =
        castToTwo (finiteModValue (modularParityPermutation n p) (pos 2)) := by
    have hmapped := congrArg castToTwo hrelation
    simp only [map_add, map_mul, map_ofNat] at hmapped
    have hneg (z : ZMod 2) : -z = z := by
      rw [← neg_one_mul, show (-1 : ZMod 2) = 1 by decide, one_mul]
    have hsum :
        castToTwo (finiteModValue (modularParityPermutation n p) (pos 0)) +
            castToTwo (finiteModValue (modularParityPermutation n p) (pos 2)) = 0 := by
      simpa only [show (2 : ZMod 2) = 0 by decide, zero_mul] using hmapped
    calc
      castToTwo (finiteModValue (modularParityPermutation n p) (pos 0)) =
          -castToTwo (finiteModValue (modularParityPermutation n p) (pos 2)) :=
        eq_neg_of_add_eq_zero_left hsum
      _ = castToTwo (finiteModValue (modularParityPermutation n p) (pos 2)) :=
        hneg _
  have hsame_half :
      ((pos (0 : Fin 3) : Nat) < n) ↔ ((pos (2 : Fin 3) : Nat) < n) := by
    constructor
    · intro h0
      by_contra h2
      rw [modularParityPermutation_value_first n p (pos 0) h0,
        modularParityPermutation_value_second n p (pos 2) h2] at hparity
      rw [hcastOdd, hcastEven] at hparity
      exact one_ne_zero hparity
    · intro h2
      by_contra h0
      rw [modularParityPermutation_value_second n p (pos 0) h0,
        modularParityPermutation_value_first n p (pos 2) h2] at hparity
      rw [hcastEven, hcastOdd] at hparity
      exact zero_ne_one hparity
  by_cases hfirst : (pos (0 : Fin 3) : Nat) < n
  · have hsecond : (pos (1 : Fin 3) : Nat) < n := hp12.trans (hsame_half.mp hfirst)
    have hthird : (pos (2 : Fin 3) : Nat) < n := hsame_half.mp hfirst
    let qpos : Fin 3 → Fin n := fun i => ⟨pos i, by
      fin_cases i
      · exact hfirst
      · exact hsecond
      · exact hthird⟩
    have hqpos : StrictMono qpos := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · exact hp01
      · exact hp12
    have hprojected :
        finiteModValue p (qpos 0) + finiteModValue p (qpos 2) =
          2 * finiteModValue p (qpos 1) := by
      let x0 : Int := (p (qpos 0) : Nat) + 1
      let x1 : Int := (p (qpos 1) : Nat) + 1
      let x2 : Int := (p (qpos 2) : Nat) + 1
      have hv0 : finiteModValue (modularParityPermutation n p) (pos 0) =
          ((2 * x0 - 1 : Int) : ZMod (2 * n)) := by
        rw [modularParityPermutation_value_first n p (pos 0) hfirst]
        push_cast
        simp [x0, qpos]
        ring
      have hv1 : finiteModValue (modularParityPermutation n p) (pos 1) =
          ((2 * x1 - 1 : Int) : ZMod (2 * n)) := by
        rw [modularParityPermutation_value_first n p (pos 1) hsecond]
        push_cast
        simp [x1, qpos]
        ring
      have hv2 : finiteModValue (modularParityPermutation n p) (pos 2) =
          ((2 * x2 - 1 : Int) : ZMod (2 * n)) := by
        rw [modularParityPermutation_value_first n p (pos 2) hthird]
        push_cast
        simp [x2, qpos]
        ring
      rw [hv0, hv1, hv2] at hrelation
      push_cast at hrelation
      have hdouble : ((2 * (x0 + x2) : Int) : ZMod (2 * n)) =
          ((2 * (2 * x1) : Int) : ZMod (2 * n)) := by
        push_cast
        linear_combination hrelation
      have hcancel := cancel_two_zmod n (x0 + x2) (2 * x1) hdouble
      simpa [finiteModValue, x0, x1, x2, qpos] using hcancel
    apply hp
    refine ⟨qpos, hqpos, finiteModValue p (qpos 0),
      finiteModValue p (qpos 1) - finiteModValue p (qpos 0), ?_, ?_⟩
    · rw [bne_iff_ne]
      intro hzero
      have heq : finiteModValue p (qpos 1) = finiteModValue p (qpos 0) :=
        sub_eq_zero.mp hzero
      have := finiteModValue_injective hn p heq
      have h10 : (1 : Fin 3) = 0 := hqpos.injective this
      omega
    · intro i
      fin_cases i
      · simp
      · simp
      · change finiteModValue p (qpos 2) =
          finiteModValue p (qpos 0) +
            (2 : Nat) * (finiteModValue p (qpos 1) - finiteModValue p (qpos 0))
        push_cast
        linear_combination hprojected
  · have hsecond : ¬(pos (1 : Fin 3) : Nat) < n := by omega
    have hthird : ¬(pos (2 : Fin 3) : Nat) < n := by
      exact fun h => hfirst (hsame_half.mpr h)
    have h0bound : (pos (0 : Fin 3) : Nat) - n < n := by
      apply (Nat.sub_lt_iff_lt_add (le_of_not_gt hfirst)).2
      simpa [Nat.two_mul] using (pos (0 : Fin 3)).isLt
    have h1bound : (pos (1 : Fin 3) : Nat) - n < n := by
      apply (Nat.sub_lt_iff_lt_add (le_of_not_gt hsecond)).2
      simpa [Nat.two_mul] using (pos (1 : Fin 3)).isLt
    have h2bound : (pos (2 : Fin 3) : Nat) - n < n := by
      apply (Nat.sub_lt_iff_lt_add (le_of_not_gt hthird)).2
      simpa [Nat.two_mul] using (pos (2 : Fin 3)).isLt
    let qpos : Fin 3 → Fin n := fun i => ⟨(pos i : Nat) - n, by
      fin_cases i
      · exact h0bound
      · exact h1bound
      · exact h2bound⟩
    have hqpos : StrictMono qpos := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · simp [qpos]
        omega
      · simp [qpos]
        omega
    have hprojected :
        finiteModValue p (qpos 0) + finiteModValue p (qpos 2) =
          2 * finiteModValue p (qpos 1) := by
      let x0 : Int := (p (qpos 0) : Nat) + 1
      let x1 : Int := (p (qpos 1) : Nat) + 1
      let x2 : Int := (p (qpos 2) : Nat) + 1
      have hv0 : finiteModValue (modularParityPermutation n p) (pos 0) =
          ((2 * x0 : Int) : ZMod (2 * n)) := by
        rw [modularParityPermutation_value_second n p (pos 0) hfirst]
        push_cast
        simp [x0, qpos]
      have hv1 : finiteModValue (modularParityPermutation n p) (pos 1) =
          ((2 * x1 : Int) : ZMod (2 * n)) := by
        rw [modularParityPermutation_value_second n p (pos 1) hsecond]
        push_cast
        simp [x1, qpos]
      have hv2 : finiteModValue (modularParityPermutation n p) (pos 2) =
          ((2 * x2 : Int) : ZMod (2 * n)) := by
        rw [modularParityPermutation_value_second n p (pos 2) hthird]
        push_cast
        simp [x2, qpos]
      rw [hv0, hv1, hv2] at hrelation
      push_cast at hrelation
      have hdouble : ((2 * (x0 + x2) : Int) : ZMod (2 * n)) =
          ((2 * (2 * x1) : Int) : ZMod (2 * n)) := by
        push_cast
        linear_combination hrelation
      have hcancel := cancel_two_zmod n (x0 + x2) (2 * x1) hdouble
      simpa [finiteModValue, x0, x1, x2, qpos] using hcancel
    apply hp
    refine ⟨qpos, hqpos, finiteModValue p (qpos 0),
      finiteModValue p (qpos 1) - finiteModValue p (qpos 0), ?_, ?_⟩
    · rw [bne_iff_ne]
      intro hzero
      have heq : finiteModValue p (qpos 1) = finiteModValue p (qpos 0) :=
        sub_eq_zero.mp hzero
      have := finiteModValue_injective hn p heq
      have h10 : (1 : Fin 3) = 0 := hqpos.injective this
      omega
    · intro i
      fin_cases i
      · simp
      · simp
      · change finiteModValue p (qpos 2) =
          finiteModValue p (qpos 0) +
            (2 : Nat) * (finiteModValue p (qpos 1) - finiteModValue p (qpos 0))
        push_cast
        linear_combination hprojected

theorem nathanson_power_of_two_holds : nathanson_power_of_two := by
  intro r
  induction r with
  | zero =>
      refine ⟨Equiv.refl (Fin 1), ?_⟩
      intro hap
      obtain ⟨pos, hpos, _⟩ := hap
      have := hpos (show (0 : Fin 3) < 1 by decide)
      omega
  | succ r ih =>
      obtain ⟨p, hp⟩ := ih
      rw [pow_succ, mul_comm]
      exact ⟨modularParityPermutation (2 ^ r) p,
        modularParityPermutation_free (pow_pos (by decide) r) p hp⟩

private def oddFactorIndex (q m : Nat) (hq : 0 < q) (t : Fin m) :
    Fin (q * m) :=
  ⟨q * ((t : Nat) + 1) - 1, by
    have ht : (t : Nat) + 1 ≤ m := Nat.succ_le_iff.mpr t.isLt
    have hmul : q * ((t : Nat) + 1) ≤ q * m := Nat.mul_le_mul_left q ht
    have hpos : 0 < q * ((t : Nat) + 1) := Nat.mul_pos hq (Nat.succ_pos _)
    omega⟩

private theorem oddFactorIndex_injective (q m : Nat) (hq : 0 < q) :
    Function.Injective (oddFactorIndex q m hq) := by
  intro t u htu
  have hval := congrArg Fin.val htu
  change q * ((t : Nat) + 1) - 1 = q * ((u : Nat) + 1) - 1 at hval
  have htpos : 1 ≤ q * ((t : Nat) + 1) :=
    (Nat.mul_pos hq (Nat.succ_pos _))
  have hupos : 1 ≤ q * ((u : Nat) + 1) :=
    (Nat.mul_pos hq (Nat.succ_pos _))
  have hmul : q * ((t : Nat) + 1) = q * ((u : Nat) + 1) := by
    calc
      q * ((t : Nat) + 1) = q * ((t : Nat) + 1) - 1 + 1 :=
        (Nat.sub_add_cancel htpos).symm
      _ = q * ((u : Nat) + 1) - 1 + 1 := by rw [hval]
      _ = q * ((u : Nat) + 1) := Nat.sub_add_cancel hupos
  have hsucc : (t : Nat) + 1 = (u : Nat) + 1 :=
    Nat.mul_left_cancel hq hmul
  exact Fin.ext (by omega)

private def oddFactorPosition (q m : Nat) (hq : 0 < q)
    (p : FinitePermutation (q * m)) (t : Fin m) : Fin (q * m) :=
  p.symm (oddFactorIndex q m hq t)

private theorem oddFactorPosition_injective (q m : Nat) (hq : 0 < q)
    (p : FinitePermutation (q * m)) :
    Function.Injective (oddFactorPosition q m hq p) :=
  p.symm.injective.comp (oddFactorIndex_injective q m hq)

private theorem oddFactorPosition_value (q m : Nat) (hq : 0 < q)
    (p : FinitePermutation (q * m)) (t : Fin m) :
    finiteModValue p (oddFactorPosition q m hq p t) =
      ((q * ((t : Nat) + 1) : Nat) : ZMod (q * m)) := by
  simp [finiteModValue, oddFactorPosition, oddFactorIndex]
  have hpos : 0 < q * ((t : Nat) + 1) := Nat.mul_pos hq (Nat.succ_pos _)
  have hnat := Nat.sub_add_cancel hpos
  have hcast := congrArg (fun z : Nat => (z : ZMod (q * m))) hnat
  push_cast at hcast
  simpa using hcast

private theorem finEquiv_eq_natCast {m : Nat} [NeZero m] (t : Fin m) :
    ZMod.finEquiv m t = ((t : Nat) : ZMod m) := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
      apply Fin.ext
      change (t : Nat) = (t : Nat) % (m + 1)
      exact (Nat.mod_eq_of_lt t.isLt).symm

private theorem monotone_mod_ap_of_odd_factor (q m : Nat)
    (hq : 0 < q) (hm : 3 ≤ m) (hmodd : ¬2 ∣ m)
    (p : FinitePermutation (q * m)) : HasMonotoneModAP p 3 := by
  letI : NeZero m := ⟨by omega⟩
  let factorPosition : Fin m → Fin (q * m) := oddFactorPosition q m hq p
  have hfactorPosition : Function.Injective factorPosition :=
    oddFactorPosition_injective q m hq p
  let positions : Finset (Fin (q * m)) := Finset.univ.image factorPosition
  have hpositionsCard : positions.card = m := by
    rw [show positions = Finset.univ.image factorPosition by rfl,
      Finset.card_image_of_injective _ hfactorPosition]
    simp
  let ordered : Fin m ≃o positions := positions.orderIsoOfFin hpositionsCard
  let orderedPosition : Fin m → Fin (q * m) := fun i => (ordered i).1
  have horderedPosition : StrictMono orderedPosition := by
    intro i j hij
    exact ordered.strictMono hij
  let first : Fin m := ⟨0, by omega⟩
  let second : Fin m := ⟨1, by omega⟩
  have hfirstMem : orderedPosition first ∈ positions := (ordered first).2
  have hsecondMem : orderedPosition second ∈ positions := (ordered second).2
  obtain ⟨t0, _, ht0⟩ := Finset.mem_image.mp hfirstMem
  obtain ⟨t1, _, ht1⟩ := Finset.mem_image.mp hsecondMem
  have hfirstSecond : orderedPosition first < orderedPosition second := by
    apply horderedPosition
    apply Fin.mk_lt_mk.mpr
    norm_num
  have ht0t1 : t0 ≠ t1 := by
    intro heq
    subst t1
    rw [ht0] at ht1
    exact (ne_of_lt hfirstSecond) ht1
  let coefficient : Fin m ≃ ZMod m :=
    (ZMod.finEquiv m).toEquiv.trans (Equiv.addRight 1)
  have coefficient_apply (t : Fin m) :
      coefficient t = (((t : Nat) + 1 : Nat) : ZMod m) := by
    change ZMod.finEquiv m t + 1 = (((t : Nat) + 1 : Nat) : ZMod m)
    rw [finEquiv_eq_natCast]
    push_cast
    rfl
  let u0 : ZMod m := coefficient t0
  let u1 : ZMod m := coefficient t1
  let u2 : ZMod m := 2 * u1 - u0
  let t2 : Fin m := coefficient.symm u2
  have hcoefficient_t2 : coefficient t2 = u2 := coefficient.apply_symm_apply u2
  have hu0u1 : u0 ≠ u1 := by
    intro heq
    apply ht0t1
    exact coefficient.injective heq
  have ht2t1 : t2 ≠ t1 := by
    intro heq
    have hu2u1 : u2 = u1 := by simpa [t2] using congrArg coefficient heq
    apply hu0u1
    dsimp [u2] at hu2u1
    have hu1u0 : u1 = u0 := by
      rw [← sub_eq_zero]
      calc
        u1 - u0 = (2 * u1 - u0) - u1 := by ring
        _ = 0 := by rw [hu2u1, sub_self]
    exact hu1u0.symm
  have hodd : Odd m := Nat.not_even_iff_odd.mp fun heven =>
    hmodd (even_iff_two_dvd.mp heven)
  have htwoUnit : IsUnit (2 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hodd)
  have ht2t0 : t2 ≠ t0 := by
    intro heq
    have hu2u0 : u2 = u0 := by simpa [t2] using congrArg coefficient heq
    have htwice : (2 : ZMod m) * u1 = 2 * u0 := by
      dsimp [u2] at hu2u0
      linear_combination hu2u0
    have hu1u0 : u1 = u0 := htwoUnit.mul_left_cancel htwice
    exact hu0u1 hu1u0.symm
  have ht2Mem : factorPosition t2 ∈ positions := by
    simp [positions, factorPosition]
  let thirdIndex : Fin m := ordered.symm ⟨factorPosition t2, ht2Mem⟩
  have hthirdPosition : orderedPosition thirdIndex = factorPosition t2 := by
    exact congrArg Subtype.val (ordered.apply_symm_apply ⟨factorPosition t2, ht2Mem⟩)
  have hthirdNeFirst : thirdIndex ≠ first := by
    intro heq
    have hposEq : factorPosition t2 = factorPosition t0 := by
      rw [← hthirdPosition, heq, ← ht0]
    exact ht2t0 (hfactorPosition hposEq)
  have hthirdNeSecond : thirdIndex ≠ second := by
    intro heq
    have hposEq : factorPosition t2 = factorPosition t1 := by
      rw [← hthirdPosition, heq, ← ht1]
    exact ht2t1 (hfactorPosition hposEq)
  have hsecondThirdIndex : second < thirdIndex := by
    have hthirdNotZero : (thirdIndex : Nat) ≠ 0 := by
      intro hzero
      exact hthirdNeFirst (Fin.ext (by simpa [first] using hzero))
    have hthirdNotOne : (thirdIndex : Nat) ≠ 1 := by
      intro hone
      exact hthirdNeSecond (Fin.ext (by simpa [second] using hone))
    have hthirdTwo : 2 ≤ (thirdIndex : Nat) := by omega
    exact hthirdTwo
  have hpos01 : factorPosition t0 < factorPosition t1 := by
    simpa [ht0, ht1] using hfirstSecond
  have hpos12 : factorPosition t1 < factorPosition t2 := by
    have := horderedPosition hsecondThirdIndex
    simpa [ht1, hthirdPosition] using this
  let apPosition : Fin 3 → Fin (q * m) := ![factorPosition t0,
    factorPosition t1, factorPosition t2]
  have hapPosition : StrictMono apPosition := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact hpos01
    · exact hpos12
  have hzmod :
      ((((t2 : Nat) + 1 : Nat) : ZMod m)) =
        2 * ((((t1 : Nat) + 1 : Nat) : ZMod m)) -
          ((((t0 : Nat) + 1 : Nat) : ZMod m)) := by
    rw [← coefficient_apply, ← coefficient_apply, ← coefficient_apply,
      hcoefficient_t2]
  let c0 : Int := (t0 : Nat) + 1
  let c1 : Int := (t1 : Nat) + 1
  let c2 : Int := (t2 : Nat) + 1
  have hzcast : (c2 : ZMod m) = 2 * (c1 : ZMod m) - (c0 : ZMod m) := by
    simpa [c0, c1, c2] using hzmod
  have hzdiv : (m : Int) ∣ 2 * c1 - c0 - c2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr hzcast.symm
  have hlift : (((q : Int) * c2 : Int) : ZMod (q * m)) =
      2 * (((q : Int) * c1 : Int) : ZMod (q * m)) -
        (((q : Int) * c0 : Int) : ZMod (q * m)) := by
    have hsingle : (((q : Int) * c2 : Int) : ZMod (q * m)) =
        ((2 * ((q : Int) * c1) - (q : Int) * c0 : Int) : ZMod (q * m)) := by
      rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hzdiv
      refine ⟨k, ?_⟩
      calc
        (2 * ((q : Int) * c1) - (q : Int) * c0) - (q : Int) * c2 =
            (q : Int) * (2 * c1 - c0 - c2) := by ring
        _ = (q : Int) * ((m : Int) * k) := by rw [hk]
        _ = ((q * m : Nat) : Int) * k := by push_cast; ring
    push_cast at hsingle ⊢
    exact hsingle
  have hvalue0 : finiteModValue p (factorPosition t0) =
      (((q : Int) * c0 : Int) : ZMod (q * m)) := by
    rw [show factorPosition t0 = oddFactorPosition q m hq p t0 by rfl,
      oddFactorPosition_value]
    push_cast
    simp [c0]
  have hvalue1 : finiteModValue p (factorPosition t1) =
      (((q : Int) * c1 : Int) : ZMod (q * m)) := by
    rw [show factorPosition t1 = oddFactorPosition q m hq p t1 by rfl,
      oddFactorPosition_value]
    push_cast
    simp [c1]
  have hvalue2 : finiteModValue p (factorPosition t2) =
      (((q : Int) * c2 : Int) : ZMod (q * m)) := by
    rw [show factorPosition t2 = oddFactorPosition q m hq p t2 by rfl,
      oddFactorPosition_value]
    push_cast
    simp [c2]
  have hprogression : finiteModValue p (factorPosition t2) =
      2 * finiteModValue p (factorPosition t1) -
        finiteModValue p (factorPosition t0) := by
    rw [hvalue0, hvalue1, hvalue2]
    exact hlift
  refine ⟨apPosition, hapPosition, finiteModValue p (factorPosition t0),
    finiteModValue p (factorPosition t1) - finiteModValue p (factorPosition t0), ?_, ?_⟩
  · rw [bne_iff_ne]
    intro hzero
    have heq : finiteModValue p (factorPosition t1) =
        finiteModValue p (factorPosition t0) := sub_eq_zero.mp hzero
    have hposEq := finiteModValue_injective (Nat.mul_pos hq (by omega)) p heq
    exact (ne_of_lt hpos01) hposEq.symm
  · intro i
    fin_cases i
    · simp [apPosition]
    · simp [apPosition]
    · change finiteModValue p (factorPosition t2) =
        finiteModValue p (factorPosition t0) +
          (2 : Nat) * (finiteModValue p (factorPosition t1) -
            finiteModValue p (factorPosition t0))
      push_cast
      linear_combination hprogression

theorem nathanson_non_power_of_two_holds : nathanson_non_power_of_two := by
  intro n hn hnot
  let q : Nat := ordProj[2] n
  let m : Nat := ordCompl[2] n
  have hqm : q * m = n := by
    simpa [q, m] using Nat.ordProj_mul_ordCompl_eq_self n 2
  have hq : 0 < q := by
    exact Nat.ordProj_pos n 2
  have hmpos : 0 < m := by
    simpa [m] using Nat.ordCompl_pos 2 hn.ne'
  have hmodd : ¬2 ∣ m := by
    simpa [m] using Nat.not_dvd_ordCompl (p := 2) (by norm_num) hn.ne'
  have hmneOne : m ≠ 1 := by
    intro hmone
    apply hnot
    refine ⟨n.factorization 2, ?_⟩
    calc
      n = q * m := hqm.symm
      _ = q := by rw [hmone, mul_one]
      _ = 2 ^ n.factorization 2 := by rfl
  have hmneTwo : m ≠ 2 := by
    intro hmtwo
    apply hmodd
    rw [hmtwo]
  have hm : 3 ≤ m := by omega
  rw [← hqm]
  intro p
  exact monotone_mod_ap_of_odd_factor q m hq hm hmodd p

end LeanProofs.DavisEntringerGrahamSimmons1977
