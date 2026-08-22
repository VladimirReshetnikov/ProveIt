import ExponentialIdentities.TwoBaseIntegerExponent.KummerCompatibilityFinite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Prime-power Kummer coherence counts

This file lifts the depth-one field count in `KummerCompatibilityFinite` to
the local rings `ZMod (q ^ e)`.  The unrestricted compatible data are written
canonically as a base vector together with an element of the cyclic additive
subgroup that it generates.  Exact additive-order shells then give the count

`1 + sum_{t=1}^e (q^(2t) - q^(2t-2)) q^t`.

The proof is entirely finite.  In particular, it does not use a distribution
or Chebotarev hypothesis.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace PrimePowerKummerCoherence

open Finset Nat

noncomputable section

/-- The additive `n`-torsion of a finite additive group. -/
abbrev NsmulTorsion (n : ℕ) (G : Type*) [AddMonoid G] :=
  {x : G // n • x = 0}

/-- The subtype defined by a decidable predicate is equivalent to the subtype
of the corresponding filtered universal finset. -/
def subtypeFilterEquiv {G : Type*} [Fintype G] (p : G → Prop) [DecidablePred p] :
    {x : G // p x} ≃ ↑((Finset.univ : Finset G).filter p) where
  toFun x := ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
  invFun x := ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- In a finite cyclic additive group, the `n`-torsion has exactly `n`
elements whenever `n` divides the group order. -/
theorem card_nsmulTorsion_of_dvd {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    [IsAddCyclic G] {n : ℕ} (hn : n ≠ 0) (hd : n ∣ Fintype.card G) :
    Fintype.card (NsmulTorsion n G) = n := by
  classical
  rw [Fintype.card_congr (subtypeFilterEquiv (fun x : G => n • x = 0)),
    Fintype.card_coe]
  rw [← sum_card_addOrderOf_eq_card_nsmul_eq_zero hn]
  calc
    ∑ m ∈ n.divisors, #{x : G | addOrderOf x = m} =
        ∑ m ∈ n.divisors, Nat.totient m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [IsAddCyclic.card_addOrderOf_eq_totient]
      exact (Nat.mem_divisors.mp hm).1.trans hd
    _ = n := Nat.sum_totient n

/-- Torsion in a product is the product of the coordinate torsion groups. -/
def nsmulTorsionProdEquiv {G H : Type*} [AddMonoid G] [AddMonoid H] (n : ℕ) :
    NsmulTorsion n (G × H) ≃ NsmulTorsion n G × NsmulTorsion n H where
  toFun x :=
    (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), Prod.ext x.1.2 x.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- The two Kummer base coordinates modulo `q^e`. -/
abbrev PrimePowerBase (q e : ℕ) :=
  ZMod (q ^ e) × ZMod (q ^ e)

/-- A compatible pair is a base vector together with a point in the cyclic
subgroup it generates.  For `ZMod (q^e)`, this is equivalent to saying that
the output is a common scalar multiple of the two base coordinates. -/
abbrev CompatibleDatum (q e : ℕ) :=
  (b : PrimePowerBase q e) × AddSubgroup.zmultiples b

/-- Coordinatewise scalar multiplication over the prime-power residue ring. -/
def scalarBase (q e : ℕ) (k : ZMod (q ^ e)) (b : PrimePowerBase q e) :
    PrimePowerBase q e :=
  (k * b.1, k * b.2)

/-- The direct existential-scalar formulation of prime-power compatibility. -/
def ScalarCompatible (q e : ℕ)
    (z : PrimePowerBase q e × PrimePowerBase q e) : Prop :=
  ∃ k : ZMod (q ^ e), z.2 = scalarBase q e k z.1

/-- Compatible base/output pairs in the direct residue-ring formulation. -/
abbrev ScalarCompatibleDatum (q e : ℕ) :=
  {z : PrimePowerBase q e × PrimePowerBase q e // ScalarCompatible q e z}

noncomputable instance (q e : ℕ) [Fact q.Prime] :
    Fintype (ScalarCompatibleDatum q e) :=
  Fintype.ofFinite _

/-- The cyclic-subgroup model is equivalent to the direct common-scalar
condition.  This equivalence removes the nonuniqueness of scalars above an
imprimitive base vector. -/
noncomputable def scalarCompatibleEquiv {q e : ℕ} [Fact q.Prime] :
    ScalarCompatibleDatum q e ≃ CompatibleDatum q e := by
  classical
  refine
    { toFun := fun z =>
        ⟨z.1.1, ⟨z.1.2, ?_⟩⟩
      invFun := fun z =>
        ⟨(z.1, z.2.1), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨k, hk⟩ := z.2
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(k.cast : ℤ), ?_⟩
    apply Prod.ext
    · change (k.cast : ℤ) • (z.1.1.1 : ZMod (q ^ e)) = z.1.2.1
      calc
        (k.cast : ℤ) • (z.1.1.1 : ZMod (q ^ e)) =
            ((k.cast : ℤ) : ZMod (q ^ e)) * z.1.1.1 :=
          zsmul_eq_mul (z.1.1.1 : ZMod (q ^ e)) k.cast
        _ = k * z.1.1.1 :=
          congrArg (fun a : ZMod (q ^ e) => a * z.1.1.1)
            (ZMod.intCast_zmod_cast k)
        _ = z.1.2.1 := congrArg Prod.fst hk.symm
    · change (k.cast : ℤ) • (z.1.1.2 : ZMod (q ^ e)) = z.1.2.2
      calc
        (k.cast : ℤ) • (z.1.1.2 : ZMod (q ^ e)) =
            ((k.cast : ℤ) : ZMod (q ^ e)) * z.1.1.2 :=
          zsmul_eq_mul (z.1.1.2 : ZMod (q ^ e)) k.cast
        _ = k * z.1.1.2 :=
          congrArg (fun a : ZMod (q ^ e) => a * z.1.1.2)
            (ZMod.intCast_zmod_cast k)
        _ = z.1.2.2 := congrArg Prod.snd hk.symm
  · obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp z.2.2
    refine ⟨(n : ZMod (q ^ e)), ?_⟩
    rw [← hn]
    apply Prod.ext <;> simp [scalarBase, zsmul_eq_mul]
  · intro z
    exact Subtype.ext rfl
  · intro z
    apply Sigma.ext rfl
    rfl

/-- The shell of base vectors of exact additive order `q^t`. -/
abbrev ExactOrderShell (q e t : ℕ) :=
  {b : PrimePowerBase q e // addOrderOf b = q ^ t}

/-- The `q^t`-torsion of the two-coordinate residue module has `q^(2t)`
elements, as long as `t ≤ e`. -/
theorem card_pair_nsmulTorsion {q e t : ℕ} [Fact q.Prime] (ht : t ≤ e) :
    Fintype.card (NsmulTorsion (q ^ t) (PrimePowerBase q e)) = q ^ (2 * t) := by
  classical
  let hq : q.Prime := Fact.out
  rw [Fintype.card_congr (nsmulTorsionProdEquiv (q ^ t)), Fintype.card_prod]
  have hpow_ne : q ^ t ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hdiv : q ^ t ∣ Fintype.card (ZMod (q ^ e)) := by
    rw [ZMod.card]
    exact Nat.pow_dvd_pow q ht
  have hcard : Fintype.card (NsmulTorsion (q ^ t) (ZMod (q ^ e))) = q ^ t :=
    card_nsmulTorsion_of_dvd hpow_ne hdiv
  rw [hcard]
  ring

/-- The lower torsion group embeds as the vectors in the next torsion group
that are already killed one level earlier. -/
def previousTorsionEquiv (q e t : ℕ) :
    NsmulTorsion (q ^ t) (PrimePowerBase q e) ≃
      {x : NsmulTorsion (q ^ (t + 1)) (PrimePowerBase q e) //
        q ^ t • x.1 = 0} where
  toFun x := by
    refine ⟨⟨x.1, ?_⟩, x.2⟩
    rw [pow_succ, mul_nsmul, x.2, nsmul_zero]
  invFun x := ⟨x.1.1, x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext (Subtype.ext rfl)

/-- At positive depth, exact order `q^(t+1)` is equivalent to being killed at
that depth but not one level earlier. -/
def exactOrderShellSuccEquiv {q e : ℕ} (hq : q.Prime) (t : ℕ) :
    ExactOrderShell q e (t + 1) ≃
      {x : NsmulTorsion (q ^ (t + 1)) (PrimePowerBase q e) //
        ¬ q ^ t • x.1 = 0} where
  toFun x := by
    refine ⟨⟨x.1, ?_⟩, ?_⟩
    · exact (addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [x.2]))
    · intro hprev
      have hdvd : q ^ (t + 1) ∣ q ^ t := by
        rw [← x.2]
        exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hprev
      have hle : t + 1 ≤ t :=
        (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hdvd
      omega
  invFun x := by
    refine ⟨x.1.1, ?_⟩
    have hdvd : addOrderOf x.1.1 ∣ q ^ (t + 1) :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr x.1.2
    obtain ⟨k, hk, hord⟩ := (Nat.dvd_prime_pow hq).mp hdvd
    have hnotle : ¬ k ≤ t := by
      intro hkt
      apply x.2
      apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
      rw [hord]
      exact Nat.pow_dvd_pow q hkt
    have hkeq : k = t + 1 := by omega
    simpa [hkeq] using hord
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext (Subtype.ext rfl)

/-- The depth-zero exact-order shell consists only of the zero vector. -/
def exactOrderShellZeroEquiv (q e : ℕ) : ExactOrderShell q e 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0, by simp⟩
  left_inv x := by
    apply Subtype.ext
    exact (AddMonoid.addOrderOf_eq_one_iff.mp (by simpa using x.2)).symm
  right_inv _ := rfl

/-- Exact cardinality of a positive additive-order shell. -/
theorem card_exactOrderShell_succ {q e t : ℕ} [Fact q.Prime] (ht : t + 1 ≤ e) :
    Fintype.card (ExactOrderShell q e (t + 1)) =
      q ^ (2 * (t + 1)) - q ^ (2 * t) := by
  classical
  let hq : q.Prime := Fact.out
  rw [Fintype.card_congr (exactOrderShellSuccEquiv hq t)]
  rw [Fintype.card_subtype_compl
    (fun x : NsmulTorsion (q ^ (t + 1)) (PrimePowerBase q e) => q ^ t • x.1 = 0)]
  rw [show Fintype.card
      {x : NsmulTorsion (q ^ (t + 1)) (PrimePowerBase q e) // q ^ t • x.1 = 0} =
      Fintype.card (NsmulTorsion (q ^ t) (PrimePowerBase q e)) by
        exact Fintype.card_congr (previousTorsionEquiv q e t).symm]
  rw [card_pair_nsmulTorsion ht, card_pair_nsmulTorsion (by omega)]

/-- The exact-order shells partition all base vectors. -/
noncomputable def baseShellEquiv {q e : ℕ} (hq : q.Prime) :
    PrimePowerBase q e ≃ (t : Fin (e + 1)) × ExactOrderShell q e t.1 := by
  classical
  let forget : ((t : Fin (e + 1)) × ExactOrderShell q e t.1) → PrimePowerBase q e :=
    fun x => x.2.1
  have hinj : Function.Injective forget := by
    rintro ⟨t, x⟩ ⟨u, y⟩ hxy
    have hpows : q ^ t.1 = q ^ u.1 := by
      rw [← x.2, ← y.2]
      exact congrArg addOrderOf (by simpa [forget] using hxy)
    have htu : t = u := Fin.ext ((Nat.pow_right_injective hq.two_le) hpows)
    cases htu
    have hxy' : x = y := Subtype.ext (by simpa [forget] using hxy)
    cases hxy'
    rfl
  have hsurj : Function.Surjective forget := by
    intro b
    have hkill : q ^ e • b = 0 := by
      apply Prod.ext
      · change q ^ e • b.1 = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      · change q ^ e • b.2 = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hdvd : addOrderOf b ∣ q ^ e :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
    obtain ⟨t, hte, ht⟩ := (Nat.dvd_prime_pow hq).mp hdvd
    exact ⟨⟨⟨t, by omega⟩, ⟨b, ht⟩⟩, rfl⟩
  exact (Equiv.ofBijective forget ⟨hinj, hsurj⟩).symm

/-- A one-coordinate exact-order shell. -/
abbrev CoordinateOrderShell (q e t : ℕ) :=
  {x : ZMod (q ^ e) // addOrderOf x = q ^ t}

/-- Base vectors whose second coordinate has the full additive order of the
pair.  This is the canonical transverse rank-three normal form. -/
abbrev DominantBase (q e : ℕ) :=
  {b : PrimePowerBase q e // addOrderOf b = addOrderOf b.2}

/-- The exact-order `q^t` part of the transverse normal form. -/
abbrev DominantOrderShell (q e t : ℕ) :=
  {b : PrimePowerBase q e //
    addOrderOf b = q ^ t ∧ addOrderOf b.2 = q ^ t}

/-- A dominant shell is a freely chosen first coordinate killed by `q^t`
and a second coordinate of exact order `q^t`. -/
def dominantOrderShellEquiv (q e t : ℕ) :
    DominantOrderShell q e t ≃
      NsmulTorsion (q ^ t) (ZMod (q ^ e)) × CoordinateOrderShell q e t where
  toFun b := by
    refine (⟨b.1.1, ?_⟩, ⟨b.1.2, b.2.2⟩)
    have hkill : q ^ t • b.1 = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [b.2.1])
    exact congrArg Prod.fst hkill
  invFun x := by
    refine ⟨(x.1.1, x.2.1), ?_⟩
    have hfirst : addOrderOf x.1.1 ∣ q ^ t :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr x.1.2
    constructor
    · rw [Prod.addOrderOf, x.2.2, Nat.lcm_eq_right hfirst]
    · exact x.2.2
  left_inv b := Subtype.ext rfl
  right_inv x := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- The dominant bases split uniquely into their exact additive-order shells. -/
noncomputable def dominantBaseShellEquiv {q e : ℕ} (hq : q.Prime) :
    DominantBase q e ≃ (t : Fin (e + 1)) × DominantOrderShell q e t.1 := by
  classical
  let forget : ((t : Fin (e + 1)) × DominantOrderShell q e t.1) →
      DominantBase q e := fun x => ⟨x.2.1, x.2.2.1.trans x.2.2.2.symm⟩
  have hinj : Function.Injective forget := by
    rintro ⟨t, x⟩ ⟨u, y⟩ hxy
    have hbase : x.1 = y.1 := congrArg Subtype.val hxy
    have hpows : q ^ t.1 = q ^ u.1 := by
      rw [← x.2.1, ← y.2.1, hbase]
    have htu : t = u := Fin.ext ((Nat.pow_right_injective hq.two_le) hpows)
    cases htu
    have hxy' : x = y := Subtype.ext hbase
    cases hxy'
    rfl
  have hsurj : Function.Surjective forget := by
    intro b
    have hkill : q ^ e • b.1 = 0 := by
      apply Prod.ext
      · change q ^ e • b.1.1 = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      · change q ^ e • b.1.2 = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hdvd : addOrderOf b.1 ∣ q ^ e :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
    obtain ⟨t, hte, ht⟩ := (Nat.dvd_prime_pow hq).mp hdvd
    refine ⟨⟨⟨t, by omega⟩, ⟨b.1, ht, ?_⟩⟩, ?_⟩
    · rw [← b.2, ht]
    · exact Subtype.ext rfl
  exact (Equiv.ofBijective forget ⟨hinj, hsurj⟩).symm

/-- Cardinality of one-coordinate `q^t`-torsion. -/
theorem card_coordinate_nsmulTorsion {q e t : ℕ} [Fact q.Prime] (ht : t ≤ e) :
    Fintype.card (NsmulTorsion (q ^ t) (ZMod (q ^ e))) = q ^ t := by
  let hq : q.Prime := Fact.out
  apply card_nsmulTorsion_of_dvd (pow_ne_zero _ hq.ne_zero)
  rw [ZMod.card]
  exact Nat.pow_dvd_pow q ht

/-- Cardinality of a positive one-coordinate exact-order shell. -/
theorem card_coordinateOrderShell_succ {q e t : ℕ} [Fact q.Prime]
    (ht : t + 1 ≤ e) :
    Fintype.card (CoordinateOrderShell q e (t + 1)) = q ^ t * (q - 1) := by
  classical
  let hq : q.Prime := Fact.out
  rw [Fintype.card_congr
    (subtypeFilterEquiv (fun x : ZMod (q ^ e) => addOrderOf x = q ^ (t + 1))),
    Fintype.card_coe]
  rw [IsAddCyclic.card_addOrderOf_eq_totient]
  · exact Nat.totient_prime_pow_succ hq t
  · rw [ZMod.card]
    exact Nat.pow_dvd_pow q ht

/-- Cardinality of the positive transverse normal-form shell. -/
theorem card_dominantOrderShell_succ {q e t : ℕ} [Fact q.Prime]
    (ht : t + 1 ≤ e) :
    Fintype.card (DominantOrderShell q e (t + 1)) =
      q ^ (2 * t + 1) * (q - 1) := by
  rw [Fintype.card_congr (dominantOrderShellEquiv q e (t + 1)),
    Fintype.card_prod, card_coordinate_nsmulTorsion ht,
    card_coordinateOrderShell_succ ht]
  calc
    q ^ (t + 1) * (q ^ t * (q - 1)) =
        (q ^ (t + 1) * q ^ t) * (q - 1) := by ac_rfl
    _ = q ^ (2 * t + 1) * (q - 1) := by
      rw [← pow_add]
      congr 2
      omega

/-- The zero dominant shell consists only of the zero base vector. -/
theorem card_dominantOrderShell_zero {q e : ℕ} [Fact q.Prime] :
    Fintype.card (DominantOrderShell q e 0) = 1 := by
  classical
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, by simp⟩, ?_⟩
  intro y
  apply Subtype.ext
  exact AddMonoid.addOrderOf_eq_one_iff.mp (by simpa using y.2.1)

/-- Exact shell sum for the canonical transverse rank-three count. -/
theorem card_dominantBase_shell_sum {q e : ℕ} [Fact q.Prime] :
    Fintype.card (DominantBase q e) =
      1 + ∑ t ∈ Finset.range e, q ^ (2 * t + 1) * (q - 1) := by
  classical
  let hq : q.Prime := Fact.out
  rw [Fintype.card_congr (dominantBaseShellEquiv hq), Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range
    (fun t => Fintype.card (DominantOrderShell q e t)) (e + 1)]
  rw [Finset.sum_range_succ']
  rw [card_dominantOrderShell_zero]
  rw [Nat.add_comm
    (∑ k ∈ Finset.range e,
      Fintype.card (DominantOrderShell q e (k + 1))) 1]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [card_dominantOrderShell_succ]
  exact Finset.mem_range.mp ht

/-- Geometric-sum form of the canonical transverse rank-three count. -/
theorem card_dominantBase_geometric_sum {q e : ℕ} [Fact q.Prime] :
    Fintype.card (DominantBase q e) =
      1 + q * (q - 1) * ∑ t ∈ Finset.range e, (q ^ 2) ^ t := by
  rw [card_dominantBase_shell_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [pow_add, pow_one, pow_mul]
  ac_rfl

/-- The factor cancellation that changes the rank-three geometric sum into
the denominator `q+1`. -/
theorem rankThree_geometric_factor {q e : ℕ} (hq : q.Prime) :
    (q - 1) * (∑ t ∈ Finset.range e, (q ^ 2) ^ t) =
      (q ^ (2 * e) - 1) / (q + 1) := by
  let S := ∑ t ∈ Finset.range e, (q ^ 2) ^ t
  have hq2 : 1 ≤ q ^ 2 := by nlinarith [hq.two_le]
  have hplus : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel hq2
  have hgeom := geom_sum_mul_add (R := ℕ) (q ^ 2 - 1) e
  rw [hplus] at hgeom
  rw [← pow_mul q 2 e] at hgeom
  have hsub : S * (q ^ 2 - 1) = q ^ (2 * e) - 1 :=
    Nat.eq_sub_of_add_eq hgeom
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [Nat.sub_mul]
    simp only [one_mul, mul_add, mul_one]
    rw [show q * q + q - (q + 1) = q * q - 1 by omega]
    simp [pow_two]
  have hprod : q ^ (2 * e) - 1 = ((q - 1) * S) * (q + 1) := by
    rw [← hsub, hfactor]
    ac_rfl
  exact (Nat.div_eq_of_eq_mul_left (Nat.succ_pos q) hprod).symm

/-- Closed canonical transverse rank-three count:
`1 + q(q^(2e)-1)/(q+1)`. -/
theorem card_dominantBase_primePower {q e : ℕ} [Fact q.Prime] :
    Fintype.card (DominantBase q e) =
      1 + (q * (q ^ (2 * e) - 1)) / (q + 1) := by
  rw [card_dominantBase_geometric_sum]
  let hq : q.Prime := Fact.out
  rw [mul_assoc, rankThree_geometric_factor hq]
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [Nat.sub_mul]
    simp only [one_mul, mul_add, mul_one]
    rw [show q * q + q - (q + 1) = q * q - 1 by omega]
    simp [pow_two]
  have hdvd₁ : q + 1 ∣ q ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_left _ _
  have hdvd₂ : q ^ 2 - 1 ∣ q ^ (2 * e) - 1 := by
    simpa [pow_mul] using
      Nat.pow_sub_one_dvd_pow_sub_one (q ^ 2) (one_dvd e)
  have hdvd : q + 1 ∣ q ^ (2 * e) - 1 := hdvd₁.trans hdvd₂
  rw [← Nat.mul_div_assoc q hdvd]

/-- Four coefficients, grouped into their two rows. -/
abbrev TransverseCoefficients (q e : ℕ) :=
  PrimePowerBase q e × PrimePowerBase q e

/-- Determinant of the two coefficient rows. -/
def coefficientDeterminant {q e : ℕ} (rho : TransverseCoefficients q e) :
    ZMod (q ^ e) :=
  rho.1.1 * rho.2.2 - rho.1.2 * rho.2.1

/-- The row-coordinate change associated with a transverse hyperplane. -/
def coefficientMap {q e : ℕ} (rho : TransverseCoefficients q e)
    (b : PrimePowerBase q e) : PrimePowerBase q e :=
  (rho.1.1 * b.1 + rho.1.2 * b.2,
    rho.2.1 * b.1 + rho.2.2 * b.2)

/-- A unit determinant is the exact transversality condition over
`ZMod (q^e)`. -/
def UnitTransverse {q e : ℕ} (rho : TransverseCoefficients q e) : Prop :=
  IsUnit (coefficientDeterminant rho)

/-- A unit-transverse coefficient map is a bijection of the two-coordinate
residue module. -/
noncomputable def coefficientEquiv {q e : ℕ} (rho : TransverseCoefficients q e)
    (hrho : UnitTransverse rho) : PrimePowerBase q e ≃ PrimePowerBase q e := by
  let dinv : ZMod (q ^ e) := ↑(hrho.unit⁻¹)
  have hinv : dinv * coefficientDeterminant rho = 1 := by
    calc
      dinv * coefficientDeterminant rho = dinv * (↑hrho.unit : ZMod (q ^ e)) :=
        congrArg (fun x : ZMod (q ^ e) => dinv * x) hrho.unit_spec.symm
      _ = ↑(hrho.unit⁻¹ * hrho.unit) := (Units.val_mul _ _).symm
      _ = 1 := by simp
  refine
    { toFun := coefficientMap rho
      invFun := fun y =>
        (dinv * (rho.2.2 * y.1 - rho.1.2 * y.2),
          dinv * (-rho.2.1 * y.1 + rho.1.1 * y.2))
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Prod.ext
    · change dinv *
          (rho.2.2 * (rho.1.1 * x.1 + rho.1.2 * x.2) -
            rho.1.2 * (rho.2.1 * x.1 + rho.2.2 * x.2)) = x.1
      rw [show rho.2.2 * (rho.1.1 * x.1 + rho.1.2 * x.2) -
          rho.1.2 * (rho.2.1 * x.1 + rho.2.2 * x.2) =
          coefficientDeterminant rho * x.1 by
            unfold coefficientDeterminant
            ring]
      rw [← mul_assoc, hinv, one_mul]
    · change dinv *
          (-rho.2.1 * (rho.1.1 * x.1 + rho.1.2 * x.2) +
            rho.1.1 * (rho.2.1 * x.1 + rho.2.2 * x.2)) = x.2
      rw [show -rho.2.1 * (rho.1.1 * x.1 + rho.1.2 * x.2) +
          rho.1.1 * (rho.2.1 * x.1 + rho.2.2 * x.2) =
          coefficientDeterminant rho * x.2 by
            unfold coefficientDeterminant
            ring]
      rw [← mul_assoc, hinv, one_mul]
  · intro y
    apply Prod.ext
    · change rho.1.1 * (dinv * (rho.2.2 * y.1 - rho.1.2 * y.2)) +
          rho.1.2 * (dinv * (-rho.2.1 * y.1 + rho.1.1 * y.2)) = y.1
      rw [show rho.1.1 * (dinv * (rho.2.2 * y.1 - rho.1.2 * y.2)) +
          rho.1.2 * (dinv * (-rho.2.1 * y.1 + rho.1.1 * y.2)) =
          dinv * coefficientDeterminant rho * y.1 by
            unfold coefficientDeterminant
            ring]
      rw [hinv, one_mul]
    · change rho.2.1 * (dinv * (rho.2.2 * y.1 - rho.1.2 * y.2)) +
          rho.2.2 * (dinv * (-rho.2.1 * y.1 + rho.1.1 * y.2)) = y.2
      rw [show rho.2.1 * (dinv * (rho.2.2 * y.1 - rho.1.2 * y.2)) +
          rho.2.2 * (dinv * (-rho.2.1 * y.1 + rho.1.1 * y.2)) =
          dinv * coefficientDeterminant rho * y.2 by
            unfold coefficientDeterminant
            ring]
      rw [hinv, one_mul]

/-- Pullback of the canonical transverse rank-three normal form through an
arbitrary unit-transverse coefficient matrix. -/
abbrev TransverseCompatibleNormalForm {q e : ℕ}
    (rho : TransverseCoefficients q e) :=
  {b : PrimePowerBase q e //
    addOrderOf (coefficientMap rho b) =
      addOrderOf (coefficientMap rho b).2}

/-- The unit-transverse pullback is equivalent to the canonical dominant-base
normal form. -/
noncomputable def transverseNormalFormEquiv {q e : ℕ}
    (rho : TransverseCoefficients q e) (hrho : UnitTransverse rho) :
    TransverseCompatibleNormalForm rho ≃ DominantBase q e :=
  Equiv.subtypeEquiv (coefficientEquiv rho hrho) (fun _ => Iff.rfl)

/-- Exact rank-three prime-power count under the unit-transversality
hypothesis.  The type counted here is the finite normal form obtained after
the common scalar has been solved and forgotten. -/
theorem card_transverseNormalForm_primePower {q e : ℕ} [Fact q.Prime]
    (rho : TransverseCoefficients q e) (hrho : UnitTransverse rho) :
    Fintype.card (TransverseCompatibleNormalForm rho) =
      1 + (q * (q ^ (2 * e) - 1)) / (q + 1) := by
  rw [Fintype.card_congr (transverseNormalFormEquiv rho hrho)]
  exact card_dominantBase_primePower

/-- The unrestricted prime-power compatibility cardinality as an exact shell
sum.  This is the finite count underlying the rank-four Kummer density. -/
theorem card_compatible_shell_sum {q e : ℕ} [Fact q.Prime] :
    Fintype.card (CompatibleDatum q e) =
      1 + ∑ t ∈ Finset.range e,
        (q ^ (2 * (t + 1)) - q ^ (2 * t)) * q ^ (t + 1) := by
  classical
  let hq : q.Prime := Fact.out
  change Fintype.card ((b : PrimePowerBase q e) × AddSubgroup.zmultiples b) = _
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_zmultiples]
  rw [Fintype.sum_equiv (baseShellEquiv hq)
    (fun b : PrimePowerBase q e => addOrderOf b)
    (fun x : (t : Fin (e + 1)) × ExactOrderShell q e t.1 => q ^ x.1.1)
    (fun b => by
      calc
        addOrderOf b = addOrderOf ((baseShellEquiv hq).symm (baseShellEquiv hq b)) :=
          congrArg addOrderOf ((baseShellEquiv hq).left_inv b).symm
        _ = addOrderOf (baseShellEquiv hq b).2.1 := by
          rfl
        _ = q ^ (baseShellEquiv hq b).1.1 := (baseShellEquiv hq b).2.2)]
  rw [Fintype.sum_sigma]
  simp_rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  simp only [Nat.cast_id]
  rw [Fin.sum_univ_eq_sum_range (fun t =>
    Fintype.card (ExactOrderShell q e t) * q ^ t) (e + 1)]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [Fintype.card_congr (exactOrderShellZeroEquiv q e), Fintype.card_unique]
  rw [Nat.add_comm
    (∑ k ∈ Finset.range e,
      Fintype.card (ExactOrderShell q e (k + 1)) * q ^ (k + 1)) 1]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [card_exactOrderShell_succ]
  exact Finset.mem_range.mp ht

/-- A shell contribution in the form used by the geometric sum. -/
theorem shell_contribution_eq (q t : ℕ) :
    (q ^ (2 * (t + 1)) - q ^ (2 * t)) * q ^ (t + 1) =
      q * (q ^ 2 - 1) * q ^ (3 * t) := by
  have hexp : 2 * (t + 1) = 2 * t + 2 := by omega
  have hfactor : q ^ (2 * (t + 1)) - q ^ (2 * t) =
      q ^ (2 * t) * (q ^ 2 - 1) := by
    rw [hexp, pow_add]
    calc
      q ^ (2 * t) * q ^ 2 - q ^ (2 * t) =
          q ^ (2 * t) * q ^ 2 - q ^ (2 * t) * 1 := by simp
      _ = _ := (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hfactor]
  calc
    q ^ (2 * t) * (q ^ 2 - 1) * q ^ (t + 1) =
        (q ^ (2 * t) * q ^ (t + 1)) * (q ^ 2 - 1) := by ac_rfl
    _ = q ^ (3 * t + 1) * (q ^ 2 - 1) := by
      rw [← pow_add]
      congr 2
      omega
    _ = q * (q ^ 2 - 1) * q ^ (3 * t) := by
      rw [pow_add]
      simp only [pow_one]
      ac_rfl

/-- The same unrestricted count in geometric-sum form. -/
theorem card_compatible_geometric_sum {q e : ℕ} [Fact q.Prime] :
    Fintype.card (CompatibleDatum q e) =
      1 + q * (q ^ 2 - 1) *
        ∑ t ∈ Finset.range e, (q ^ 3) ^ t := by
  rw [card_compatible_shell_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simpa only [pow_mul] using shell_contribution_eq q t

/-- Closed form for the unrestricted prime-power compatibility count:
`1 + q(q²-1)(q^(3e)-1)/(q³-1)`. -/
theorem card_compatible_primePower {q e : ℕ} [Fact q.Prime] :
    Fintype.card (CompatibleDatum q e) =
      1 + (q * (q ^ 2 - 1) * (q ^ (3 * e) - 1)) / (q ^ 3 - 1) := by
  rw [card_compatible_geometric_sum]
  let hq : q.Prime := Fact.out
  have hcube : 2 ≤ q ^ 3 :=
    hq.two_le.trans (Nat.le_pow (by norm_num : 0 < 3))
  rw [Nat.geomSum_eq hcube e]
  rw [← pow_mul]
  have hdvd : q ^ 3 - 1 ∣ q ^ (3 * e) - 1 := by
    simpa [pow_mul] using
      Nat.pow_sub_one_dvd_pow_sub_one (q ^ 3) (one_dvd e)
  rw [← Nat.mul_div_assoc (q * (q ^ 2 - 1)) hdvd]

/-- Closed count in the direct common-scalar formulation over `ZMod (q^e)`. -/
theorem card_scalarCompatible_primePower {q e : ℕ} [Fact q.Prime] :
    Fintype.card (ScalarCompatibleDatum q e) =
      1 + (q * (q ^ 2 - 1) * (q ^ (3 * e) - 1)) / (q ^ 3 - 1) := by
  rw [Fintype.card_congr scalarCompatibleEquiv]
  exact card_compatible_primePower

end
end PrimePowerKummerCoherence
end LeanProofs.TwoBaseIntegerExponent
