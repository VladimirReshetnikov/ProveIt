import GowersSzemeredi.Proofs16IntegerClassesAll
import GowersSzemeredi.Proofs16AllDimensionsExplicit
import GowersSzemeredi.Proofs16IntegerBaseSourceBounds

/-! Theorem 16.2 with genuine integer boxes in every dimension.
The printed controls are retained over every prime modulus, without an
additional eventual-modulus threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def Theorem162IntegerAt (k : Nat) : Prop :=
  ∀ (gamma theta : Real), 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
    ∀ Gamma : Finset (Point N k × ZMod N),
      (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k →
      RelationProductProperty gamma Gamma →
      ∃ J : Finset (Point N k), (1 - theta) * (N : Real) ^ k ≤ J.card ∧
        let r := gamma ^ (-(2 : Int)) * multipleS theta gamma k
        IntegerMultiplyLinearWith
          (fun rho => (multipleQ (r⁻¹ * rho) gamma k) ^ r)
          (fun rho => (multipleC (r⁻¹ * rho) gamma k) ^ r) (restrictRelation Gamma J)

theorem theorem162IntegerAt_of_integerPolyCover_tower {k : Nat} {Qb Eb : Real → Real → Real → Real}
    (hcov : IntegerPolyCoverAt k Qb Eb) {W0 : Real} (hW0 : 1 ≤ W0)
    (hW0' : W0 ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat}
    (hD : D ≤ (2 : Nat) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))))
    (hQ : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → Qb gamma theta rho ≤ (W0 * (2 / (gamma * theta * rho))) ^ D)
    (hE : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → ((W0 * (2 / (gamma * theta * rho))) ^ D)⁻¹ ≤ Eb gamma theta rho) :
    Theorem162IntegerAt k := by
  intro gamma theta hg hg1 ht ht1 N _ _ Gamma hcard hprod
  obtain ⟨J, hJ, hML⟩ := hcov N gamma theta hg hg1 ht ht1 Gamma hcard hprod
  refine ⟨J, hJ, ?_⟩
  change IntegerMultiplyLinearWith
    (fun rho => (multipleQ ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
      (gamma ^ (-(2 : Int)) * multipleS theta gamma k))
    (fun rho => (multipleC ((gamma ^ (-(2 : Int)) * multipleS theta gamma k)⁻¹ * rho) gamma k) ^
      (gamma ^ (-(2 : Int)) * multipleS theta gamma k)) (restrictRelation Gamma J)
  refine hML.weaken ?_ ?_ ?_
  · intro rho hr hr1
    exact (hQ gamma theta rho hg hg1 ht ht1 hr hr1).trans
      (printed_controls_of_poly_tower hg hg1 ht ht1 hr hr1 hW0 hW0' hD).1
  · intro rho hr _
    have hs : 0 < gamma ^ (-(2 : Int)) * multipleS theta gamma k := by
      have := one_le_multipleS k ht ht1 hg hg1
      have hg2 : (0 : Real) < gamma ^ (-(2 : Int)) := zpow_pos hg _
      positivity
    exact Real.rpow_pos_of_pos (multipleC_pos k (by positivity) hg) _
  · intro rho hr hr1
    exact (printed_controls_of_poly_tower hg hg1 ht ht1 hr hr1 hW0 hW0' hD).2.trans
      (hE gamma theta rho hg hg1 ht ht1 hr hr1)

theorem PowerUniformClass.integerTheorem162At_tower {k : Nat} {V : Real} {dC dE dT : Nat}
    (C : PowerUniformClass k V dC dE dT) (hInt : C.IntegerCover) (hk : 0 < k) (hV : 1 ≤ V)
    (hVb : 2 * V ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat} (hDC : dC ≤ D)
    (hDE : dE ≤ D) (hDT : dT + k + 1 ≤ D) (hD : D ≤ (2 : Nat) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))) :
    Theorem162IntegerAt k := by
  have hbase : ∀ gamma theta rho : Real,
      uniformBase V 1 theta gamma rho = 2 * V * (2 / (gamma * theta * rho)) := by
    intro gamma theta rho; unfold uniformBase; push_cast; ring
  refine theorem162IntegerAt_of_integerPolyCover_tower (C.integerPolyCoverAt hInt hk hV hDC hDE hDT) (W0 := 2 * V)
    (by linarith) hVb hD ?_ ?_
  · intro gamma theta rho _ _ _ _ _ _
    rw [hbase]
  · intro gamma theta rho _ _ _ _ _ _
    rw [hbase]

theorem integerMultiplyLinear_relation_dimension_zero {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 0 × ZMod N)) {gamma r : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 1 ≤ r)
    (hcard : (Gamma.card : Real) ≤ r) : IntegerMultiplyLinearWith
      (fun theta => (multipleQ (r⁻¹ * theta) gamma 0) ^ r)
      (fun theta => (multipleC (r⁻¹ * theta) gamma 0) ^ r) Gamma := by
  classical
  let e : Fin Gamma.card ≃ {z // z ∈ Gamma} := Gamma.equivFin.symm
  apply IntegerMultiplyLinearWith.of_ascending
  intro theta ht ht1 P hP
  have hc : 0 < multipleC (r⁻¹ * theta) gamma 0 := pow_pos (by positivity) _
  have ha : 0 < (multipleC (r⁻¹ * theta) gamma 0) ^ r :=
    Real.rpow_pos_of_pos hc _
  refine ⟨1, Gamma.card, P.carrier, fun _ => P,
    fun _ i _ => (e i).val.2, Finset.Subset.rfl, ?_, ?_, fun _ => hP,
    hcard.trans (multipleQ_rpow_ge_parameter 0 hg hg1 ht ht1 hr), ?_,
    fun _ _ => isMultilinear_dimension_zero _, ?_⟩
  · have hnonneg : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · intro j
    have hw : P.width = 0 := by simp [Box.width]
    simp only [hw, Nat.cast_zero, Real.zero_rpow ha.ne', le_refl]
  · intro j x hxQ hxH y hxy
    refine ⟨e.symm ⟨(x, y), hxy⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]


theorem theorem_16_2_integer_zero : Theorem162IntegerAt 0 := by
  intro gamma theta hg hg1 ht ht1 N _ _ Gamma hcard hprod
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := one_le_gamma_inv_sq hg hg1
  have hs : 1 ≤ multipleS theta gamma 0 := one_le_multipleS 0 ht ht1 hg hg1
  have hgr : gamma ^ (-(2 : Int)) ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma 0 :=
    le_mul_of_one_le_right (zpow_nonneg hg.le _) hs
  refine ⟨Finset.univ, ?_, ?_⟩
  · simp only [pow_zero, mul_one, Finset.card_univ, Fintype.card_pi,
      Fin.prod_univ_zero, Nat.cast_one]
    linarith only [ht]
  · rw [restrictRelation_univ]
    have hcard' : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) := by
      simpa only [pow_zero, mul_one] using hcard
    exact integerMultiplyLinear_relation_dimension_zero Gamma hg hg1 (hginv.trans hgr)
      (hcard'.trans hgr)

def theorem_16_2_integer_representatives : Prop := ∀ k : Nat, Theorem162IntegerAt k

theorem theorem_16_2_integer_representatives_holds : theorem_16_2_integer_representatives := by
  let Kc (k : Nat) := Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
  let pc (k : Nat) := (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))
  have hK : ∀ k, 1 ≤ Kc k := fun k =>
    le_trans (by norm_num) (two_le_ceil_multiaffinePartitionK _ _)
  have hp : ∀ k, 0 < pc k := fun k =>
    Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _)
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) := by
    intro k _
    exact abstractFamilyLemma166At_of k (two_le_ceil_multiaffinePartitionK _ _) (hp k)
      (section16RecurrenceProfileWith_explicit k)
  have hIntegerLemma : ∀ k, 1 ≤ k → IntegerAbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k _ => integerAbstractFamilyLemma166At_explicit k
  have hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))) :=
    fun k => explicit_family_constants_le k
  intro k
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · exact theorem_16_2_integer_zero
    · intro gamma theta hg hg1 ht ht1 N _ _ Gamma hcard hprod
      simpa only [pow_one] using lemma_16_3_integer_representatives_holds N gamma theta hg hg1 ht ht1 Gamma
        (by simpa only [pow_one] using hcard) hprod
  · obtain ⟨C, hC⟩ := powerUniformClass_all_integer Kc pc hK hp hlem hIntegerLemma k hk
    exact C.integerTheorem162At_tower hC (by omega) (one_le_classV Kc pc k)
      (classV_bound Kc pc hconst hk) (D := classDeg k + k + 1)
      (by omega) (by omega) le_rfl (classDeg_add_le k)

end LeanProofs.GowersSzemeredi
