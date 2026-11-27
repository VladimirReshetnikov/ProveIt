import IPRADerivations.Algebra.QuadraticTowerMultiplicationCommutativity

/-!
# The actual multiplicative unit at numerical tower depth

Both original multiplication queries with the constructed scalar one
return the SAME normalized original coefficient array. Original heights
imply the needed positive scalar bound. A genuine finite predicate is
proved along the actual multiplication state; its zero terms use the
independently proved zero-absorption predicate for that SAME state.
Raw input codes are never identified with their normalization.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationUnit

open_ipra
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open QuadraticTowerCoefficients (width singleton)
open QuadraticTowerArrayCodec (arrayHeight horizon code normalized)
open QuadraticTowerCoefficientArithmetic (added)
open QuadraticTowerScalarArrays (zeroArray zeroScalar scalarArray)
open QuadraticRationalEmbedding (oneScalar)
open QuadraticTowerMultiplicationTable (lookup budget recipe leftHalf rightHalf)
open QuadraticTowerMultiplicationHeight (radicandsHeight word cap state)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length append entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem array_height_floor (h A b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx] le one b :=
  le_trans (RationalArgmin.denominator_positive (entry A zero))
    (.andE₂ (QuadraticTowerArrayCodec.height_at h A b zero ha (QuadraticTowerScalarArrays.width_positive h)))

theorem one_canonical : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (oneScalar : PTm n) :=
  RationalNormalForm.normalize_well_formed _ one (le_refl _)
theorem one_recode : Γ ⊢[PRAAx] RationalArithmetic.recode (oneScalar : PTm n) ≐ oneScalar :=
  RationalNormalForm.normalize_fixed_point _ one_canonical
theorem one_height (b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] QuadraticTowerScalarBudget.height oneScalar b := by
  have mag : Γ ⊢[PRAAx] le (Foundations.GapDecision.zabs (ZT.ofNat (one : PTm n))) b :=
    le_congr ((congrAdd (monus_zero one) (zero_monus one)).eqTrans (add_zero one)).eqSymm (.eqRefl _) hb
  exact QuadraticTowerScalarBudget.normalize_height (ZT.ofNat one) one b (le_refl _) mag hb

theorem scalar_multiply_one (q : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.multiply q oneScalar ≐ RationalArithmetic.recode q := by
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) q oneScalar
    (numeratorOf q) (ZT.ofNat one) (denominatorOf q) one
      (RationalRepresentations.represents_self q) (QuadraticRationalPairArithmetic.scalar_represents one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalArithmetic.recode_guard _) rep (RationalArithmetic.recode_value q)
    (RationalAlgebra.positive_product (RationalArgmin.denominator_positive q) (le_refl one)) (RationalArgmin.denominator_positive q)
  ipra_lc

theorem scalar_one_multiply (q : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.multiply oneScalar q ≐ RationalArithmetic.recode q :=
  (RationalAlgebra.multiply_commutative _ _).eqTrans (scalar_multiply_one q)

theorem scalar_add_zero (q : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.add q zeroScalar ≐ RationalArithmetic.recode q := by
  have rep := RationalRepresentations.represents_add (Γ := Γ) q zeroScalar
    (numeratorOf q) (ZT.ofNat zero) (denominatorOf q) one
      (RationalRepresentations.represents_self q) (QuadraticRationalEmbedding.zero_scalar_represents one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalArithmetic.recode_guard _) rep (RationalArithmetic.recode_value q)
    (RationalAlgebra.positive_product (RationalArgmin.denominator_positive q) (le_refl one)) (RationalArgmin.denominator_positive q)
  ipra_lc

theorem added_zero_normalized (h A : PTm n) : Γ ⊢[PRAAx] added h A (zeroArray h) ≐ normalized h A := by
  apply sequence_equal QuadraticTowerCoefficientArithmetic.addBody QuadraticTowerArrayCodec.normalizeBody
    (width h) (pairT A (zeroArray h)) A
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have value : Δ ⊢[PRAAx] inst2 QuadraticTowerCoefficientArithmetic.addBody (var 0) (pairT (Syn.shift A) (zeroArray (Syn.shift h))) ≐
      RationalArithmetic.recode (entry (Syn.shift A) (var 0)) :=
    (QuadraticTowerCoefficientArithmetic.add_body_at _ _ _).eqTrans
      ((RationalAlgebra.add_congr (.eqRefl _) (QuadraticTowerScalarArrays.zero_lookup _ _ Prf.hyp0)).eqTrans (scalar_add_zero _))
  simpa only [Δ,Syn.shift,subst_pairT,QuadraticTowerScalarArrays.subst_zeroArray,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerArrayCodec.normalize_body_at] using value

theorem normalized_base (A : PTm n) : Γ ⊢[PRAAx] normalized zero A ≐ singleton (RationalArithmetic.recode (entry A zero)) := by
  have first : Γ ⊢[PRAAx] normalized zero A ≐ sequence QuadraticTowerArrayCodec.normalizeBody one A :=
    QuadraticTowerMultiplicationZero.sequence_congr _ QuadraticTowerCoefficients.width_zero (.eqRefl _)
  refine first.eqTrans (sequence_equal QuadraticTowerArrayCodec.normalizeBody (var 1) one A
    (RationalArithmetic.recode (entry A zero)) ?_)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) one :: Γ.map Fm.shift
  have iz : Δ ⊢[PRAAx] (var 0 : PTm (n+1)) ≐ zero :=
    le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) (zero_le _)
  have val := QuadraticTowerArrayNormalization.recode_congr (entry_congr (Γ := Δ) (.eqRefl (Syn.shift A)) iz)
  simpa only [Δ,inst2,QuadraticTowerArrayCodec.normalizeBody,Syn.subst_var,Matrix.cons_val_one,
    Matrix.cons_val_zero,Matrix.head_cons,RationalArithmetic.subst_recode,Foundations.MasterCertificate.subst_entry,
    Syn.shift,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using val

theorem normalized_join_at (h A i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width (succ h))) : Γ ⊢[PRAAx]
    entry (append (normalized h (leftHalf h A)) (normalized h (rightHalf h A))) i ≐ RationalArithmetic.recode (entry A i) := by
  refine .orE (lt_or_le i (width h)) ?_ ?_
  · have pos : (lt i (width h)) :: Γ ⊢[PRAAx] lt i (length (normalized h (leftHalf h A))) :=
      lt_congr (.eqRefl _) (Foundations.MasterCertificate.sequence_length _ _ _).eqSymm Prf.hyp0
    exact (Foundations.SequenceComposition.append_left pos).eqTrans
      ((QuadraticTowerArrayCodec.normalized_lookup _ _ _ Prf.hyp0).eqTrans
        (QuadraticTowerArrayNormalization.recode_congr ((Foundations.RealizerComposition.slice_lookup _ zero _ _ Prf.hyp0).eqTrans
          (entry_congr (.eqRefl _) (zero_add _)))))
  · let Δ := le (width h) i :: Γ
    have hj : Δ ⊢[PRAAx] lt (monus i (width h)) (width h) :=
      QuadraticTowerMultiplicationHeight.right_index_bound (width h) i
        (lt_congr (.eqRefl _) (QuadraticTowerCoefficients.width_succ h) hi.wk) Prf.hyp0
    have oldLength : Δ ⊢[PRAAx] length (normalized h (leftHalf h A)) ≐ width h := Foundations.MasterCertificate.sequence_length _ _ _
    have newLength : Δ ⊢[PRAAx] length (normalized h (rightHalf h A)) ≐ width h := Foundations.MasterCertificate.sequence_length _ _ _
    have place := (eq_add_of_le (Prf.hyp0 : Δ ⊢[PRAAx] le (width h) i)).eqTrans (congrAdd oldLength.eqSymm (.eqRefl _))
    have lookup := (entry_congr (Γ := Δ) (.eqRefl (append (normalized h (leftHalf h A)) (normalized h (rightHalf h A)))) place).eqTrans
      (Foundations.SequenceComposition.append_right (lt_congr (.eqRefl _) newLength.eqSymm hj))
    have value := (QuadraticTowerArrayCodec.normalized_lookup h (rightHalf h A) _ hj).eqTrans
      (QuadraticTowerArrayNormalization.recode_congr ((Foundations.RealizerComposition.slice_lookup A (width h) (width h) _ hj).eqTrans
        (entry_congr (.eqRefl _) (eq_add_of_le (Prf.hyp0 : Δ ⊢[PRAAx] le (width h) i)).eqSymm)))
    exact lookup.eqTrans value

theorem normalized_join (h A : PTm n) : Γ ⊢[PRAAx]
    append (normalized h (leftHalf h A)) (normalized h (rightHalf h A)) ≐ normalized (succ h) A := by
  have size : Γ ⊢[PRAAx] length (normalized h (leftHalf h A))+length (normalized h (rightHalf h A)) ≐ width (succ h) :=
    (congrAdd (Foundations.MasterCertificate.sequence_length _ _ _) (Foundations.MasterCertificate.sequence_length _ _ _)).eqTrans
      (QuadraticTowerCoefficients.width_succ h).eqSymm
  have first : Γ ⊢[PRAAx] append (normalized h (leftHalf h A)) (normalized h (rightHalf h A)) ≐
      sequence Foundations.SequenceComposition.appendBody (width (succ h))
        (pairT (normalized h (leftHalf h A)) (normalized h (rightHalf h A))) :=
    QuadraticTowerMultiplicationZero.sequence_congr _ size (.eqRefl _)
  refine first.eqTrans (sequence_equal Foundations.SequenceComposition.appendBody QuadraticTowerArrayCodec.normalizeBody
    (width (succ h)) (pairT (normalized h (leftHalf h A)) (normalized h (rightHalf h A))) A ?_)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (succ (Syn.shift h))) :: Γ.map Fm.shift
  have size : Δ ⊢[PRAAx] width (succ (Syn.shift h)) ≐
      length (normalized (Syn.shift h) (leftHalf (Syn.shift h) (Syn.shift A)))+
        length (normalized (Syn.shift h) (rightHalf (Syn.shift h) (Syn.shift A))) :=
    (QuadraticTowerCoefficients.width_succ _).eqTrans
      (congrAdd (Foundations.MasterCertificate.sequence_length _ _ _).eqSymm (Foundations.MasterCertificate.sequence_length _ _ _).eqSymm)
  have hi := lt_congr (Γ := Δ) (.eqRefl (var 0)) size Prf.hyp0
  have value := (QuadraticTowerMultiplicationZero.append_body_lookup _ _ _ hi).eqTrans (normalized_join_at _ _ _ Prf.hyp0)
  simpa only [Δ,Syn.shift,QuadraticTowerCoefficients.subst_width,ConciseIPRA.PTm.subst_succ,
    QuadraticTowerArrayCodec.normalize_body_at,QuadraticTowerArrayCodec.subst_normalized,
    QuadraticTowerMultiplicationTable.subst_leftHalf,QuadraticTowerMultiplicationTable.subst_rightHalf,subst_pairT] using value

def unitArray (h : PTm n) : PTm n := scalarArray h oneScalar
ipra_subst unitArray
theorem unit_height (h b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] arrayHeight h (unitArray h) b :=
  QuadraticTowerScalarArrays.scalar_array_height h oneScalar b hb (one_height b hb)
theorem unit_left (h : PTm n) : Γ ⊢[PRAAx] leftHalf h (unitArray (succ h)) ≐ unitArray h :=
  QuadraticTowerScalarArrays.left_scalar h oneScalar
theorem unit_right (h : PTm n) : Γ ⊢[PRAAx] rightHalf h (unitArray (succ h)) ≐ zeroArray h :=
  QuadraticTowerScalarArrays.right_scalar h oneScalar
theorem unit_at_zero (h : PTm n) : Γ ⊢[PRAAx] entry (unitArray h) zero ≐ oneScalar :=
  (QuadraticTowerScalarArrays.scalar_at_zero h oneScalar).eqTrans one_recode
theorem normalized_unit (h : PTm n) : Γ ⊢[PRAAx] normalized h (unitArray h) ≐ unitArray h :=
  QuadraticTowerScalarArrays.normalized_scalar h oneScalar

def rowLaw (h B D T b u : PTm n) : Fm PTm n := radicandsHeight D h b ⟶ arrayHeight h (word h b u) b ⟶
  lookup h B T (word h b u) (unitArray h) ≐ normalized h (word h b u)
def atHeight (h B D T b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ rowLaw (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localLaw (h B D T : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift B)) ⟶ atHeight (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (var 0))
ipra_subst rowLaw
@[simp] theorem subst_atHeight {k : ℕ} (σ : Fin n → PTm k) (h B D T b : PTm n) :
    (atHeight h B D T b).subst σ = atHeight (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ T) (Syn.subst σ b) := by
  simp [atHeight,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
ipra_subst localLaw [Syn.subst_shift, Syn.shift_subst]

def rowSyntax (h B D T b u : PTm n) : BFm n :=
  .imp (QuadraticTowerMultiplicationHeight.radicandsSyntax D h b)
    (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b u) b)
      (.eq (lookup h B T (word h b u) (unitArray h)) (normalized h (word h b u))))
def heightRowsSyntax (h B D T b : PTm n) : BFm n := .all (horizon h b)
  (rowSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localSyntax (h B D T : PTm n) : BFm n := .all (succ B)
  (heightRowsSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (var 0))
theorem row_formula (h B D T b u : PTm n) : formula (rowSyntax h B D T b u) = rowLaw h B D T b u := by
  simp [rowSyntax,rowLaw,formula,QuadraticTowerMultiplicationHeight.radicands_formula,
    QuadraticTowerMultiplicationHeight.height_formula]
theorem height_rows_formula (h B D T b : PTm n) : formula (heightRowsSyntax h B D T b) = atHeight h B D T b := by
  simp [heightRowsSyntax,atHeight,formula,row_formula]
theorem local_formula (h B D T : PTm n) : formula (localSyntax h B D T) = localLaw h B D T := by
  simp [localSyntax,localLaw,formula,height_rows_formula,Syn.shift]

theorem local_at (h B D T b u : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le b B) (hu : Γ ⊢[PRAAx] lt u (horizon h b))
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h (word h b u) b) : Γ ⊢[PRAAx]
    lookup h B T (word h b u) (unitArray h) ≐ normalized h (word h b u) := by
  have bg : Γ ⊢[PRAAx] lt b (succ B) ⟶ atHeight h B D T b := by simpa [localLaw] using hL.allE b
  have ug : Γ ⊢[PRAAx] lt u (horizon h b) ⟶ rowLaw h B D T b u := by
    simpa [atHeight] using (Prf.impE bg ((succ_monus_succ _ _).eqTrans hb)).allE u
  exact .impE (.impE (.impE ug hu) hD) ha

theorem lookup_unit (h B D T A b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    lookup h B T A (unitArray h) ≐ normalized h A := by
  have middle := local_at h B D T b (code h A b) hL hb (QuadraticTowerArrayCodec.code_bound h A b ha) hD
    (QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _))
  have av := QuadraticTowerMultiplicationCoherence.restored_values h A b ha
  exact (QuadraticTowerOperandProperness.lookup_proper h B T _ A _ _ av
    (QuadraticTowerMultiplicationZero.values_refl h (unitArray h))).eqSymm.eqTrans
      (middle.eqTrans (QuadraticTowerArrayNormalization.normalized_proper _ _ _ av))

theorem recipe_unit (h B D T A b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hZ : Γ ⊢[PRAAx] QuadraticTowerMultiplicationZero.localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    recipe h B T D A (unitArray (succ h)) ≐ normalized (succ h) A := by
  let K := budget h B D
  have h1 := array_height_floor (succ h) A b ha
  have bK := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path h) b)
    (QuadraticTowerGrowth.lower_path_budget h B D b hb)
  have rh := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have a0 := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have a1 := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have z0 := QuadraticTowerMultiplicationZero.lookup_zero h K D T (leftHalf h A) b hZ bK h1 rh a0
  have z1 := QuadraticTowerMultiplicationZero.lookup_zero h K D T (rightHalf h A) b hZ bK h1 rh a1
  have zd := QuadraticTowerMultiplicationZero.lookup_zero h K D T (entry D h) b hZ bK h1 rh
    (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h hD (le_refl _))
  have ac := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (.eqRefl (leftHalf h A)) (unit_left h)).eqTrans (lookup_unit h K D T _ b hL bK rh a0)
  have be := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (.eqRefl (rightHalf h A)) (unit_right h)).eqTrans (.andE₁ z1)
  have bed := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    be (.eqRefl (entry D h))).eqTrans (.andE₂ zd)
  have ae := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (.eqRefl (leftHalf h A)) (unit_right h)).eqTrans (.andE₁ z0)
  have bc := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
    (.eqRefl (rightHalf h A)) (unit_left h)).eqTrans (lookup_unit h K D T _ b hL bK rh a1)
  have low := (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) ac bed).eqTrans
    ((added_zero_normalized h _).eqTrans (QuadraticTowerArrayNormalization.normalized_idempotent h _))
  have high := (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl h) ae bc).eqTrans
    ((QuadraticTowerMultiplicationCommutativity.added_commutative h _ _).eqTrans
      ((added_zero_normalized h _).eqTrans (QuadraticTowerArrayNormalization.normalized_idempotent h _)))
  exact (QuadraticTowerCoefficients.append_congr low high).eqTrans (normalized_join h A)

theorem step_unit (h B D T A b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hZ : Γ ⊢[PRAAx] QuadraticTowerMultiplicationZero.localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A (unitArray (succ h)) ≐ normalized (succ h) A := by
  have ab := QuadraticTowerMultiplicationHeight.array_mono (succ h) A b B ha hb
  have ub := unit_height (Γ := Γ) (succ h) B (le_trans (array_height_floor (succ h) A b ha) hb)
  have first := QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D A (unitArray (succ h)) ab ub
  have reset := QuadraticTowerMultiplicationTable.recipe_congr (Γ := Γ) (.eqRefl h) (.eqRefl B) (.eqRefl T) (.eqRefl D)
    (.eqRefl (normalized (succ h) A)) (normalized_unit (succ h))
  exact first.eqTrans (reset.eqTrans
    ((recipe_unit h B D T _ b hL hZ hb hD (QuadraticTowerMultiplicationZero.normalized_height _ _ _ ha)).eqTrans
      (QuadraticTowerArrayNormalization.normalized_idempotent _ _)))

theorem base_unit (B A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (ha : Γ ⊢[PRAAx] arrayHeight zero A b) : Γ ⊢[PRAAx]
    lookup zero B (QuadraticTowerMultiplicationTable.base B) A (unitArray zero) ≐ normalized zero A := by
  have ab := QuadraticTowerMultiplicationHeight.array_mono zero A b B ha hb
  have ub := unit_height (Γ := Γ) zero B (le_trans (array_height_floor zero A b ha) hb)
  have mulUnit := (RationalAlgebra.multiply_congr (.eqRefl (entry A zero)) (unit_at_zero (Γ := Γ) zero)).eqTrans (scalar_multiply_one _)
  exact (QuadraticTowerMultiplicationCoherence.base_lookup_original B A (unitArray zero) ab ub).eqTrans
    ((QuadraticTowerMultiplicationZero.sequence_congr (var 1) (.eqRefl one) mulUnit).eqTrans (normalized_base A).eqSymm)

theorem local_base (B D : PTm n) : Γ ⊢[PRAAx] localLaw zero B D (QuadraticTowerMultiplicationTable.base B) := by
  refine .allI (.impI (.allI (.impI (.impI (.impI ?_)))))
  let B' := Syn.shift (Syn.shift B)
  let D' := Syn.shift (Syn.shift D)
  let b := (var 1 : PTm (n+2))
  let u := (var 0 : PTm (n+2))
  let Δ := arrayHeight zero (word zero b u) b :: radicandsHeight D' zero b ::
    lt u (horizon zero b) :: lt b (succ B') :: (Γ.map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero b u) b := Prf.hyp0
  have hr : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hr
  simpa [Δ,B',D',b,u,Fm.shift,Syn.shift] using base_unit B' (word zero b u) b hb ha

theorem local_step (h B D T : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hZ : Γ ⊢[PRAAx] QuadraticTowerMultiplicationZero.localLaw h (budget h B D) D T) : Γ ⊢[PRAAx]
    localLaw (succ h) B D (QuadraticTowerMultiplicationTable.step h B T D) := by
  have ls : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] localLaw (Syn.shift (Syn.shift h))
      (budget (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift D)))
        (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift T)) := by
    simpa only [Fm.shift,subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hL.shift.shift
  have zs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] QuadraticTowerMultiplicationZero.localLaw (Syn.shift (Syn.shift h))
      (budget (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift D)))
        (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift T)) := by
    simpa only [Fm.shift,QuadraticTowerMultiplicationZero.subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hZ.shift.shift
  refine .allI (.impI (.allI (.impI (.impI (.impI ?_)))))
  let h' := Syn.shift (Syn.shift h)
  let B' := Syn.shift (Syn.shift B)
  let D' := Syn.shift (Syn.shift D)
  let T' := Syn.shift (Syn.shift T)
  let b := (var 1 : PTm (n+2))
  let u := (var 0 : PTm (n+2))
  let Δ := arrayHeight (succ h') (word (succ h') b u) b :: radicandsHeight D' (succ h') b ::
    lt u (horizon (succ h') b) :: lt b (succ B') :: (Γ.map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b u) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := Prf.hyp1
  have hr : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hr
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') D' T' := ls.wk.wk.wk.wk
  have lowerZero : Δ ⊢[PRAAx] QuadraticTowerMultiplicationZero.localLaw h' (budget h' B' D') D' T' := zs.wk.wk.wk.wk
  simpa [Δ,h',B',D',T',b,u,Fm.shift,Syn.shift] using
    step_unit h' B' D' T' (word (succ h') b u) b lower lowerZero hb hd ha

theorem local_congr {h h' B B' D D' T T' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hb : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] D ≐ D') (ht : Γ ⊢[PRAAx] T ≐ T')
    (hL : Γ ⊢[PRAAx] localLaw h B D T) : Γ ⊢[PRAAx] localLaw h' B' D' T' := by
  have p := Prf.eqSubst (localLaw (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![h,B,D,T] ![h',B',D',T'] (fun i => by fin_cases i; exact hh; exact hb; exact hd; exact ht) (by simpa using hL)
  simpa using p

def forwardLaw (H B D t : PTm n) : Fm PTm n := le t H ⟶ localLaw t (cap H B t D) D (state H B t D)
def forwardSyntax (H B D t : PTm n) : BFm n := .imp (.le t H)
  (localSyntax t (cap H B t D) D (state H B t D))
ipra_subst forwardLaw
theorem forward_formula (H B D t : PTm n) : formula (forwardSyntax H B D t) = forwardLaw H B D t := by
  simp [forwardSyntax,forwardLaw,formula,local_formula,BFm.le,le]

theorem forward_zero (H B D : PTm n) : Γ ⊢[PRAAx] forwardLaw H B D zero :=
  .impI (local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (QuadraticTowerMultiplicationHeight.state_zero H B D).wk.eqSymm (local_base _ D))

theorem forward_step (H B D t : PTm n) (ih : Γ ⊢[PRAAx] forwardLaw H B D t) : Γ ⊢[PRAAx]
    forwardLaw H B D (succ t) := by
  refine QuadraticTowerMultiplicationHeight.forward_step_of_local localLaw H B D t local_congr ih ?_
  intro Δ ht adjusted
  have tle : Δ ⊢[PRAAx] le t H := le_trans (le_succ_self t) ht
  have zeroGate : Δ ⊢[PRAAx] QuadraticTowerMultiplicationZero.forwardLaw H B D t := by
    simpa only [QuadraticTowerMultiplicationZero.forward_formula,QuadraticTowerMultiplicationZero.subst_forwardLaw,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (QuadraticTowerMultiplicationZero.forward_all (Γ := Δ) H B D).allE t
  have zeroPrevious : Δ ⊢[PRAAx] QuadraticTowerMultiplicationZero.localLaw t (cap H B t D) D (state H B t D) :=
    .impE zeroGate tle
  have zeroAdjusted := QuadraticTowerMultiplicationZero.local_congr (.eqRefl _)
    (QuadraticTowerMultiplicationHeight.cap_link H B t D ht) (.eqRefl _) (.eqRefl _) zeroPrevious
  exact local_step t (cap H B (succ t) D) D (state H B t D) adjusted zeroAdjusted

/-- Actual fixed-depth/budget finite syntax, with one forward counter. -/
theorem forward_all (H B D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0))) := by
  refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
  · simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero (Γ := Γ) H B D
  · simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Γ := formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)) :: Γ.map Fm.shift)
        (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)
        (by simpa only [forward_formula] using (Prf.hyp0 (Ax := PRAAx)))

theorem table_unit_law (h B D : PTm n) : Γ ⊢[PRAAx] localLaw h B D (QuadraticTowerMultiplicationTable.table h B D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := Γ) h B D).allE h
  exact local_congr (.eqRefl _)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h B D)
    (.eqRefl _) (.eqRefl _) (Prf.impE gate (le_refl h))

theorem query_right_unit (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D A (unitArray h) ≐ normalized h A :=
  lookup_unit h B D _ A b (table_unit_law h B D) hb hD ha

theorem query_left_unit (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D (unitArray h) A ≐ normalized h A :=
  (QuadraticTowerMultiplicationCommutativity.query_commutative h B D (unitArray h) A b hb hD
    (unit_height h b (array_height_floor h A b ha)) ha).eqTrans (query_right_unit h B D A b hb hD ha)

theorem query_right_field_unit (h B D A U b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hu : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h U (unitArray h)) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D A U ≐ normalized h A :=
  (QuadraticTowerOperandProperness.query_operands_proper h B D A A U (unitArray h)
    (QuadraticTowerMultiplicationZero.values_refl h A) hu).eqTrans (query_right_unit h B D A b hb hD ha)
theorem query_left_field_unit (h B D A U b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hu : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h U (unitArray h)) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D U A ≐ normalized h A :=
  (QuadraticTowerOperandProperness.query_operands_proper h B D U (unitArray h) A A
    hu (QuadraticTowerMultiplicationZero.values_refl h A)).eqTrans (query_left_unit h B D A b hb hD ha)

def output (h B D A : PTm n) : PTm n := pairT
  (QuadraticTowerMultiplicationTable.query h B D A (unitArray h))
    (pairT (QuadraticTowerMultiplicationTable.query h B D (unitArray h) A) (pairT (normalized h A) (unitArray h)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (h B D A : PTm n) : PTm n := PTm.app outputF ![h,B,D,A]
ipra_subst output
ipra_subst run

theorem program_at (h B D A : PTm n) : Γ ⊢[PRAAx] run h B D A ≐ output h B D A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![h,B,D,A]
theorem returned_right (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A) ≐
    QuadraticTowerMultiplicationTable.query h B D A (unitArray h) :=
  (program_at _ _ _ _).fstE
theorem returned_tail (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A) ≐
    pairT (QuadraticTowerMultiplicationTable.query h B D (unitArray h) A) (pairT (normalized h A) (unitArray h)) :=
  (program_at _ _ _ _).sndE
theorem returned_left (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A)) ≐
    QuadraticTowerMultiplicationTable.query h B D (unitArray h) A :=
  (returned_tail _ _ _ _).fstE
theorem returned_arrays (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A)) ≐ pairT (normalized h A) (unitArray h) :=
  (returned_tail _ _ _ _).sndE
theorem returned_normalized (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h B D A))) ≐ normalized h A :=
  (returned_arrays _ _ _ _).fstE
theorem returned_unit (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h B D A))) ≐ unitArray h :=
  (returned_arrays _ _ _ _).sndE
theorem returned_identity (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    ((fstT (run h B D A) ≐ fstT (sndT (sndT (run h B D A)))) ⋏
      (fstT (sndT (run h B D A)) ≐ fstT (sndT (sndT (run h B D A))))) :=
  .andI ((returned_right _ _ _ _).eqTrans ((query_right_unit h B D A b hb hD ha).eqTrans (returned_normalized _ _ _ _).eqSymm))
    ((returned_left _ _ _ _).eqTrans ((query_left_unit h B D A b hb hD ha).eqTrans (returned_normalized _ _ _ _).eqSymm))

theorem actual_scalar_multiplicative_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((RationalArithmetic.multiply (var 0) oneScalar ≐ RationalArithmetic.recode (var 0)) ⋏
      (RationalArithmetic.multiply oneScalar (var 0) ≐ RationalArithmetic.recode (var 0))) :=
  closeUniv 1 (.andI (scalar_multiply_one _) (scalar_one_multiply _))
theorem actual_normalized_half_join_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (append (normalized (var 0) (leftHalf (var 0) (var 1))) (normalized (var 0) (rightHalf (var 0) (var 1))) ≐ normalized (succ (var 0)) (var 1)) :=
  closeUniv 2 (normalized_join _ _)
theorem actual_multiplication_unit_predicate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localLaw (var 0) (var 1) (var 2) (QuadraticTowerMultiplicationTable.table (var 0) (var 1) (var 2))) := closeUniv 3 (table_unit_law _ _ _)
theorem actual_finite_forward_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (forwardLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (by simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    (forward_all (Γ := ([] : List (Fm PTm 4))) (var 0) (var 1) (var 2)).allE (var 3))
theorem original_heights_actual_multiplicative_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 4) ⟶ arrayHeight (var 0) (var 3) (var 4) ⟶
      ((QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (unitArray (var 0)) ≐ normalized (var 0) (var 3)) ⋏
        (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (unitArray (var 0)) (var 3) ≐ normalized (var 0) (var 3)))) :=
  closeUniv 5 (.impI (.impI (.impI (.andI
    (query_right_unit _ _ _ _ (var 4) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)
    (query_left_unit _ _ _ _ (var 4) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem original_field_unit_operand_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 5) ⟶ arrayHeight (var 0) (var 3) (var 5) ⟶
      QuadraticTowerCoefficientArithmetic.equalValues (var 0) (var 4) (unitArray (var 0)) ⟶
        ((QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (var 4) ≐ normalized (var 0) (var 3)) ⋏
          (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 4) (var 3) ≐ normalized (var 0) (var 3)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.andI
    (query_right_field_unit _ _ _ _ _ (var 5) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)
    (query_left_field_unit _ _ _ _ _ (var 5) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))
theorem actual_multiplication_unit_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem original_returned_multiplicative_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 4) ⟶ arrayHeight (var 0) (var 3) (var 4) ⟶
      ((fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))) :=
  closeUniv 5 (.impI (.impI (.impI (returned_identity _ _ _ _ (var 4) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationUnit
