import IPRADerivations.Algebra.QuadraticTowerMultiplicationCoherence
import IPRADerivations.Algebra.QuadraticTowerScalarArrays

/-!
# Actual tower multiplication absorbs the constructed zero array

The original five-call multiplication table is used throughout. A finite
bounded invariant tracks both zero orientations along its actual forward
state. Original rational operand and radicand heights are the only local
legitimacy guards. Equality below concerns the actual canonical output
constructors; no extensionality of arbitrary outer list codes is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationZero

open_ipra
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open QuadraticTowerCoefficients (width singleton)
open QuadraticTowerArrayCodec (arrayHeight horizon code)
open QuadraticTowerCoefficientArithmetic (added)
open QuadraticTowerScalarArrays (zeroArray zeroScalar)
open QuadraticTowerMultiplicationTable (lookup budget recipe)
open QuadraticTowerMultiplicationHeight (radicandsHeight word cap state)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length append entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem scalar_multiply_zero (q : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply q zeroScalar ≐ zeroScalar := by
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) q zeroScalar
    (numeratorOf q) (ZT.ofNat zero) (denominatorOf q) one
      (RationalRepresentations.represents_self q) (QuadraticRationalEmbedding.zero_scalar_represents one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    QuadraticTowerScalarArrays.zero_canonical rep (QuadraticRationalEmbedding.zero_scalar_represents one)
    (RationalAlgebra.positive_product (RationalArgmin.denominator_positive q) (le_refl one)) (le_refl one)
  ipra_lc

theorem scalar_zero_multiply (q : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply zeroScalar q ≐ zeroScalar :=
  (RationalAlgebra.multiply_commutative _ _).eqTrans (scalar_multiply_zero q)

theorem scalar_add_zero_zero : Γ ⊢[PRAAx]
    RationalArithmetic.add (zeroScalar : PTm n) zeroScalar ≐ zeroScalar := by
  have rep := RationalRepresentations.represents_add (Γ := Γ) zeroScalar zeroScalar
    (ZT.ofNat zero) (ZT.ofNat zero) one one
      (QuadraticRationalEmbedding.zero_scalar_represents one) (QuadraticRationalEmbedding.zero_scalar_represents one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    QuadraticTowerScalarArrays.zero_canonical rep (QuadraticRationalEmbedding.zero_scalar_represents one)
    (RationalAlgebra.positive_product (le_refl one) (le_refl one)) (le_refl one)
  ipra_lc

theorem sequence_congr (f : PTm 2) {N M x y : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ M) (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    sequence f N x ≐ sequence f M y := by
  ipra_congr (sequence f (var 0) (var 1) : PTm 2) with [hN, hx]

theorem singleton_zero : Γ ⊢[PRAAx] singleton (zeroScalar : PTm n) ≐ zeroArray zero := by
  have eq : Γ ⊢[PRAAx] sequence (var 1) one zeroScalar ≐ sequence QuadraticTowerScalarArrays.zeroBody one zero := by
    apply sequence_equal
    refine .allI (.impI ?_)
    simp only [inst2,Syn.subst_var,Matrix.cons_val_one,QuadraticTowerScalarArrays.zeroBody,
      QuadraticTowerScalarArrays.subst_zeroScalar,Syn.shift]
    exact .eqRefl _
  exact eq.eqTrans (sequence_congr _ QuadraticTowerCoefficients.width_zero.eqSymm (.eqRefl _))

theorem added_zero (h : PTm n) : Γ ⊢[PRAAx] added h (zeroArray h) (zeroArray h) ≐ zeroArray h := by
  apply sequence_equal QuadraticTowerCoefficientArithmetic.addBody QuadraticTowerScalarArrays.zeroBody
    (width h) (pairT (zeroArray h) (zeroArray h)) zero
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have v : Δ ⊢[PRAAx] inst2 QuadraticTowerCoefficientArithmetic.addBody (var 0)
      (pairT (zeroArray (Syn.shift h)) (zeroArray (Syn.shift h))) ≐ zeroScalar :=
    (QuadraticTowerCoefficientArithmetic.add_body_at _ _ _).eqTrans
      ((RationalAlgebra.add_congr (QuadraticTowerScalarArrays.zero_lookup _ _ Prf.hyp0)
        (QuadraticTowerScalarArrays.zero_lookup _ _ Prf.hyp0)).eqTrans scalar_add_zero_zero)
  simpa only [Δ,Syn.shift,subst_pairT,QuadraticTowerScalarArrays.subst_zeroArray,
    QuadraticTowerScalarArrays.zero_body_at,QuadraticTowerCoefficients.subst_width] using v

theorem append_zero_at (h i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width (succ h))) : Γ ⊢[PRAAx]
    entry (append (zeroArray h) (zeroArray h)) i ≐ zeroScalar := by
  refine .orE (lt_or_le i (width h)) ?_ ?_
  · exact (Foundations.SequenceComposition.append_left
      (lt_congr (.eqRefl _) (QuadraticTowerScalarArrays.zero_length h).wk.eqSymm Prf.hyp0)).eqTrans
        (QuadraticTowerScalarArrays.zero_lookup _ _ Prf.hyp0)
  · have hj := QuadraticTowerMultiplicationHeight.right_index_bound (width h) i
      (lt_congr (.eqRefl _) (QuadraticTowerCoefficients.width_succ h) hi.wk) Prf.hyp0
    have eq := entry_congr (Γ := le (width h) i :: Γ) (.eqRefl (append (zeroArray h) (zeroArray h)))
      ((eq_add_of_le Prf.hyp0).eqTrans
        (congrAdd (QuadraticTowerScalarArrays.zero_length h).eqSymm (.eqRefl _)))
    exact eq.eqTrans ((Foundations.SequenceComposition.append_right
      (lt_congr (.eqRefl _) (QuadraticTowerScalarArrays.zero_length h).eqSymm hj)).eqTrans
        (QuadraticTowerScalarArrays.zero_lookup _ _ hj))

theorem append_body_lookup (A C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length A+length C)) : Γ ⊢[PRAAx]
    inst2 Foundations.SequenceComposition.appendBody i (pairT A C) ≐ entry (append A C) i :=
  (sequence_decode Foundations.SequenceComposition.appendBody hi).eqSymm

theorem append_zero (h : PTm n) : Γ ⊢[PRAAx] append (zeroArray h) (zeroArray h) ≐ zeroArray (succ h) := by
  have size : Γ ⊢[PRAAx] length (zeroArray h)+length (zeroArray h) ≐ width (succ h) :=
    (congrAdd (QuadraticTowerScalarArrays.zero_length h) (QuadraticTowerScalarArrays.zero_length h)).eqTrans
      (QuadraticTowerCoefficients.width_succ h).eqSymm
  have first : Γ ⊢[PRAAx] append (zeroArray h) (zeroArray h) ≐
      sequence Foundations.SequenceComposition.appendBody (width (succ h)) (pairT (zeroArray h) (zeroArray h)) :=
    sequence_congr _ size (.eqRefl _)
  refine first.eqTrans (sequence_equal Foundations.SequenceComposition.appendBody QuadraticTowerScalarArrays.zeroBody
    (width (succ h)) (pairT (zeroArray h) (zeroArray h)) zero ?_)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (succ (Syn.shift h))) :: Γ.map Fm.shift
  have ss : Δ ⊢[PRAAx] width (succ (Syn.shift h)) ≐ length (zeroArray (Syn.shift h))+length (zeroArray (Syn.shift h)) :=
    (QuadraticTowerCoefficients.width_succ _).eqTrans
      (congrAdd (QuadraticTowerScalarArrays.zero_length _).eqSymm (QuadraticTowerScalarArrays.zero_length _).eqSymm)
  have hi : Δ ⊢[PRAAx] lt (var 0) (length (zeroArray (Syn.shift h))+length (zeroArray (Syn.shift h))) :=
    lt_congr (.eqRefl _) ss Prf.hyp0
  have value : Δ ⊢[PRAAx] inst2 Foundations.SequenceComposition.appendBody (var 0)
      (pairT (zeroArray (Syn.shift h)) (zeroArray (Syn.shift h))) ≐ zeroScalar :=
    (append_body_lookup _ _ _ hi).eqTrans (append_zero_at _ _ Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_pairT,QuadraticTowerScalarArrays.subst_zeroArray,
    QuadraticTowerScalarArrays.zero_body_at,QuadraticTowerCoefficients.subst_width,ConciseIPRA.PTm.subst_succ] using value

def rowLaw (h B D T b u : PTm n) : Fm PTm n := le one b ⟶ radicandsHeight D h b ⟶
  arrayHeight h (word h b u) b ⟶
    ((lookup h B T (word h b u) (zeroArray h) ≐ zeroArray h) ⋏
      (lookup h B T (zeroArray h) (word h b u) ≐ zeroArray h))
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

def rowSyntax (h B D T b u : PTm n) : BFm n := .imp (.le one b)
  (.imp (QuadraticTowerMultiplicationHeight.radicandsSyntax D h b)
    (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b u) b)
      (.and (.eq (lookup h B T (word h b u) (zeroArray h)) (zeroArray h))
        (.eq (lookup h B T (zeroArray h) (word h b u)) (zeroArray h)))))
def heightRowsSyntax (h B D T b : PTm n) : BFm n := .all (horizon h b)
  (rowSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localSyntax (h B D T : PTm n) : BFm n := .all (succ B)
  (heightRowsSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (var 0))
theorem row_formula (h B D T b u : PTm n) : formula (rowSyntax h B D T b u) = rowLaw h B D T b u := by
  simp [rowSyntax,rowLaw,formula,QuadraticTowerMultiplicationHeight.radicands_formula,
    QuadraticTowerMultiplicationHeight.height_formula,BFm.le,le]
theorem height_rows_formula (h B D T b : PTm n) : formula (heightRowsSyntax h B D T b) = atHeight h B D T b := by
  simp [heightRowsSyntax,atHeight,formula,row_formula]
theorem local_formula (h B D T : PTm n) : formula (localSyntax h B D T) = localLaw h B D T := by
  simp [localSyntax,localLaw,formula,height_rows_formula,Syn.shift]

theorem values_refl (h A : PTm n) : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h A A := by
  refine .allI (.impI ?_)
  exact .eqRefl _

theorem local_at (h B D T b u : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le b B) (hu : Γ ⊢[PRAAx] lt u (horizon h b)) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h (word h b u) b) : Γ ⊢[PRAAx]
    ((lookup h B T (word h b u) (zeroArray h) ≐ zeroArray h) ⋏
      (lookup h B T (zeroArray h) (word h b u) ≐ zeroArray h)) := by
  have bg : Γ ⊢[PRAAx] lt b (succ B) ⟶ atHeight h B D T b := by simpa [localLaw] using hL.allE b
  have ug : Γ ⊢[PRAAx] lt u (horizon h b) ⟶ rowLaw h B D T b u := by
    simpa [atHeight] using (Prf.impE bg (Order.lt_succ_of_le hb)).allE u
  exact .impE (.impE (.impE (.impE ug hu) h1) hD) ha

theorem lookup_zero (h B D T A b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    ((lookup h B T A (zeroArray h) ≐ zeroArray h) ⋏
      (lookup h B T (zeroArray h) A ≐ zeroArray h)) := by
  have middle := local_at h B D T b (code h A b) hL hb (QuadraticTowerArrayCodec.code_bound h A b ha) h1 hD
    (QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _))
  have av := QuadraticTowerMultiplicationCoherence.restored_values h A b ha
  have zv := values_refl (Γ := Γ) h (zeroArray h)
  exact .andI ((QuadraticTowerOperandProperness.lookup_proper h B T _ A _ _ av zv).eqSymm.eqTrans (.andE₁ middle))
    ((QuadraticTowerOperandProperness.lookup_proper h B T _ _ _ A zv av).eqSymm.eqTrans (.andE₂ middle))

theorem recipe_zero (h B D T A b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    ((recipe h B T D A (zeroArray (succ h)) ≐ zeroArray (succ h)) ⋏
      (recipe h B T D (zeroArray (succ h)) A ≐ zeroArray (succ h))) := by
  let K := budget h B D
  have bK := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path h) b)
    (QuadraticTowerGrowth.lower_path_budget h B D b hb)
  have rh := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have az := lookup_zero h K D T (QuadraticTowerMultiplicationTable.leftHalf h A) b hL bK h1 rh
    (QuadraticTowerMultiplicationHeight.left_height h A b ha)
  have bz := lookup_zero h K D T (QuadraticTowerMultiplicationTable.rightHalf h A) b hL bK h1 rh
    (QuadraticTowerMultiplicationHeight.right_height h A b ha)
  have dz := lookup_zero h K D T (entry D h) b hL bK h1 rh
    (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h hD (le_refl _))
  have lz := QuadraticTowerScalarArrays.left_zero (Γ := Γ) h
  have rz := QuadraticTowerScalarArrays.right_zero (Γ := Γ) h
  have rr : Γ ⊢[PRAAx] recipe h B T D A (zeroArray (succ h)) ≐
      append (added h (zeroArray h) (zeroArray h)) (added h (zeroArray h) (zeroArray h)) := by
    have ac := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      (.eqRefl _) lz).eqTrans (.andE₁ az)
    have be := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      (.eqRefl _) rz).eqTrans (.andE₁ bz)
    have bed := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      be (.eqRefl _)).eqTrans (.andE₂ dz)
    have ae := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      (.eqRefl _) rz).eqTrans (.andE₁ az)
    have bc := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      (.eqRefl _) lz).eqTrans (.andE₁ bz)
    exact QuadraticTowerCoefficients.append_congr (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _) ac bed)
      (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _) ae bc)
  have ll : Γ ⊢[PRAAx] recipe h B T D (zeroArray (succ h)) A ≐
      append (added h (zeroArray h) (zeroArray h)) (added h (zeroArray h) (zeroArray h)) := by
    have ac := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      lz (.eqRefl _)).eqTrans (.andE₂ az)
    have be := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      rz (.eqRefl _)).eqTrans (.andE₂ bz)
    have bed := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      be (.eqRefl _)).eqTrans (.andE₂ dz)
    have ae := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      lz (.eqRefl _)).eqTrans (.andE₂ bz)
    have bc := (QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl K) (.eqRefl T)
      rz (.eqRefl _)).eqTrans (.andE₂ az)
    exact QuadraticTowerCoefficients.append_congr (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _) ac bed)
      (QuadraticTowerCoefficientArithmetic.added_congr (.eqRefl _) ae bc)
  have out : Γ ⊢[PRAAx] append (added h (zeroArray h) (zeroArray h)) (added h (zeroArray h) (zeroArray h)) ≐ zeroArray (succ h) :=
    (QuadraticTowerCoefficients.append_congr (added_zero h) (added_zero h)).eqTrans (append_zero h)
  exact .andI (rr.eqTrans out) (ll.eqTrans out)

theorem normalized_height (h A b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    arrayHeight h (QuadraticTowerArrayCodec.normalized h A) b :=
  QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _)
    (QuadraticTowerArrayNormalization.restored_normalized h A b ha) (.eqRefl _)
      (QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _))

theorem step_zero (h B D T A b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T)
    (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    ((lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) A (zeroArray (succ h)) ≐ zeroArray (succ h)) ⋏
      (lookup (succ h) B (QuadraticTowerMultiplicationTable.step h B T D) (zeroArray (succ h)) A ≐ zeroArray (succ h))) := by
  have ab := QuadraticTowerMultiplicationHeight.array_mono (succ h) A b B ha hb
  have zb := QuadraticTowerScalarArrays.zero_array_height (succ h) B (le_trans h1 hb)
  have z := QuadraticTowerScalarArrays.normalized_zero (Γ := Γ) (succ h)
  have result := recipe_zero h B D T (QuadraticTowerArrayCodec.normalized (succ h) A) b hL hb h1 hD
    (normalized_height (succ h) A b ha)
  have right := (QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D A (zeroArray (succ h)) ab zb).eqTrans
    ((QuadraticTowerMultiplicationTable.recipe_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (.eqRefl _) z).eqTrans (.andE₁ result))
  have left := (QuadraticTowerMultiplicationCoherence.step_lookup_normalized h B T D (zeroArray (succ h)) A zb ab).eqTrans
    ((QuadraticTowerMultiplicationTable.recipe_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      z (.eqRefl _)).eqTrans (.andE₂ result))
  exact .andI right left

theorem base_zero (B A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (ha : Γ ⊢[PRAAx] arrayHeight zero A b) : Γ ⊢[PRAAx]
    ((lookup zero B (QuadraticTowerMultiplicationTable.base B) A (zeroArray zero) ≐ zeroArray zero) ⋏
      (lookup zero B (QuadraticTowerMultiplicationTable.base B) (zeroArray zero) A ≐ zeroArray zero)) := by
  have ab := QuadraticTowerMultiplicationHeight.array_mono zero A b B ha hb
  have zb := QuadraticTowerScalarArrays.zero_array_height (Γ := Γ) zero B (le_trans h1 hb)
  have zr := QuadraticTowerScalarArrays.zero_at_zero (Γ := Γ) zero
  have sr := (RationalAlgebra.multiply_congr (.eqRefl (entry A zero)) zr).eqTrans (scalar_multiply_zero _)
  have sl := (RationalAlgebra.multiply_congr zr (.eqRefl (entry A zero))).eqTrans (scalar_zero_multiply _)
  have right := (QuadraticTowerMultiplicationCoherence.base_lookup_original B A (zeroArray zero) ab zb).eqTrans
    ((sequence_congr (var 1) (.eqRefl one) sr).eqTrans singleton_zero)
  have left := (QuadraticTowerMultiplicationCoherence.base_lookup_original B (zeroArray zero) A zb ab).eqTrans
    ((sequence_congr (var 1) (.eqRefl one) sl).eqTrans singleton_zero)
  exact .andI right left

theorem local_base (B D : PTm n) : Γ ⊢[PRAAx] localLaw zero B D (QuadraticTowerMultiplicationTable.base B) := by
  refine .allI (.impI (.allI (.impI (.impI (.impI (.impI ?_))))))
  let B' := Syn.shift (Syn.shift B)
  let D' := Syn.shift (Syn.shift D)
  let b := (var 1 : PTm (n+2))
  let u := (var 0 : PTm (n+2))
  let Δ := arrayHeight zero (word zero b u) b :: radicandsHeight D' zero b :: le one b ::
    lt u (horizon zero b) :: lt b (succ B') :: (Γ.map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero b u) b := Prf.hyp0
  have h1 : Δ ⊢[PRAAx] le one b := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := Order.le_of_lt_succ (.hyp (by simp [Δ]))
  simpa [Δ,B',D',b,u,Fm.shift,Syn.shift] using base_zero B' (word zero b u) b hb h1 ha

theorem local_step (h B D T : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T) : Γ ⊢[PRAAx]
    localLaw (succ h) B D (QuadraticTowerMultiplicationTable.step h B T D) := by
  have ls := hL.shift.shift
  simp only [Fm.shift, subst_localLaw, QuadraticTowerMultiplicationTable.subst_budget] at ls
  refine .allI (.impI (.allI (.impI (.impI (.impI (.impI ?_))))))
  let h' := Syn.shift (Syn.shift h)
  let B' := Syn.shift (Syn.shift B)
  let D' := Syn.shift (Syn.shift D)
  let T' := Syn.shift (Syn.shift T)
  let b := (var 1 : PTm (n+2))
  let u := (var 0 : PTm (n+2))
  let Δ := arrayHeight (succ h') (word (succ h') b u) b :: radicandsHeight D' (succ h') b :: le one b ::
    lt u (horizon (succ h') b) :: lt b (succ B') :: (Γ.map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b u) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := Prf.hyp1
  have h1 : Δ ⊢[PRAAx] le one b := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := Order.le_of_lt_succ (.hyp (by simp [Δ]))
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') D' T' :=
    ls.weaken (by intro φ hφ; simp only [Δ, List.mem_cons, hφ, or_true])
  simpa [Δ,h',B',D',T',b,u,Fm.shift,Syn.shift] using
    step_zero h' B' D' T' (word (succ h') b u) b lower hb h1 hd ha

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
    forwardLaw H B D (succ t) :=
  QuadraticTowerMultiplicationHeight.forward_step_of_local localLaw H B D t local_congr ih (fun _ adjusted =>
    local_step t (cap H B (succ t) D) D (state H B t D) adjusted)

/-- The entire finite zero-absorption predicate is compiled before induction. -/
theorem forward_all (H B D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0))) := by
  refine Foundations.BoundedSyntaxInduction.induction_of_formula _ (forward_formula _ _ _ _) ?_ ?_
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero (Γ := Γ) H B D
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0) (Prf.hyp0 (Γ := Γ.map Fm.shift))

theorem table_zero_law (h B D : PTm n) : Γ ⊢[PRAAx] localLaw h B D (QuadraticTowerMultiplicationTable.table h B D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := Γ) h B D).allE h
  have terminal := Prf.impE gate (le_refl h)
  exact local_congr (.eqRefl _)
    (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h B D)
    (.eqRefl _) (.eqRefl _) terminal

theorem query_zero_absorption (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    ((QuadraticTowerMultiplicationTable.query h B D A (zeroArray h) ≐ zeroArray h) ⋏
      (QuadraticTowerMultiplicationTable.query h B D (zeroArray h) A ≐ zeroArray h)) :=
  lookup_zero h B D _ A b (table_zero_law h B D) hb h1 hD ha

theorem query_right_zero (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D A (zeroArray h) ≐ zeroArray h :=
  .andE₁ (query_zero_absorption h B D A b hb h1 hD ha)
theorem query_left_zero (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D (zeroArray h) A ≐ zeroArray h :=
  .andE₂ (query_zero_absorption h B D A b hb h1 hD ha)

/-- Any raw operand representing coefficient-wise zero gives the same
actual query. No height or outer-code equality of that zero operand is
needed for the existing same-cap address-properness theorem. -/
theorem query_right_field_zero (h B D A Z b : PTm n)
    (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hz : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h Z (zeroArray h)) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D A Z ≐ zeroArray h :=
  (QuadraticTowerOperandProperness.query_operands_proper h B D A A Z (zeroArray h) (values_refl h A) hz).eqTrans
    (query_right_zero h B D A b hb h1 hD ha)
theorem query_left_field_zero (h B D A Z b : PTm n)
    (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hz : Γ ⊢[PRAAx] QuadraticTowerCoefficientArithmetic.equalValues h Z (zeroArray h)) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.query h B D Z A ≐ zeroArray h :=
  (QuadraticTowerOperandProperness.query_operands_proper h B D Z (zeroArray h) A A hz (values_refl h A)).eqTrans
    (query_left_zero h B D A b hb h1 hD ha)

def output (h B D A : PTm n) : PTm n := pairT
  (QuadraticTowerMultiplicationTable.query h B D A (zeroArray h))
    (pairT (QuadraticTowerMultiplicationTable.query h B D (zeroArray h) A) (zeroArray h))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (h B D A : PTm n) : PTm n := PTm.app outputF ![h,B,D,A]
ipra_subst output
ipra_subst run

theorem program_at (h B D A : PTm n) : Γ ⊢[PRAAx] run h B D A ≐ output h B D A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![h,B,D,A]
theorem returned_right (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A) ≐
    QuadraticTowerMultiplicationTable.query h B D A (zeroArray h) :=
  (program_at _ _ _ _).fstE
theorem returned_tail (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A) ≐
    pairT (QuadraticTowerMultiplicationTable.query h B D (zeroArray h) A) (zeroArray h) :=
  (program_at _ _ _ _).sndE
theorem returned_left (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A)) ≐
    QuadraticTowerMultiplicationTable.query h B D (zeroArray h) A :=
  (returned_tail _ _ _ _).fstE
theorem returned_zero (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A)) ≐ zeroArray h :=
  (returned_tail _ _ _ _).sndE
theorem returned_absorption (h B D A b : PTm n)
    (hb : Γ ⊢[PRAAx] le b B) (h1 : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    ((fstT (run h B D A) ≐ sndT (sndT (run h B D A))) ⋏
      (fstT (sndT (run h B D A)) ≐ sndT (sndT (run h B D A)))) :=
  .andI ((returned_right _ _ _ _).eqTrans ((query_right_zero h B D A b hb h1 hD ha).eqTrans (returned_zero _ _ _ _).eqSymm))
    ((returned_left _ _ _ _).eqTrans ((query_left_zero h B D A b hb h1 hD ha).eqTrans (returned_zero _ _ _ _).eqSymm))

theorem actual_scalar_zero_absorption_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((RationalArithmetic.multiply (var 0) zeroScalar ≐ zeroScalar) ⋏
      (RationalArithmetic.multiply zeroScalar (var 0) ≐ zeroScalar)) :=
  closeUniv 1 (.andI (scalar_multiply_zero _) (scalar_zero_multiply _))
theorem actual_constructed_zero_join_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (append (zeroArray (var 0)) (zeroArray (var 0)) ≐ zeroArray (succ (var 0))) := closeUniv 1 (append_zero _)
theorem actual_zero_absorption_table_predicate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localLaw (var 0) (var 1) (var 2) (QuadraticTowerMultiplicationTable.table (var 0) (var 1) (var 2))) :=
  closeUniv 3 (table_zero_law _ _ _)
theorem actual_finite_forward_zero_absorption_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (forwardLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (by simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    (forward_all (Γ := ([] : List (Fm PTm 4))) (var 0) (var 1) (var 2)).allE (var 3))
theorem original_height_actual_zero_absorption_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ le one (var 4) ⟶ radicandsHeight (var 2) (var 0) (var 4) ⟶ arrayHeight (var 0) (var 3) (var 4) ⟶
      ((QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (zeroArray (var 0)) ≐ zeroArray (var 0)) ⋏
        (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (zeroArray (var 0)) (var 3) ≐ zeroArray (var 0)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (query_zero_absorption _ _ _ _ (var 4) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem original_field_zero_operand_absorption_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ le one (var 5) ⟶ radicandsHeight (var 2) (var 0) (var 5) ⟶ arrayHeight (var 0) (var 3) (var 5) ⟶
      QuadraticTowerCoefficientArithmetic.equalValues (var 0) (var 4) (zeroArray (var 0)) ⟶
        ((QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zeroArray (var 0)) ⋏
          (QuadraticTowerMultiplicationTable.query (var 0) (var 1) (var 2) (var 4) (var 3) ≐ zeroArray (var 0)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.andI
    (query_right_field_zero _ _ _ _ _ (var 5) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)
    (query_left_field_zero _ _ _ _ _ (var 5) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))))
theorem actual_zero_absorption_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem original_returned_zero_absorption_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ le one (var 4) ⟶ radicandsHeight (var 2) (var 0) (var 4) ⟶ arrayHeight (var 0) (var 3) (var 4) ⟶
      ((fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (returned_absorption _ _ _ _ (var 4) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationZero
