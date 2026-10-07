import OAI.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem principalCoefficientImage_family {Z K D α I J N : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H ℓ C U G : ℝ} (hH : 0 < H) (hℓ : 0 < ℓ)
    (hC0 : 0 ≤ C) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (rows : I → Finset α) (degree : ℕ)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
      ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
        Sum.elim zr (principalTupleNormalized L y) (input k a))
    (ctrl : ∀ y, (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0 →
      CoefficientFiberControl
        (Matrix.fromCols A (integerMappedJetMatrix e input zi rows (principalTupleIntegers y)))
        (s.trans Function.Embedding.inl) (Sum.elim S (fun n => H/monomialScale T (e n)))
        H ℓ degree C U G)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (ref : JointBlockParameter B h α → ℤ) (href : integerResidueMap _ m ref = principalTupleResidues r)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hC : C ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε ℓ degree ≤ H) :
    let E := normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) (fun _ => H)
      (fun i => hS (s i)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) (fun _ => H))
    let mask := coefficientResidueMultiplier A (integerResidueMatrix (integerMappedJetMatrix e input zi rows ref) m)
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w)
        (Sum.elim S (fun n => H/monomialScale T (e n))),
      (∀ v, 0 ≤ mask v ∧ mask v ≤ G) ∧
      ∀ y, (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0 → ∀ v,
        |H^Fintype.card I *
          (coefficientImagePMF
            (Matrix.fromCols A (integerMappedJetMatrix e input zi rows (principalTupleIntegers y)))
            (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
            (Sum.elim S (fun n => H/monomialScale T (e n)))
            (Sum.rec hS (fun n => div_pos hH (monomialScale_pos T hT (e n))))
            (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal -
          mask v * affineSelectedJetDensity s E F e input zr rows c w (principalTupleNormalized L y)
            (fun i => (v i : ℝ)/H)| ≤ ε := by
  dsimp only
  obtain ⟨hZ, hmask, herr⟩ := affineCoefficientImage_residue_family
    (principalResidueWeights B h L hL m hm r hsize) A s hA
    (fun y => integerMappedJetMatrix e input zi rows (principalTupleIntegers y))
    S (fun n => H/monomialScale T (e n)) hS (fun n => div_pos hH (monomialScale_pos T hT (e n)))
    degree ctrl hℓ hH hC0 hU0 hG0 c w hw hδ hwidth R hsupport hb ht hε hG hU hC hR hi hlarge
    m (integerResidueMatrix (integerMappedJetMatrix e input zi rows ref) m) hperiod
    (principalResidueWeights_matrix B h L hL m hm r hsize e input zi rows ref href)
  refine ⟨hZ, hmask, fun y hy v => ?_⟩
  have he := herr y hy v
  have hid := kernelCoefficientDensity_eq_jet A s hA S hS hH e input zr rows
    (principalTupleNormalized L y) (integerMappedCubeTuple input zi (principalTupleIntegers y)) T
    (integerMappedCubeTuple_normalized input zi (principalTupleIntegers y) zr
      (principalTupleNormalized L y) T (hn y)) c w
  simpa only [integerMappedJetMatrix, hid] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem jointPrincipalCoefficientImage_comparison {Q Z K D α : Type*}
    [Fintype Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {I J N : Q → Type*} [∀ q, Fintype (I q)] [∀ q, DecidableEq (I q)]
    [∀ q, Fintype (J q)] [∀ q, DecidableEq (J q)] [∀ q, Fintype (N q)] [∀ q, DecidableEq (N q)]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : ∀ q, Matrix (I q) (J q) ℤ) (s : ∀ q, I q ↪ J q)
    (hA : ∀ q, ((A q).submatrix id (s q)).det ≠ 0)
    (S : ∀ q, J q → ℝ) (hS : ∀ q j, 0 < S q j) (H ℓ C U : Q → ℝ) (G : ℝ)
    (hH : ∀ q, 0 < H q) (hℓ : ∀ q, 0 < ℓ q) (hC0 : ∀ q, 0 ≤ C q) (hU0 : ∀ q, 0 ≤ U q) (hG0 : 0 ≤ G)
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (rows : ∀ q, I q → Finset α) (degree : Q → ℕ)
    (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
    (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j) (δ R : Q → ℝ≥0)
    (hδ : ∀ q, 0 < δ q) (hwidth : ∀ q j, (δ q : ℝ) ≤ w q j)
    (hsupport : ∀ q j, |c q j|+w q j ≤ R q)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (hn : ∀ (y : PrincipalIntegerTuples B h α L) k a,
      ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
        Sum.elim zr (principalTupleNormalized L y) (input k a))
    (ctrl : ∀ q y, (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0 →
      CoefficientFiberControl
        (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
        ((s q).trans Function.Embedding.inl) (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
        (H q) (ℓ q) (degree q) (C q) (U q) G)
    (hperiod : ∀ q, integerScalarLattice (I q) (m : ℤ) ≤ (A q).mulVecLin.range)
    (ref : JointBlockParameter B h α → ℤ) (href : integerResidueMap _ m ref = principalTupleResidues r)
    (b t : Q → ℝ) {ε : ℝ} (hb : ∀ q, 0 ≤ b q) (ht : ∀ q, 0 ≤ t q) (hε : 0 < ε)
    (hG : ∀ q, G ≤ Real.exp (b q)) (hU : ∀ q, U q ≤ Real.exp (b q))
    (hC : ∀ q, C q ≤ Real.exp (b q)) (hR : ∀ q, (R q : ℝ) ≤ Real.exp (b q))
    (hi : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp (t q))
    (hlarge : ∀ q, coefficientReplacementScale (J := J q ⊕ N q)
      ((s q).trans Function.Embedding.inl) (b q) (t q) ε (ℓ q) (degree q) ≤ H q)
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap) :
    let E := fun q => normalizedPivotEquiv ((A q).submatrix id (s q)) (hA q)
      (fun i => S q (s q i)) (fun _ => H q) (fun i => hS q (s q i)) (fun _ => hH q)
    let F := fun q => matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A q) (s q))
      (fun j => S q j.val) (fun _ => H q))
    let mask := fun q => coefficientResidueMultiplier (A q)
      (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) ref) m)
    (∀ q, pivotKernelCap (UnselectedColumn (s q)) (E q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap) →
    (∀ q, pivotKernelLip (UnselectedColumn (s q)) (E q) (R q) (affineProductProfileLip (J q) (δ q)) *
      (Fintype.card (N q) * polynomialBoxLip (Fintype.card (JointBlockParameter B h α)) (degree q)
        (normalizedJetMass α (degree q))) * R q ≤ Lip) →
    ∃ hZ : ∀ q, 0 < coefficientWeightSum (affineProductProfile (c q) (w q))
        (Sum.elim (S q) (fun n => H q/monomialScale T (e q n))), ∀ v : ∀ q, I q → ℤ,
      |(principalResidueWeights B h L hL m hm r hsize).mean
        (fun y => (∏ q, H q^Fintype.card (I q)) *
          (dependentProductPMF (fun q => coefficientImagePMF
            (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
            (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
            (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
            (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
            (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q)) (hZ q)) v).toReal) -
        (∏ q, mask q (v q)) *
          (∫ x, jointAffineJetDensity s E F e input zr rows c w x (fun q i => (v q i : ℝ)/H q)
            ∂jointBooleanSource h)| ≤
        Fintype.card Q*ε*(1+G*Cap+ε)^Fintype.card Q +
          G^Fintype.card Q*jointTupleQuadratureError (α := α) B h (Fintype.card Q) Cap Lip L m := by
  classical
  dsimp only
  intro hcap hlip
  have hfamily (q : Q) := principalCoefficientImage_family B h (A q) (s q) (hA q) (S q) (hS q)
    (hH q) (hℓ q) (hC0 q) (hU0 q) hG0 (e q) input zi zr T hT (rows q) (degree q)
    (c q) (w q) (hw q) (hδ q) (hwidth q) (R q) (hsupport q) L hL m hm r hsize hn (ctrl q)
    (hperiod q) ref href (hb q) (ht q) hε (hG q) (hU q) (hC q) (hR q) (hi q) (hlarge q)
  choose hZ hmask herr using hfamily
  refine ⟨hZ, fun v => ?_⟩
  let E := fun q => normalizedPivotEquiv ((A q).submatrix id (s q)) (hA q)
    (fun i => S q (s q i)) (fun _ => H q) (fun i => hS q (s q i)) (fun _ => hH q)
  let F := fun q => matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (A q) (s q))
    (fun j => S q j.val) (fun _ => H q))
  have hreg (q : Q) (v : I q → ℤ) := affineSelectedJetDensity_bounds (s q) (E q) (F q) (e q)
    input zr hz (rows q) (hd q) (c q) (w q) (hw q) (hδ q) (fun j => hwidth q (.inl j))
    (R q) (hsupport q) (fun i => (v i : ℝ)/H q)
  apply jointCoefficient_principalTuple_comparison B h L hL m hm r hsize hsmall
    (fun y q => coefficientImagePMF
      (Matrix.fromCols (A q) (integerMappedJetMatrix (e q) input zi (rows q) (principalTupleIntegers y)))
      (affineProductProfile (c q) (w q)) (affineProductProfile_nonneg (c q) (w q) (hw q))
      (Sum.elim (S q) (fun n => H q/monomialScale T (e q n)))
      (Sum.rec (hS q) (fun n => div_pos (hH q) (monomialScale_pos T hT (e q n))))
      (affineProductProfile_zero_outside (c q) (w q) (hw q) (R q).coe_nonneg (hsupport q)) (hZ q))
    (fun q => H q^Fintype.card (I q))
    (fun q => coefficientResidueMultiplier (A q)
      (integerResidueMatrix (integerMappedJetMatrix (e q) input zi (rows q) ref) m))
    (fun x q v => affineSelectedJetDensity (s q) (E q) (F q) (e q) input zr (rows q) (c q) (w q)
      x (fun i => (v i : ℝ)/H q)) Cap Lip hCap hG0 hε.le
  · intro x q v
    exact ((hreg q v).1 x).trans (hcap q)
  · intro q v
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact ((hreg q v).2.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_right (show (_ : ℝ) ≤ Lip from hlip q) dist_nonneg)
  · exact hmask
  · intro y hy q v
    exact herr q y hy v

end Erdos3

end

end OAI
