import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3

theorem kernelJetInterpolationAllowance_le_exp (q h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    kernelJetInterpolationAllowance q h κ ≤
      Real.exp ((h : ℝ) * ((q : ℝ)^2 + q + b + 2)) := by
  have hq : (q : ℝ) ≤ Real.exp q := by linarith [Real.add_one_le_exp (q : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hterm : (q : ℝ) * (2 * (q.factorial / κ)) ≤
      Real.exp ((q : ℝ)^2 + q + b + 1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp q * (Real.exp 1 * (Real.exp ((q : ℝ)^2) * Real.exp b)) := by
        gcongr
        exact factorial_le_exp_sq q
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have he : 1 ≤ Real.exp ((q : ℝ)^2 + q + b + 1) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hbase : 1 + (q : ℝ) * (2 * (q.factorial / κ)) ≤
      Real.exp ((q : ℝ)^2 + q + b + 2) := by
    calc
      _ ≤ 2 * Real.exp ((q : ℝ)^2 + q + b + 1) := by linarith
      _ ≤ Real.exp 1 * Real.exp ((q : ℝ)^2 + q + b + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  unfold kernelJetInterpolationAllowance
  calc
    _ ≤ (Real.exp ((q : ℝ)^2 + q + b + 2)) ^ h := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem kernelJetEntryAllowance_le_exp (q h : ℕ) :
    kernelJetEntryAllowance q h ≤ Real.exp ((q : ℝ) * (h + 1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq := Real.add_one_le_exp (q : ℝ)
  unfold kernelJetEntryAllowance
  calc
    _ ≤ (Real.exp 1) ^ q * (Real.exp q) ^ h := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem kernelJetMinorThreshold_inv_le_exp (q n j h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    (kernelJetMinorThreshold q n j h κ)⁻¹ ≤
      Real.exp ((j : ℝ) * (h * n + h * ((q : ℝ)^2 + q + b + 2))) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hQ := kernelJetInterpolationAllowance_le_exp q h hκ hb hi
  have hQpos := (kernelJetInterpolationAllowance_pos q h hκ).le
  simp only [kernelJetMinorThreshold, one_div, inv_inv]
  calc
    _ ≤ ((Real.exp n) ^ h *
        Real.exp ((h : ℝ) * ((q : ℝ)^2 + q + b + 2))) ^ j := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]

theorem kernelJetInverseAllowance_le_exp (q n j h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    kernelJetInverseAllowance q n j h κ ≤
      Real.exp ((j : ℝ) + (j : ℝ)^2 +
        (j - 1 : ℕ) * ((q : ℝ) * (h + 1)) +
        j * (h * n + h * ((q : ℝ)^2 + q + b + 2))) := by
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hE := kernelJetEntryAllowance_le_exp q h
  have hEin := (kernelJetEntryAllowance_pos q h).le
  have hminor := kernelJetMinorThreshold_inv_le_exp q n j h hκ hb hi
  have hminorpos := (kernelJetMinorThreshold_pos q n j h hκ).le
  unfold kernelJetInverseAllowance
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp j * ((Real.exp ((j : ℝ)^2) *
        (Real.exp ((q : ℝ) * (h + 1))) ^ (j - 1)) *
        Real.exp ((j : ℝ) * (h * n + h * ((q : ℝ)^2 + q + b + 2)))) := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

theorem goodKernel_common_period {Q α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J]
    {O : Q → Type*} [∀ q, Fintype (O q)]
    {L B : ℕ} {κ : ℝ} (selection : α ↪ J)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (smax : ℕ) (hsmax : 1 ≤ smax) (degree : Q → ℕ) (hdegree : ∀ q, degree q ≤ smax)
    (rows : ∀ q, O q → Finset α) (hinj : ∀ q, Function.Injective (rows q))
    (hrows : ∀ q i, (rows q i).card ≤ degree q) :
    ∃ m : ℕ, 0 < m ∧ m ≤ B^smax ∧
      (∀ root : J → ℤ, integerScalarLattice (Unit ⊕ α) (m : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ q, integerScalarLattice (O q) (m : ℤ) ≤
        (scalarKernelIntegerJet x (degree q) (rows q)).mulVecLin.range) := by
  obtain ⟨a, ha, haB, hp⟩ := hx.2
  refine ⟨a^smax, pow_pos ha _, Nat.pow_le_pow_left haB _, ?_, ?_⟩
  · intro root
    rw [selectedSpatial_full_image, Nat.cast_pow]
    apply (integerScalarLattice_pow_le (a : ℤ) hsmax).trans
    simpa only [pow_one] using rootDifferenceMatrix_period root (scalarCubeDifferenceMatrix x) (a : ℤ) hp
  · intro q
    rw [Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period _ _ (a : ℤ) hp smax (degree q)
      (hdegree q) (rows q) (hinj q) (hrows q)

theorem goodKernel_mapped_pivots {Q α J K Z X : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O N : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)]
    [∀ q, Fintype (N q)] [∀ q, DecidableEq (N q)]
    {L B : ℕ} {κ : ℝ} (hL : 0 < L) (selection : α ↪ J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (hinj : ∀ q, Function.Injective (rows q)) (hrows : ∀ q i, (rows q i).card ≤ degree q) :
    ∃ s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q),
      (∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0) ∧
      ∀ (H : Q → ℝ), (∀ q, 0 < H q) →
      ∀ (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
        (z : Z → ℤ) (y : X → ℤ) (T : K → ℝ),
      (∀ k, 0 < T k) → (∀ k, T k ≤ (L : ℝ)) →
      (∀ q n, (e q n).sum (fun _ d => d) ≤ degree q) →
      (∀ k a, |((Sum.elim z y (input k a) : ℤ) : ℝ)/T k| ≤ 1) →
      ∀ G : ℝ, (∀ q, (((B^degree q)^Fintype.card (O q) : ℕ) : ℝ) ≤ G) →
      ∀ q, CoefficientFiberControl
        (Matrix.fromCols (scalarKernelIntegerJet x (degree q) (rows q))
          (integerMappedJetMatrix (e q) input z (rows q) y))
        ((s q).trans Function.Embedding.inl)
        (Sum.elim (kernelJetCoefficientScale J (degree q) L (H q))
          (fun n => H q / monomialScale T (e q n)))
        (H q) L (degree q) (kernelJetEntryAllowance (Fintype.card α) (degree q))
        (kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card (O q)) (degree q) κ) G := by
  classical
  have hchoice (q) := goodScalarKernelTuple_fixed_jet_pivot hL selection hκ x hx
    (degree q) (rows q) (hinj q) (hrows q)
  choose s hd hi using hchoice
  refine ⟨s, hd, ?_⟩
  intro H hH e input z y T hT hTL he hn G hG q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fromCols_left_pivot] using hd q
  · intro j
    cases j with
    | inl a => exact kernelJetCoefficientScale_lower J (degree q) (by exact_mod_cast hL) (hH q).le a
    | inr n => exact kernelCoefficientScale_lower T hT (hH q).le (by exact_mod_cast hL) hTL (e q n) (he q n)
  · intro i j
    exact scalarKernelJet_integer_entry hL x (degree q) (rows q) i (s q j)
  · intro i j
    rw [normalizedIntegerColumns_fromCols]
    cases j with
    | inl a =>
      simpa only [Matrix.fromCols_apply_inl, normalizedIntegerColumns_entry_div] using
        scalarKernelJet_normalized_entry hL x (degree q) (rows q) (hH q).ne' i a
    | inr n =>
      simpa only [Matrix.fromCols_apply_inr, normalizedIntegerColumns_entry_div,
        integerMappedJetMatrix, integerMappedCubeTuple] using
        normalizedAffineMonomialJetMatrix_bound
        (fun k => Sum.elim z y (input k none)) (fun a k => Sum.elim z y (input k (some a)))
        (e q) (rows q) T (he q) (fun k => hn k none) (fun a k => hn k (some a)) (hH q).ne' i n
  · rw [fromCols_left_pivot]
    exact hi q (H q) (hH q).ne'
  · have hb := scalarKernelJet_extended_index selection x hx (degree q) (rows q)
      (hinj q) (hrows q) (integerMappedJetMatrix (e q) input z (rows q) y)
    have hb' : ((Matrix.fromCols (scalarKernelIntegerJet x (degree q) (rows q))
        (integerMappedJetMatrix (e q) input z (rows q) y)).mulVecLin.range.toAddSubgroup.index : ℝ) ≤
        (((B^degree q)^Fintype.card (O q) : ℕ) : ℝ) := by exact_mod_cast hb
    exact hb'.trans (hG q)

end Erdos3

end

section

namespace Erdos3

theorem scalarKernel_real_entry_bound {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L : ℕ} (hL : 0 < L)
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ) (rows : O → Finset α)
    (i : O) (a : BoundedIntegerExponent J degree) :
    |normalizedScalarKernelJet x degree rows i a| ≤ kernelJetEntryAllowance (Fintype.card α) degree := by
  have hc (j : J) (i : Option α) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  exact boundedDegreeRealJetMatrix_entry_bound _ _ (fun j => hc j none)
    (fun i j => hc j (some i)) degree rows i a

theorem scalarKernelFixed_operator_bounds {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ} (hL : 0 < L)
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) :
    ‖(scalarKernelFixedPivot hL x degree rows s hs).toContinuousLinearMap‖ ≤
      Fintype.card O * kernelJetEntryAllowance (Fintype.card α) degree ∧
    ‖scalarKernelFixedFree x degree rows s‖ ≤
      Fintype.card (UnselectedColumn s) * kernelJetEntryAllowance (Fintype.card α) degree := by
  constructor
  · rw [scalarKernelFixedPivot, normalizedPivotEquiv_coe,
      normalized_scalarKernel_pivot x degree rows s one_ne_zero]
    exact matrixSupCLM_norm_le _ (kernelJetEntryAllowance_pos _ _).le
      (fun i j => scalarKernel_real_entry_bound hL x degree rows i (s j))
  · exact matrixSupCLM_norm_le _ (kernelJetEntryAllowance_pos _ _).le
      (fun i j => scalarKernel_real_entry_bound hL x degree rows i j.val)

theorem goodKernel_fixed_pivots {Q α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)]
    {L B : ℕ} {κ : ℝ} (hL : 0 < L) (selection : α ↪ J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (hinj : ∀ q, Function.Injective (rows q)) (hrows : ∀ q i, (rows q i).card ≤ degree q) :
    ∃ s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q),
    ∃ hs : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0,
      ∀ q, ‖(scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)).symm.toContinuousLinearMap‖ ≤
        kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card (O q)) (degree q) κ := by
  classical
  have hc (q) := goodScalarKernelTuple_fixed_jet_pivot hL selection hκ x hx
    (degree q) (rows q) (hinj q) (hrows q)
  choose s hs hi using hc
  refine ⟨s, hs, fun q => ?_⟩
  rw [scalarKernelFixedPivot, normalizedPivotEquiv_inverse_eq]
  exact hi q 1 one_ne_zero

theorem fixedKernel_mapped_control {α J O N K Z X : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    {L B : ℕ} {κ H U G : ℝ} (hL : 0 < L) (selection : α ↪ J)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (degree : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hrows : ∀ i, (rows i).card ≤ degree) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0)
    (hi : ‖(scalarKernelFixedPivot hL x degree rows s hs).symm.toContinuousLinearMap‖ ≤ U)
    (hH : 0 < H) (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℤ) (y : X → ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (hTL : ∀ k, T k ≤ (L : ℝ)) (he : ∀ n, (e n).sum (fun _ d => d) ≤ degree)
    (hn : ∀ k a, |((Sum.elim z y (input k a) : ℤ) : ℝ)/T k| ≤ 1)
    (hG : (((B^degree)^Fintype.card O : ℕ) : ℝ) ≤ G) :
    CoefficientFiberControl
      (Matrix.fromCols (scalarKernelIntegerJet x degree rows) (integerMappedJetMatrix e input z rows y))
      (s.trans Function.Embedding.inl)
      (Sum.elim (kernelJetCoefficientScale J degree L H) (fun n => H / monomialScale T (e n)))
      H L degree (kernelJetEntryAllowance (Fintype.card α) degree) U G := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fromCols_left_pivot] using hs
  · intro j
    cases j with
    | inl a => exact kernelJetCoefficientScale_lower J degree (by exact_mod_cast hL) hH.le a
    | inr n => exact kernelCoefficientScale_lower T hT hH.le (by exact_mod_cast hL) hTL (e n) (he n)
  · intro i j
    exact scalarKernelJet_integer_entry hL x degree rows i (s j)
  · intro i j
    rw [normalizedIntegerColumns_fromCols]
    cases j with
    | inl a =>
      simpa only [Matrix.fromCols_apply_inl, normalizedIntegerColumns_entry_div] using
        scalarKernelJet_normalized_entry hL x degree rows hH.ne' i a
    | inr n =>
      simpa only [Matrix.fromCols_apply_inr, normalizedIntegerColumns_entry_div,
        integerMappedJetMatrix, integerMappedCubeTuple] using
        normalizedAffineMonomialJetMatrix_bound
          (fun k => Sum.elim z y (input k none)) (fun a k => Sum.elim z y (input k (some a)))
          e rows T he (fun k => hn k none) (fun a k => hn k (some a)) hH.ne' i n
  · rw [fromCols_left_pivot]
    change ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x degree rows).submatrix id s)
      (fun i => kernelJetCoefficientScale J degree L H (s i)) (fun _ => H))).inverse‖ ≤ U
    rw [← normalizedPivotEquiv_inverse_eq _ hs
      (fun i => kernelJetCoefficientScale J degree L H (s i)) (fun _ => H)
      (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) hH (s i)) (fun _ => hH),
      scalarKernel_pivot_scale_independent hL x degree rows s hs hH]
    exact hi
  · have hb := scalarKernelJet_extended_index selection x hx degree rows hinj hrows
      (integerMappedJetMatrix e input z rows y)
    have hb' : ((Matrix.fromCols (scalarKernelIntegerJet x degree rows)
        (integerMappedJetMatrix e input z rows y)).mulVecLin.range.toAddSubgroup.index : ℝ) ≤
        (((B^degree)^Fintype.card O : ℕ) : ℝ) := by exact_mod_cast hb
    exact hb'.trans hG

end Erdos3

end

section

namespace Erdos3

def kernelPeriodCandidate {B : ℕ} (degree : ℕ) (a : Fin B) : ℕ :=
  (a.val + 1) ^ degree

theorem kernelPeriodCandidate_pos {B : ℕ} (degree : ℕ) (a : Fin B) :
    0 < kernelPeriodCandidate degree a :=
  pow_pos (Nat.succ_pos _) _

instance kernelPeriodCandidate_neZero {B : ℕ} (degree : ℕ) (a : Fin B) :
    NeZero (kernelPeriodCandidate degree a) :=
  ⟨(kernelPeriodCandidate_pos degree a).ne'⟩

theorem kernelPeriodCandidate_le {B : ℕ} (degree : ℕ) (a : Fin B) :
    kernelPeriodCandidate degree a ≤ B ^ degree :=
  Nat.pow_le_pow_left (Nat.succ_le_of_lt a.isLt) _

theorem kernelPeriodCandidate_le_exp {B : ℕ} {p : ℝ}
    (hB : (B : ℝ) ≤ Real.exp p) (degree : ℕ) (a : Fin B) :
    (kernelPeriodCandidate degree a : ℝ) ≤ Real.exp (degree * p) := by
  calc
    _ ≤ (B : ℝ) ^ degree := by exact_mod_cast kernelPeriodCandidate_le degree a
    _ ≤ (Real.exp p) ^ degree := pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
    _ = _ := (Real.exp_nat_mul p degree).symm

theorem goodKernel_periodFamily {Q α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J]
    {O : Q → Type*} [∀ q, Fintype (O q)]
    {L B : ℕ} {κ : ℝ} (selection : α ↪ J)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (smax : ℕ) (hsmax : 1 ≤ smax) (degree : Q → ℕ) (hdegree : ∀ q, degree q ≤ smax)
    (rows : ∀ q, O q → Finset α) (hinj : ∀ q, Function.Injective (rows q))
    (hrows : ∀ q i, (rows q i).card ≤ degree q) :
    ∃ a : Fin B,
      (∀ root : J → ℤ, integerScalarLattice (Unit ⊕ α) (kernelPeriodCandidate smax a : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ q, integerScalarLattice (O q) (kernelPeriodCandidate smax a : ℤ) ≤
        (scalarKernelIntegerJet x (degree q) (rows q)).mulVecLin.range) := by
  obtain ⟨a, ha, haB, hp⟩ := hx.2
  let candidate : Fin B := ⟨a - 1, by omega⟩
  have hc : candidate.val + 1 = a := by dsimp [candidate]; omega
  refine ⟨candidate, ?_, ?_⟩
  · intro root
    rw [selectedSpatial_full_image, kernelPeriodCandidate, hc, Nat.cast_pow]
    apply (integerScalarLattice_pow_le (a : ℤ) hsmax).trans
    simpa only [pow_one] using
      rootDifferenceMatrix_period root (scalarCubeDifferenceMatrix x) (a : ℤ) hp
  · intro q
    rw [kernelPeriodCandidate, hc, Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period _ _ (a : ℤ) hp smax (degree q)
      (hdegree q) (rows q) (hinj q) (hrows q)

end Erdos3

end

section

namespace Erdos3

theorem goodKernel_periodFamily_uniform_rows {α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J]
    {L B : ℕ} {κ : ℝ} (selection : α ↪ J)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (smax : ℕ) (hsmax : 1 ≤ smax) :
    ∃ candidate : Fin B,
      (∀ root : J → ℤ, integerScalarLattice (Unit ⊕ α) (kernelPeriodCandidate smax candidate : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      ∀ (O : Type*) [Fintype O] (degree : ℕ), degree ≤ smax →
        ∀ rows : O → Finset α, Function.Injective rows →
          (∀ o, (rows o).card ≤ degree) →
            integerScalarLattice O (kernelPeriodCandidate smax candidate : ℤ) ≤
              (scalarKernelIntegerJet x degree rows).mulVecLin.range := by
  obtain ⟨a, ha, haB, hp⟩ := hx.2
  let candidate : Fin B := ⟨a - 1, by omega⟩
  have hc : candidate.val + 1 = a := by dsimp [candidate]; omega
  refine ⟨candidate, ?_, ?_⟩
  · intro root
    rw [selectedSpatial_full_image, kernelPeriodCandidate, hc, Nat.cast_pow]
    apply (integerScalarLattice_pow_le (a : ℤ) hsmax).trans
    simpa only [pow_one] using rootDifferenceMatrix_period root (scalarCubeDifferenceMatrix x) (a : ℤ) hp
  · intro O hO degree hdegree rows hinj hrows
    rw [kernelPeriodCandidate, hc, Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period _ _ (a : ℤ) hp smax degree
      hdegree rows hinj hrows

noncomputable def goodKernelUniformCandidate {α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L B : ℕ} {κ : ℝ}
    (selection : α ↪ J) (x : J → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection κ B x) (_height : ℕ) : Fin B :=
  ⟨Classical.choose hx.2 - 1, by
    have h := Classical.choose_spec hx.2
    omega⟩

theorem goodKernelUniformCandidate_spec {α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L B : ℕ} {κ : ℝ}
    (selection : α ↪ J) (x : J → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection κ B x) (height : ℕ) :
    let period := kernelPeriodCandidate (height + 1) (goodKernelUniformCandidate selection x hx height)
    (∀ root : J → ℤ, integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    ∀ (O : Type*) [Fintype O] (degree : ℕ), degree ≤ height + 1 →
      ∀ rows : O → Finset α, Function.Injective rows →
        (∀ o, (rows o).card ≤ degree) →
          integerScalarLattice O (period : ℤ) ≤ (scalarKernelIntegerJet x degree rows).mulVecLin.range :=
by
  let a := Classical.choose hx.2
  obtain ⟨ha, haB, hp⟩ := Classical.choose_spec hx.2
  have hc : (goodKernelUniformCandidate selection x hx height).val + 1 = a := by
    dsimp only [goodKernelUniformCandidate, a]
    omega
  refine ⟨?_, ?_⟩
  · intro root
    rw [selectedSpatial_full_image, kernelPeriodCandidate, hc, Nat.cast_pow]
    apply (integerScalarLattice_pow_le (a : ℤ) (by omega : 1 ≤ height + 1)).trans
    simpa only [pow_one] using rootDifferenceMatrix_period root (scalarCubeDifferenceMatrix x) (a : ℤ) hp
  · intro O hO degree hdegree rows hinj hrows
    rw [kernelPeriodCandidate, hc, Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period _ _ (a : ℤ) hp (height + 1) degree
      hdegree rows hinj hrows

theorem integerScalarLattice_le_of_nat_dvd {O : Type*} [Fintype O] {a b : ℕ}
    (h : a ∣ b) : integerScalarLattice O (b : ℤ) ≤ integerScalarLattice O (a : ℤ) := by
  obtain ⟨c, rfl⟩ := h
  rintro y ⟨z, rfl⟩
  refine ⟨(c : ℤ) • z, ?_⟩
  change (a : ℤ) • ((c : ℤ) • z) = ((a * c : ℕ) : ℤ) • z
  rw [smul_smul, Nat.cast_mul]

theorem kernelPeriodCandidate_cover {B : ℕ} (smax : ℕ) (candidate : Fin B)
    {d₀ : ℕ} (hd₀ : 0 < d₀) {D P : ℝ}
    (hd : (d₀ : ℝ) ≤ Real.exp D) (hB : (B : ℝ) ≤ Real.exp P) :
    ∃ d : ℕ, 0 < d ∧ d₀ ∣ d ∧ kernelPeriodCandidate smax candidate ∣ d ∧
      d₀ ≤ d ∧ (d : ℝ) ≤ Real.exp (D + smax * P) := by
  refine ⟨d₀ * kernelPeriodCandidate smax candidate,
    Nat.mul_pos hd₀ (kernelPeriodCandidate_pos _ _), dvd_mul_right _ _, dvd_mul_left _ _, ?_, ?_⟩
  · exact Nat.le_mul_of_pos_right _ (kernelPeriodCandidate_pos _ _)
  · rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hd (kernelPeriodCandidate_le_exp hB smax candidate)
      (Nat.cast_nonneg _) (Real.exp_nonneg _)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def kernelInverseLog (q n j d : ℕ) (p : ℝ) : ℝ :=
  (j : ℝ) + (j : ℝ)^2 + (j - 1 : ℕ) * ((q : ℝ) * (d + 1)) +
    j * (d * n + d * ((q : ℝ)^2 + q + p + 2))

def kernelGeometryLog (q n j k d : ℕ) (p : ℝ) : ℝ :=
  p + j + k + (q : ℝ) * (d + 1) + kernelInverseLog q n j d p

theorem kernelGeometryLog_bounds (q n j k d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelGeometryLog q n j k d p ∧ p ≤ kernelGeometryLog q n j k d p ∧
    kernelInverseLog q n j d p ≤ kernelGeometryLog q n j k d p ∧
    (j : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p ∧
    (k : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p := by
  have hi : 0 ≤ kernelInverseLog q n j d p := by unfold kernelInverseLog; positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have he : 0 ≤ (q : ℝ) * (d + 1) := by positivity
  unfold kernelGeometryLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem nat_mul_kernelEntry_le_exp (a q d : ℕ) :
    (a : ℝ) * kernelJetEntryAllowance q d ≤ Real.exp ((a : ℝ) + (q : ℝ) * (d + 1)) := by
  have ha : (a : ℝ) ≤ Real.exp a := by linarith [Real.add_one_le_exp (a : ℝ)]
  calc
    _ ≤ Real.exp a * Real.exp ((q : ℝ) * (d + 1)) :=
      mul_le_mul ha (kernelJetEntryAllowance_le_exp q d) (kernelJetEntryAllowance_pos q d).le (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem fixedKernel_geometry_le_exp {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (x : J → IntegerScalarCubeBox α L) (d : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J d)
    (hs : ((scalarKernelIntegerJet x d rows).submatrix id s).det ≠ 0)
    (hi : ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card O) d (1/(M : ℝ)))
    {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p) :
    let P := kernelGeometryLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent J d)) d p
    ‖(scalarKernelFixedPivot hL x d rows s hs).toContinuousLinearMap‖ ≤ Real.exp P ∧
    ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤ Real.exp P ∧
    ‖scalarKernelFixedFree x d rows s‖ ≤ Real.exp P := by
  dsimp only
  have hb := kernelGeometryLog_bounds (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d hp
  have he := scalarKernelFixed_operator_bounds hL x d rows s hs
  have hcard : Fintype.card (UnselectedColumn s) ≤ Fintype.card (BoundedIntegerExponent J d) :=
    Fintype.card_subtype_le _
  refine ⟨he.1.trans ((nat_mul_kernelEntry_le_exp _ _ _).trans (Real.exp_le_exp.mpr hb.2.2.2.1)), ?_, ?_⟩
  · apply hi.trans
    apply (kernelJetInverseAllowance_le_exp (Fintype.card α) (Fintype.card J) (Fintype.card O) d
      (one_div_pos.mpr (by exact_mod_cast hM)) hp (by simpa only [one_div, inv_inv] using hMp)).trans
    exact Real.exp_le_exp.mpr hb.2.2.1
  · apply he.2.trans
    apply (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤
      Fintype.card (BoundedIntegerExponent J d)) (kernelJetEntryAllowance_pos _ _).le).trans
    exact (nat_mul_kernelEntry_le_exp _ _ _).trans (Real.exp_le_exp.mpr hb.2.2.2.2)

noncomputable def kernelRowOutputLog (q n j k u d : ℕ) (p : ℝ) : ℝ :=
  let P := kernelGeometryLog q n j k d p
  (j : ℝ)^2 + (j + 1) * P + affineProfileLogBound k p + k * (P + 1) +
    jetOutputRadiusLog q u d P + 1

theorem kernelRowOutputLog_nonneg (q n j k u d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelRowOutputLog q n j k u d p := by
  have hP := (kernelGeometryLog_bounds q n j k d hp).1
  have hf := affineProfileLogBound_nonneg k hp
  have hr := jetOutputRadiusLog_nonneg q u d hP
  unfold kernelRowOutputLog
  positivity

theorem fixedKernel_output_le_exp {α J O N : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype N]
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (x : J → IntegerScalarCubeBox α L) (d : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J d)
    (hs : ((scalarKernelIntegerJet x d rows).submatrix id s).det ≠ 0)
    (hi : ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card O) d (1/(M : ℝ)))
    (δ R : ℝ≥0) (hδ : 0 < δ) {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hR : (R : ℝ) ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let E := scalarKernelFixedPivot hL x d rows s hs
    let F := scalarKernelFixedFree x d rows s
    let B := kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent J d)) (Fintype.card N) d p
    (pivotKernelCap (UnselectedColumn s) E R (δ⁻¹^Fintype.card (BoundedIntegerExponent J d)) : ℝ) ≤ Real.exp B ∧
    (pivotKernelLip (UnselectedColumn s) E R (affineProductProfileLip (BoundedIntegerExponent J d) δ) : ℝ) ≤ Real.exp B ∧
    (normalizedJetOutputRadius α N E F d R R : ℝ) ≤ Real.exp B := by
  dsimp only
  let P := kernelGeometryLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d p
  have hb := kernelGeometryLog_bounds (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d hp
  have hnorm := fixedKernel_geometry_le_exp hL hM x d rows s hs hi hp hMp
  have hP : 0 ≤ P := hb.1
  have hRP : (R : ℝ) ≤ Real.exp P := hR.trans (Real.exp_le_exp.mpr hb.2.1)
  have hprof := affineProfileLogBound_nonneg (Fintype.card (BoundedIntegerExponent J d)) hp
  have hrad := jetOutputRadiusLog_nonneg (Fintype.card α) (Fintype.card N) d hb.1
  have hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤ Fintype.card (BoundedIntegerExponent J d) :=
    by exact_mod_cast Fintype.card_subtype_le (fun a : BoundedIntegerExponent J d => a ∉ Set.range s)
  have hmul := mul_le_mul_of_nonneg_right hcard (by linarith : 0 ≤ P + 1)
  have hcap : ((δ⁻¹^Fintype.card (BoundedIntegerExponent J d) : ℝ≥0) : ℝ) ≤
      Real.exp (affineProfileLogBound (Fintype.card (BoundedIntegerExponent J d)) p) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using
      affineProductProfile_cap_le_exp _ (show (0 : ℝ) < δ from hδ) hp hδp
  refine ⟨?_, ?_, ?_⟩
  · apply (pivotKernelCap_le_exp _ _ R _ hnorm.2.1 hRP hcap).trans
    apply Real.exp_le_exp.mpr
    dsimp [kernelRowOutputLog]
    nlinarith [hb.1]
  · apply (pivotKernelLip_le_exp _ _ R _ hnorm.2.1 hRP
      (affineProductProfileLip_le_exp (BoundedIntegerExponent J d) hδp)).trans
    apply Real.exp_le_exp.mpr
    dsimp [kernelRowOutputLog]
    linarith
  · apply (normalizedJetOutputRadius_le_exp α N _ _ d R R hb.1 hnorm.1 hnorm.2.2 hRP hRP).trans
    apply Real.exp_le_exp.mpr
    have hbase : 0 ≤ (Fintype.card O : ℝ)^2 + (Fintype.card O + 1) * P +
        affineProfileLogBound (Fintype.card (BoundedIntegerExponent J d)) p +
        Fintype.card (BoundedIntegerExponent J d) * (P + 1) := by positivity
    dsimp [kernelRowOutputLog]
    linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def kernelFamilyIndexLog {Q : Type*} [Fintype Q]
    (O : Q → Type*) [∀ q, Fintype (O q)] (smax : ℕ) (p : ℝ) : ℝ :=
  p * smax * ∑ q, (Fintype.card (O q) : ℝ)

theorem kernelFamilyIndexLog_nonneg {Q : Type*} [Fintype Q]
    (O : Q → Type*) [∀ q, Fintype (O q)] (smax : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelFamilyIndexLog O smax p := by unfold kernelFamilyIndexLog; positivity

theorem kernelFamilyIndexLog_row {Q : Type*} [Fintype Q]
    (O : Q → Type*) [∀ q, Fintype (O q)] (smax : ℕ) (degree : Q → ℕ)
    (hdegree : ∀ q, degree q ≤ smax) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p) (q : Q) :
    (((M^degree q)^Fintype.card (O q) : ℕ) : ℝ) ≤ Real.exp (kernelFamilyIndexLog O smax p) := by
  have hc : (Fintype.card (O q) : ℝ) ≤ ∑ r, (Fintype.card (O r) : ℝ) :=
    Finset.single_le_sum (f := fun r => (Fintype.card (O r) : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ q)
  have hd : (degree q : ℝ) ≤ smax := by exact_mod_cast hdegree q
  have he := mul_le_mul_of_nonneg_left
    (mul_le_mul hd hc (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp
  calc
    _ = (M : ℝ)^(degree q * Fintype.card (O q)) := by simp only [Nat.cast_pow, pow_mul]
    _ ≤ (Real.exp p)^(degree q * Fintype.card (O q)) := pow_le_pow_left₀ (Nat.cast_nonneg _) hMp _
    _ = Real.exp (((degree q * Fintype.card (O q) : ℕ) : ℝ) * p) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold kernelFamilyIndexLog
      push_cast
      nlinarith

def kernelCoefficientLog (q n j k d : ℕ) (p g : ℝ) : ℝ :=
  g + kernelGeometryLog q n j k d p

theorem kernelCoefficientLog_bounds (q n j k d : ℕ) {M : ℕ} (hM : 0 < M)
    {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) (hMp : (M : ℝ) ≤ Real.exp p) :
    let b := kernelCoefficientLog q n j k d p g
    0 ≤ b ∧ Real.exp g ≤ Real.exp b ∧
    kernelJetInverseAllowance q n j d (1/(M : ℝ)) ≤ Real.exp b ∧
    kernelJetEntryAllowance q d ≤ Real.exp b ∧ Real.exp p ≤ Real.exp b := by
  dsimp only
  have hb := kernelGeometryLog_bounds q n j k d hp
  have hP : kernelGeometryLog q n j k d p ≤ kernelCoefficientLog q n j k d p g := by
    unfold kernelCoefficientLog
    linarith
  refine ⟨add_nonneg hg hb.1, ?_, ?_, ?_, ?_⟩
  · apply Real.exp_le_exp.mpr
    unfold kernelCoefficientLog
    linarith [hb.1]
  · apply (kernelJetInverseAllowance_le_exp q n j d
      (one_div_pos.mpr (by exact_mod_cast hM)) hp (by simpa only [one_div, inv_inv] using hMp)).trans
    exact Real.exp_le_exp.mpr (hb.2.2.1.trans hP)
  · apply (kernelJetEntryAllowance_le_exp q d).trans
    apply Real.exp_le_exp.mpr
    have he := hb.2.2.2.1.trans hP
    linarith [Nat.cast_nonneg j (α := ℝ)]
  · exact Real.exp_le_exp.mpr (hb.2.1.trans hP)

end Erdos3

end

end OAI
