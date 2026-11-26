import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelCofinal
import IPRADerivations.Analysis.Stirling.Wallis.GaussianGammaHalfWallisRate

/-!
# Time continuity of the actual Binet kernel

On the rational time interval [0,T], both the finite observation and
the cofinal kernel admit the Lipschitz gain T. The finite estimate uses
a telescoping row majorant and is independent of the cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelTimeContinuity

open_ipra
open GaussianBinetKernelRows
  (inputData rowData rowF rowBody row_at row_sample regular_rows
    denominator denominatorLower denominator_lower weight value subst_inputData)
open GaussianBinetKernelTail (finiteF finiteData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qzero qadd qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalReciprocal (reciprocal norm_positive inverse_bound bound_congr bounded_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "observedBody" => GaussianNamedFiniteSumFamily.body rowF rowBody
local notation "finite" => GaussianNamedFiniteSumFamily.finite rowF rowBody

def source (A B a b T E D : PTm n) : Fm PTm n :=
  le one B ⋏ (le one b ⋏ (le one D ⋏
    (le A (T*B) ⋏ (le a (T*b) ⋏ distanceBounded (fraction A B) (fraction a b) E D))))

ipra_subst source [one]

theorem row_time_distance (p i A B a b T E D : PTm n)
    (h : Γ ⊢[PRAAx] source A B a b T E D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rowF p (rowData i A B)) (ap2 rowF p (rowData i a b))
      (T*E) (D*(succ i*succ (succ i))) := by
  let k := succ i
  let l := succ k
  let R := denominatorLower k
  let π := GaussianBinetKernelPi.sample p
  let u := denominator A B k π
  let v := denominator a b k π
  let F := E*T+T*E
  have hB := h.andE₁
  have hb := h.andE₂.andE₁
  have hD := h.andE₂.andE₂.andE₁
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ i
  have hl : Γ ⊢[PRAAx] le one l := zero_lt_succ k
  have hkk : Γ ⊢[PRAAx] le one (succ i*succ i) := positive_product _ _ hk hk
  have hR : Γ ⊢[PRAAx] le one R := positive_product (num 16) _ (by ipra_le 15) hkk
  have hx := GaussianEulerExponentCompactBounds.fraction_bound A B T hB h.andE₂.andE₂.andE₂.andE₁
  have hy := GaussianEulerExponentCompactBounds.fraction_bound a b T hb h.andE₂.andE₂.andE₂.andE₂.andE₁
  have xy := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have hs := GaussianNameArithmetic.product_distance (fraction A B) (fraction a b)
    (fraction A B) (fraction a b) E E D T T hD xy xy hx hy
  have hd : Γ ⊢[PRAAx] distanceBounded u v F D :=
    GaussianNameRingLaws.sum_left_error _ _ (qmul (fraction (weight k) one) (qmul π π)) F D hD hs
  have hu := denominator_lower p k A B hB
  have hv := denominator_lower p k a b hb
  have he := GaussianNameReciprocal.inverse_difference u v (norm_positive u R hR hu) (norm_positive v R hR hv)
  have left := bounded_product (reciprocal u) (qsub v u) one R F D hR hD
    (inverse_bound u R hR hu) (distance_symmetric u v F D hD hd)
  have both := bounded_product (qmul (reciprocal u) (qsub v u)) (reciprocal v) (one*F) (R*D) one R
    (positive_product _ _ hR hD) hR left (inverse_bound v R hR hv)
  have inv : Γ ⊢[PRAAx] distanceBounded (reciprocal u) (reciprocal v) F (D*(R*R)) :=
    bound_congr he.eqSymm (by ipra_ring) (by ipra_ring) both
  have hS := positive_product _ _ hD (positive_product _ _ hR hR)
  have scalar := GaussianEulerExponentCompactBounds.fraction_bound (Γ := Γ) two one two (le_refl one)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl two))
  have raw : Γ ⊢[PRAAx] distanceBounded (value p k A B) (value p k a b) (two*F) (D*(R*R)) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference (fraction two one) _ _).eqSymm
      (.eqRefl _) (one_mul _) (bounded_product _ _ two one F (D*(R*R)) (le_refl one) hS scalar inv)
  have rowPad : Γ ⊢[PRAAx] le (num 4*(k*l)) (R*R) := by
    dsimp only [R, denominatorLower, k, l]
    ipra_le 256*𝔞(succ i*succ i)*sl hkk+248*𝔞(succ i*succ i)+4*𝔞(succ i)*𝔞(i)
  have widened := distance_radius_mono _ _ _ _ (T*E) (D*(k*l)) hS
    (positive_product _ _ hD (positive_product _ _ hk hl))
    (le_congr (by dsimp only [F]; ipra_ring) (by ipra_ring) (mul_le_mul_right (T*E*D) rowPad)) raw
  exact distance_congr (row_sample p i A B).eqSymm (row_sample p i a b).eqSymm
    (.eqRefl _) (.eqRefl _) widened

private theorem entry_at (p i A B : PTm n) :
    Γ ⊢[PRAAx] inst2 observedBody i (pairT p (inputData A B)) ≐ ap2 rowF p (rowData i A B) :=
  (GaussianNamedFiniteSumFamily.term_at rowF rowBody i p (inputData A B)).eqTrans
    (congrAp2 rowF (.eqRefl p) (row_at i A B))

private def prefixLaw (p N A B a b T E D : PTm n) : Fm PTm n :=
  distanceBounded (finite p N (inputData A B)) (finite p N (inputData a b)) ((T*E)*N) (D*succ N)

@[simp] private theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (p N A B a b T E D : PTm n) :
    (prefixLaw p N A B a b T E D).subst σ =
      prefixLaw (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B)
        (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ T) (Syn.subst σ E) (Syn.subst σ D) := by
  simp [prefixLaw, GaussianNamedFiniteSumFamily.finite]

private theorem prefix_step (p N A B a b T E D : PTm n)
    (h : Γ ⊢[PRAAx] source A B a b T E D) (previous : Γ ⊢[PRAAx] prefixLaw p N A B a b T E D) :
    Γ ⊢[PRAAx] prefixLaw p (succ N) A B a b T E D := by
  let k := succ N
  let l := succ k
  let W := D*(k*l)
  let L := (T*E)*N*l
  have hD := h.andE₂.andE₂.andE₁
  have hk := zero_lt_succ (Γ := Γ) N
  have hl := zero_lt_succ (Γ := Γ) k
  have hW := positive_product _ _ hD (positive_product _ _ hk hl)
  have prev := distance_radius_mono _ _ ((T*E)*N) (D*k) L W (positive_product _ _ hD hk) hW
    (le_of_eq_add (d := zero) (by dsimp only [W,L]; ipra_ring)) previous
  have row := distance_congr (entry_at p N A B).eqSymm (entry_at p N a b).eqSymm
    (.eqRefl _) (.eqRefl _) (row_time_distance p N A B a b T E D h)
  have total := GaussianNameArithmetic.sum_distance _ _ _ _ L (T*E) W hW prev row
  have sharp := distance_radius_mono _ _ _ _ ((T*E)*k) (D*l) hW (positive_product _ _ hD hl)
    (le_of_eq_add (d := zero) (by dsimp only [W,L,k,l]; ipra_ring)) total
  exact distance_congr (GaussianRationalFiniteSum.sum_succ observedBody N (pairT p (inputData A B))).eqSymm
    (GaussianRationalFiniteSum.sum_succ observedBody N (pairT p (inputData a b))).eqSymm
    (.eqRefl _) (.eqRefl _) sharp

theorem prefix_distance (p N A B a b T E D : PTm n) (h : Γ ⊢[PRAAx] source A B a b T E D) :
    Γ ⊢[PRAAx] distanceBounded (finite p N (inputData A B)) (finite p N (inputData a b))
      ((T*E)*N) (D*succ N) := by
  let sh (z : PTm n) := Syn.shift z
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh A) (sh B) (sh a) (sh b) (sh T) (sh E) (sh D) := by
    simpa only [Fm.shift, Syn.shift, sh, subst_source] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (sh p) (var 0) (sh A) (sh B) (sh a) (sh b) (sh T) (sh E) (sh D)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,sh,Syn.subst_inst_shift]
      have hD := positive_product _ _ h.andE₂.andE₂.andE₁ (zero_lt_succ zero)
      exact distance_congr (GaussianRationalFiniteSum.sum_zero observedBody (pairT p (inputData A B))).eqSymm
        (GaussianRationalFiniteSum.sum_zero observedBody (pairT p (inputData a b))).eqSymm
        (by ipra_ring) (.eqRefl _) (GaussianRationalPowerDifference.distance_refl_zero qzero (D*succ zero) hD)
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,sh,subst_repl_shift]
      exact prefix_step (sh p) (var 0) (sh A) (sh B) (sh a) (sh b) (sh T) (sh E) (sh D) hs.wk Prf.hyp0
  change Γ ⊢[PRAAx] prefixLaw p N A B a b T E D
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,sh,Syn.subst_inst_shift] using all.allE N

theorem finite_at (p N A B a b T E D : PTm n) (h : Γ ⊢[PRAAx] source A B a b T E D) :
    Γ ⊢[PRAAx] distanceBounded (finite p N (inputData A B)) (finite p N (inputData a b)) (T*E) D := by
  have hD := h.andE₂.andE₂.andE₁
  exact distance_radius_mono _ _ _ _ (T*E) D (positive_product _ _ hD (zero_lt_succ N)) hD
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (T*E*D) (le_succ_self N)))
    (prefix_distance p N A B a b T E D h)

theorem named_finite_at (p N A B a b T E D : PTm n) (h : Γ ⊢[PRAAx] source A B a b T E D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 finiteF p (finiteData N A B)) (ap2 finiteF p (finiteData N a b)) (T*E) D :=
  distance_congr (GaussianNamedFiniteSumFamily.sample_at rowF rowBody p N (inputData A B)).eqSymm
    (GaussianNamedFiniteSumFamily.sample_at rowF rowBody p N (inputData a b)).eqSymm
    (.eqRefl _) (.eqRefl _) (finite_at (GaussianFastValueCut.exponent N p) N A B a b T E D h)

theorem cofinal_at (p A B a b T E D : PTm n) (h : Γ ⊢[PRAAx] source A B a b T E D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianBinetKernelCofinal.nameF p (inputData A B))
      (ap2 GaussianBinetKernelCofinal.nameF p (inputData a b)) (T*E) D :=
  distance_congr (GaussianBinetKernelCofinal.sample_at p A B).eqSymm (GaussianBinetKernelCofinal.sample_at p a b).eqSymm
    (.eqRefl _) (.eqRefl _) (named_finite_at (succ p) (GaussianBinetKernelCofinal.cutoff p) A B a b T E D h)

private theorem envelope_bound (x y A D p : PTm n) (F : PR 2) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 F p y) A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 F p y) (diagonalNumerator A D zero p) (diagonalDenominator D p) :=
  distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ hD (unit_positive p))
    (le_of_eq_add (d := zero) (by dsimp only [diagonalNumerator, diagonalDenominator]; ipra_ring)) h

theorem named_finite_rate (N A B a b T E D : PTm n) (h : Γ ⊢[PRAAx] source A B a b T E D) :
    Γ ⊢[PRAAx] independentRate finiteF finiteF (finiteData N A B) (finiteData N a b) (T*E) D := by
  have ra := GaussianNamedFiniteSumFamily.regular rowF rowBody N (inputData A B) (regular_rows N A B h.andE₁)
  have rb := GaussianNamedFiniteSumFamily.regular rowF rowBody N (inputData a b) (regular_rows N a b h.andE₂.andE₁)
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ zero h.andE₂.andE₂.andE₁ ra rb (.allI ?_)
  let sh (z : PTm n) := Syn.shift z
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh A) (sh B) (sh a) (sh b) (sh T) (sh E) (sh D) := by
    simpa only [Fm.shift, Syn.shift, sh, subst_source] using h.shift
  simpa only [diagonalEnvelope, Syn.shift, sh, GaussianNamedFiniteSumFamily.subst_data, subst_inputData,
    PTm.subst_mul, ConciseIPRA.PTm.subst_zero] using
    envelope_bound (finiteData (sh N) (sh A) (sh B)) (finiteData (sh N) (sh a) (sh b))
      (sh T*sh E) (sh D) (var 0) finiteF hs.andE₂.andE₂.andE₁
      (named_finite_at (var 0) (sh N) (sh A) (sh B) (sh a) (sh b) (sh T) (sh E) (sh D) hs)

theorem cofinal_rate (A B a b T E D : PTm n) (h : Γ ⊢[PRAAx] source A B a b T E D) :
    Γ ⊢[PRAAx] independentRate GaussianBinetKernelCofinal.nameF GaussianBinetKernelCofinal.nameF
      (inputData A B) (inputData a b) (T*E) D := by
  have ra := GaussianBinetKernelCofinal.regular A B h.andE₁
  have rb := GaussianBinetKernelCofinal.regular a b h.andE₂.andE₁
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ zero h.andE₂.andE₂.andE₁ ra rb (.allI ?_)
  let sh (z : PTm n) := Syn.shift z
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh A) (sh B) (sh a) (sh b) (sh T) (sh E) (sh D) := by
    simpa only [Fm.shift, Syn.shift, sh, subst_source] using h.shift
  simpa only [diagonalEnvelope, Syn.shift, sh, subst_inputData, PTm.subst_mul, ConciseIPRA.PTm.subst_zero] using
    envelope_bound (inputData (sh A) (sh B)) (inputData (sh a) (sh b)) (sh T*sh E) (sh D) (var 0)
      GaussianBinetKernelCofinal.nameF hs.andE₂.andE₂.andE₁
      (cofinal_at (var 0) (sh A) (sh B) (sh a) (sh b) (sh T) (sh E) (sh D) hs)

theorem mesh_input (A B j T : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le (A+j) (T*B)) :
    Γ ⊢[PRAAx] source A B (A+j) B T j B := by
  refine .andI hB (.andI hB (.andI hB (.andI (le_trans (le_add_right A j) hT) (.andI hT ?_))))
  exact GaussianGammaHalfWallisRate.fraction_distance A B (A+j) B j B hB hB hB
    (le_of_eq_add (d := two*j*B*B) (by ipra_ring)) (le_of_eq_add (d := zero) (by ipra_ring))

theorem actual_finite_Binet_kernel_mesh_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 2) ⟶ le (var 1+var 3) (var 4*var 2) ⟶ independentRate finiteF finiteF
        (finiteData (var 0) (var 1) (var 2)) (finiteData (var 0) (var 1+var 3) (var 2))
        (var 4*var 3) (var 2)) :=
  closeUniv 5 (.impI (.impI (named_finite_rate _ _ _ _ _ _ _ _ (mesh_input _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_cofinal_Binet_kernel_mesh_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 1) ⟶ le (var 0+var 2) (var 3*var 1) ⟶
        independentRate GaussianBinetKernelCofinal.nameF GaussianBinetKernelCofinal.nameF
          (inputData (var 0) (var 1)) (inputData (var 0+var 2) (var 1)) (var 3*var 2) (var 1)) :=
  closeUniv 4 (.impI (.impI (cofinal_rate _ _ _ _ _ _ _ (mesh_input _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelTimeContinuity
