/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Fourier.FourierLawTransport
import OAI.Combinatorics.Progressions.Polynomial.CommonPolynomialScale

namespace OAI

section

namespace Erdos3

theorem natCeil_le_exp_succ {x P : ℝ} (hx : 0 ≤ x) (hP : 0 ≤ P)
    (h : x ≤ Real.exp P) : (⌈x⌉₊ : ℝ) ≤ Real.exp (P+1) := by
  apply (Nat.ceil_lt_add_one hx).le.trans
  simpa only [add_comm x 1] using one_add_le_exp_succ hP h

theorem natFinsetSup_cast_le {I : Type*} (s : Finset I) (f : I → ℕ)
    {P : ℝ} (hP : 0 ≤ P) (hf : ∀ i ∈ s, (f i : ℝ) ≤ P) :
    ((s.sup f : ℕ) : ℝ) ≤ P := by
  apply (Nat.le_floor_iff hP).mp
  exact Finset.sup_le_iff.mpr (fun i hi => (Nat.le_floor_iff hP).mpr (hf i hi))

theorem integerPolynomialInitialScale_exp_bound {ε P Q : ℝ}
    (hε : 0 < ε) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hεQ : ε⁻¹ ≤ Real.exp Q) :
    (integerPolynomialInitialScale ε : ℝ) ≤ Real.exp (P+Q+17) := by
  have h8 : (8 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hx : 8 * (probabilityProfileLipschitz : ℝ) / ε ≤ Real.exp (P+Q+16) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 16 * Real.exp P * Real.exp Q := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hc := natCeil_le_exp_succ (by positivity) (by positivity) hx
  rw [show P+Q+16+1 = P+Q+17 by ring] at hc
  simp only [integerPolynomialInitialScale, Nat.cast_max, Nat.cast_one]
  exact max_le (Real.one_le_exp (by positivity)) hc

theorem principalSamplingGapRatio_exp_bound {γ P Q : ℝ}
    (hγ : 0 < γ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hγQ : γ⁻¹ ≤ Real.exp Q) :
    (principalSamplingGapRatio γ : ℝ) ≤ Real.exp (P+Q+17) := by
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hx : 16 * (probabilityProfileLipschitz : ℝ) / γ ≤ Real.exp (P+Q+16) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 16 * Real.exp P * Real.exp Q := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hmax := max_le (Real.one_le_exp (by positivity : 0 ≤ P+Q+16)) hx
  have hc := natCeil_le_exp_succ (le_trans zero_le_one (le_max_left _ _))
    (by positivity) hmax
  simpa only [principalSamplingGapRatio, show P+Q+16+1 = P+Q+17 by ring] using hc

theorem commonPolynomialGapRatio_exp_bound {I : Type*} [Fintype I]
    (γ : I → ℝ) {P Q : ℝ} (hγ : ∀ i, 0 < γ i) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hγQ : ∀ i, (γ i)⁻¹ ≤ Real.exp Q) :
    (commonPolynomialGapRatio γ : ℝ) ≤ Real.exp (P+Q+17) := by
  simp only [commonPolynomialGapRatio, Nat.cast_max, Nat.cast_one]
  refine max_le (Real.one_le_exp (by positivity)) ?_
  apply natFinsetSup_cast_le _ _ (Real.exp_nonneg _)
  exact fun i _ => principalSamplingGapRatio_exp_bound (hγ i) hP hQ hA (hγQ i)

theorem commonPolynomialInitialScale_exp_bound {I : Type*} [Fintype I]
    (ε : I → ℝ) (L₀ : ℕ) {P Q : ℝ} (hε : ∀ i, 0 < ε i) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hεQ : ∀ i, (ε i)⁻¹ ≤ Real.exp Q) (hL₀ : (L₀ : ℝ) ≤ Real.exp P) :
    (commonPolynomialInitialScale L₀ ε : ℝ) ≤ Real.exp (P+Q+17) := by
  simp only [commonPolynomialInitialScale, Nat.cast_max, Nat.cast_one]
  refine max_le (hL₀.trans (Real.exp_le_exp.mpr (by linarith)))
    (max_le (Real.one_le_exp (by positivity)) ?_)
  apply natFinsetSup_cast_le _ _ (Real.exp_nonneg _)
  exact fun i _ => integerPolynomialInitialScale_exp_bound (hε i) hP hQ hA (hεQ i)

end Erdos3

end

section

namespace Erdos3

noncomputable def integerAxisShortBound (h T : ℕ) (γ : ℝ) : ℕ :=
  2*inactiveDenominator γ*(2*T)^h

theorem integerAxisSideLength_inactive_of_short {h K L T : ℕ} {γ : ℝ}
    (hTL : T ≤ L) (hshort : integerAxisSideLength h K L γ < T) :
    K ≤ L^h ∧ integerAxisSideLength h K L γ = inactiveSideLength h K (inactiveDenominator γ) := by
  have ha : ¬ L^h < K := by
    intro ha
    have hside : integerAxisSideLength h K L γ = L := by simp [integerAxisSideLength, ha]
    rw [hside] at hshort
    omega
  exact ⟨Nat.le_of_not_gt ha, by simp [integerAxisSideLength, ha]⟩

theorem integerAxisSideLength_short_scale {h K L T : ℕ} {γ : ℝ}
    (hh : 0 < h) (hT : 0 < T) (hTL : T ≤ L)
    (hshort : integerAxisSideLength h K L γ < T) :
    K ≤ integerAxisShortBound h T γ := by
  obtain ⟨_, heq⟩ := integerAxisSideLength_inactive_of_short hTL hshort
  rw [heq] at hshort
  let q := inactiveDenominator γ
  have hq : 0 < q := inactiveDenominator_pos γ
  change K ≤ 2*q*(2*T)^h
  by_cases hlarge : 2*q ≤ K
  · calc
      K ≤ q*2^h*inactiveSideLength h K q^h := (inactiveSideLength_lower_power hh hq hlarge).le
      _ ≤ q*2^h*T^h := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hshort.le h)
      _ = q*(2*T)^h := by rw [mul_pow]; ring
      _ ≤ 2*q*(2*T)^h := Nat.mul_le_mul_right _ (by omega)
  · have hp : 0 < (2*T)^h := pow_pos (by omega) h
    exact (Nat.le_of_lt (Nat.lt_of_not_ge hlarge)).trans (Nat.le_mul_of_pos_right _ hp)

theorem integerAxisSideLength_long_or_bounded {h K L T : ℕ} {γ : ℝ}
    (hh : 0 < h) (hT : 0 < T) (hTL : T ≤ L) :
    T ≤ integerAxisSideLength h K L γ ∨ K ≤ integerAxisShortBound h T γ := by
  by_cases hs : T ≤ integerAxisSideLength h K L γ
  · exact Or.inl hs
  · exact Or.inr (integerAxisSideLength_short_scale hh hT hTL (Nat.lt_of_not_ge hs))

theorem inactiveDenominator_le_exp {γ p : ℝ} (hγ : 0 < γ) (hp : 0 ≤ p)
    (hγp : γ⁻¹ ≤ Real.exp p) :
    (inactiveDenominator γ : ℝ) ≤ Real.exp (p+1) := by
  simp only [inactiveDenominator, Nat.cast_max, Nat.cast_one]
  exact max_le (Real.one_le_exp_iff.mpr (by linarith))
    (natCeil_le_exp_succ (by positivity) hp hγp)

theorem integerAxisShortBound_le_exp (h T : ℕ) {γ p t : ℝ}
    (hγ : 0 < γ) (hp : 0 ≤ p) (hγp : γ⁻¹ ≤ Real.exp p) (hT : (T : ℝ) ≤ Real.exp t) :
    (integerAxisShortBound h T γ : ℝ) ≤ Real.exp (p+2+h*(t+1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq := inactiveDenominator_le_exp hγ hp hγp
  have hbase : (2*T : ℝ) ≤ Real.exp (t+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp t := mul_le_mul htwo hT (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  simp only [integerAxisShortBound, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    _ ≤ Real.exp 1*Real.exp (p+1)*(Real.exp (t+1))^h := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem integerAxisPrincipalPMF_pure_of_short {h K L T : ℕ}
    (hh : 0 < h) (hK : 0 < K) (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L^h < K → (principalSamplingGapRatio γ*L)^h ≤ K)
    (hTL : T ≤ L) (hshort : integerAxisSideLength h K L γ < T) :
    integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap =
      PMF.pure (inactivePrincipalCoefficient K (inactiveDenominator γ)) :=
  integerAxisPrincipalPMF_inactive hh hK hL hγ hgap
    (integerAxisSideLength_inactive_of_short hTL hshort).1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def shortIntegerImageAxis {X J : Type} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : (J → ℤ) → X → J → ℤ) (Q : ℕ)
    {h K L T : ℕ} [NeZero K] {γ : ℝ} (hh : 0 < h) (hT : 0 < T) (hTL : T ≤ L)
    (hshort : integerAxisSideLength h K L γ < T)
    (hY : ∀ center x, p.weight x ≠ 0 → ∀ j,
      |(Y center x j : ℝ)-center j| ≤ (Q : ℝ)*K) : IntegerFourierAxis :=
  boundedIntegerFourierAxis p Y K Q ((2*Q+1)*integerAxisShortBound h T γ)
    (Nat.mul_le_mul_left _ (integerAxisSideLength_short_scale hh hT hTL hshort)) hY

theorem shortIntegerImageAxis_exact {X J : Type} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : (J → ℤ) → X → J → ℤ) (Q : ℕ)
    {h K L T : ℕ} [NeZero K] {γ : ℝ} (hh : 0 < h) (hT : 0 < T) (hTL : T ≤ L)
    (hshort : integerAxisSideLength h K L γ < T)
    (hY : ∀ center x, p.weight x ≠ 0 → ∀ j,
      |(Y center x j : ℝ)-center j| ≤ (Q : ℝ)*K) :
    let A := shortIntegerImageAxis p Y Q hh hT hTL hshort hY
    A.law = p ∧ A.image = Y ∧ A.scale = K ∧ A.countExponent = 0 ∧
      ∀ ε, A.residualBound ε = 0 := ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem shortIntegerImageAllowance_le_exp (h T Q : ℕ) {γ u t r : ℝ}
    (hγ : 0 < γ) (hu : 0 ≤ u) (hγu : γ⁻¹ ≤ Real.exp u)
    (hTt : (T : ℝ) ≤ Real.exp t) (hr : 0 ≤ r) (hQr : (Q : ℝ) ≤ Real.exp r) :
    (((2*Q+1)*integerAxisShortBound h T γ : ℕ) : ℝ) ≤
      Real.exp (r+u+4+h*(t+1)) := by
  have h1 : 1 ≤ Real.exp r := Real.one_le_exp_iff.mpr hr
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hfactor : (2*Q+1 : ℝ) ≤ Real.exp (r+2) := by
    calc
      _ ≤ 3*Real.exp r := by linarith
      _ ≤ Real.exp 2*Real.exp r := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  push_cast
  calc
    _ ≤ Real.exp (r+2)*Real.exp (u+2+h*(t+1)) :=
      mul_le_mul hfactor (integerAxisShortBound_le_exp h T hγ hu hγu hTt)
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem shortIntegerImageAxis_log_bounds {X J : Type} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : (J → ℤ) → X → J → ℤ) (Q : ℕ)
    {h K L T : ℕ} [NeZero K] {γ : ℝ} (hh : 0 < h) (hT : 0 < T) (hTL : T ≤ L)
    (hshort : integerAxisSideLength h K L γ < T)
    (hY : ∀ center x, p.weight x ≠ 0 → ∀ j,
      |(Y center x j : ℝ)-center j| ≤ (Q : ℝ)*K)
    {u t r : ℝ} (hγ : 0 < γ) (hu : 0 ≤ u) (hγu : γ⁻¹ ≤ Real.exp u)
    (hTt : (T : ℝ) ≤ Real.exp t) (hr : 0 ≤ r) (hQr : (Q : ℝ) ≤ Real.exp r) :
    let A := shortIntegerImageAxis p Y Q hh hT hTL hshort hY
    let V := r+u+4+h*(t+1)
    (A.period : ℝ) ≤ Real.exp V ∧
      A.countConstant ≤ Real.exp (Fintype.card J*V) ∧
      A.coefficientCap ≤ Real.exp (Fintype.card J*V) ∧
      ∀ ε, A.denominatorBound ε ≤ Real.exp V := by
  let B := (2*Q+1)*integerAxisShortBound h T γ
  let V := r+u+4+h*(t+1)
  have hB : (B : ℝ) ≤ Real.exp V := shortIntegerImageAllowance_le_exp h T Q hγ hu hγu hTt hr hQr
  have hcap : (B : ℝ)^Fintype.card J ≤ Real.exp (Fintype.card J*V) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg B) hB (Fintype.card J)
  refine ⟨?_, hcap, hcap, fun _ => hB⟩
  change (((2*Q+1)*K : ℕ) : ℝ) ≤ _
  apply le_trans _ hB
  exact_mod_cast Nat.mul_le_mul_left (2*Q+1) (integerAxisSideLength_short_scale hh hT hTL hshort)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem shortIntegerAxis_block_volume {b g q K L T : ℕ} {γ : ℝ}
    (hg : 0 < g) (hK : 0 < K) (hTL : T ≤ L)
    (hshort : integerAxisSideLength g K L γ < T)
    (s : Fin b → Fin g → FiniteCubeSlice q)
    (hlen : ∀ a j, (s a j).length ≤ integerAxisSideLength g K L γ) (a : Fin b) :
    |(inactivePrincipalCoefficient K (inactiveDenominator γ) : ℝ)| *
      ∏ j, ((s a j).length : ℝ) ≤ (1/(inactiveDenominator γ : ℝ))*K := by
  have heq := (integerAxisSideLength_inactive_of_short hTL hshort).2
  have hp : (∏ j, ((s a j).length : ℝ)) ≤
      (inactiveSideLength g K (inactiveDenominator γ) : ℝ)^g := by
    calc
      _ ≤ ∏ _j : Fin g, (inactiveSideLength g K (inactiveDenominator γ) : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro j _
        exact_mod_cast (hlen a j).trans_eq heq
      _ = _ := by simp
  have hb := inactivePrincipal_scaled_upper hg hK (inactiveDenominator_pos γ)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans ((div_le_iff₀ hKr).mp hb)

noncomputable def shortIntegerCubeFourierAxis {b g q K L T : ℕ} [NeZero K] {γ : ℝ}
    (hg : 0 < g) (hT : 0 < T) (hTL : T ≤ L)
    (hshort : integerAxisSideLength g K L γ < T)
    (s : Fin b → Fin g → FiniteCubeSlice q)
    (w : CubeSliceBlockDomain s Unit → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x)
    (hlen : ∀ a j, (s a j).length ≤ integerAxisSideLength g K L γ)
    {O : ℝ} (hO : 0 ≤ O) (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O*(s a j).length)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g) : IntegerFourierAxis :=
  boundedCubeSliceFourierAxis s w hw hmass
    (fun _ _ => inactivePrincipalCoefficient K (inactiveDenominator γ))
    (fun _ => |(inactivePrincipalCoefficient K (inactiveDenominator γ) : ℝ)|)
    hO (fun _ _ => le_rfl) hroot
    (shortIntegerAxis_block_volume hg (Nat.pos_of_ne_zero (NeZero.ne K)) hTL hshort s hlen) J hJ
    (integerAxisShortBound g T γ) (integerAxisSideLength_short_scale hg hT hTL hshort)

theorem shortIntegerCubeFourierAxis_exact {b g q K L T : ℕ} [NeZero K] {γ : ℝ}
    (hg : 0 < g) (hT : 0 < T) (hTL : T ≤ L)
    (hshort : integerAxisSideLength g K L γ < T)
    (s : Fin b → Fin g → FiniteCubeSlice q)
    (w : CubeSliceBlockDomain s Unit → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x)
    (hlen : ∀ a j, (s a j).length ≤ integerAxisSideLength g K L γ)
    {O : ℝ} (hO : 0 ≤ O) (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O*(s a j).length)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g) :
    let A := shortIntegerCubeFourierAxis hg hT hTL hshort s w hw hmass hlen hO hroot J hJ
    A.scale = K ∧ A.law = cubeSliceBlockWeights s w hw hmass ∧
      A.image = cubeSliceBlockSum s (fun _ _ => inactivePrincipalCoefficient K (inactiveDenominator γ)) J ∧
      A.countExponent = 0 ∧ ∀ ε, A.residualBound ε = 0 :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem shortIntegerCubeRadius_le_exp (b g q : ℕ) (γ : ℝ) {O o : ℝ}
    (hO : 0 ≤ O) (ho : 0 ≤ o) (hOo : O ≤ Real.exp o) :
    (⌈blockJetScaleBound q g b ((O+1)^g*(1/(inactiveDenominator γ : ℝ)))⌉₊ : ℝ) ≤
      Real.exp (b+g*(q+o+2)+1) := by
  have hqpos : (0 : ℝ) < inactiveDenominator γ := by exact_mod_cast inactiveDenominator_pos γ
  have hqone : (1 : ℝ) ≤ inactiveDenominator γ := by exact_mod_cast inactiveDenominator_pos γ
  have hq : 1/(inactiveDenominator γ : ℝ) ≤ 1 := (div_le_one hqpos).mpr hqone
  have hb : (b : ℝ) ≤ Real.exp b := by linarith [Real.add_one_le_exp (b : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hdim : ((q+1 : ℕ) : ℝ) ≤ Real.exp q := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (q : ℝ)
  have hO1 : O+1 ≤ Real.exp (o+1) := by
    simpa only [add_comm O 1] using one_add_le_exp_succ ho hOo
  have hraw : blockJetScaleBound q g b ((O+1)^g*(1/(inactiveDenominator γ : ℝ))) ≤
      Real.exp (b+g*(q+o+2)) := by
    unfold blockJetScaleBound
    calc
      _ ≤ Real.exp b*(Real.exp 1)^g*(Real.exp q)^g*((Real.exp (o+1))^g*1) := by gcongr
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [mul_one, ← Real.exp_add]
        congr 1
        ring
  exact natCeil_le_exp_succ (by unfold blockJetScaleBound; positivity) (by positivity) hraw

noncomputable def shortIntegerFourierLog (b g q : ℕ) (p t o : ℝ) : ℝ :=
  b+g*(q+o+t+3)+p+5

theorem shortIntegerFourierAllowance_le_exp (b g q T : ℕ) {γ O p t o : ℝ}
    (hγ : 0 < γ) (hp : 0 ≤ p) (hγp : γ⁻¹ ≤ Real.exp p) (hT : (T : ℝ) ≤ Real.exp t)
    (hO : 0 ≤ O) (ho : 0 ≤ o) (hOo : O ≤ Real.exp o) :
    (((2*⌈blockJetScaleBound q g b ((O+1)^g*(1/(inactiveDenominator γ : ℝ)))⌉₊+1)*
        integerAxisShortBound g T γ : ℕ) : ℝ) ≤ Real.exp (shortIntegerFourierLog b g q p t o) := by
  let Q := ⌈blockJetScaleBound q g b ((O+1)^g*(1/(inactiveDenominator γ : ℝ)))⌉₊
  let r : ℝ := b+g*(q+o+2)+1
  have hQ : (Q : ℝ) ≤ Real.exp r := shortIntegerCubeRadius_le_exp b g q γ hO ho hOo
  have h1 : 1 ≤ Real.exp r := Real.one_le_exp_iff.mpr (by dsimp [r]; positivity)
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hfactor : (2*Q+1 : ℝ) ≤ Real.exp (r+2) := by
    calc
      _ ≤ 3*Real.exp r := by linarith
      _ ≤ Real.exp 2*Real.exp r := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hK := integerAxisShortBound_le_exp g T hγ hp hγp hT
  change (((2*Q+1)*integerAxisShortBound g T γ : ℕ) : ℝ) ≤ _
  push_cast
  calc
    _ ≤ Real.exp (r+2)*Real.exp (p+2+g*(t+1)) :=
      mul_le_mul hfactor hK (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [r, shortIntegerFourierLog]; ring

theorem shortIntegerCubeFourierAxis_log_bounds {b g q K L T : ℕ} [NeZero K] {γ : ℝ}
    (hg : 0 < g) (hT : 0 < T) (hTL : T ≤ L)
    (hshort : integerAxisSideLength g K L γ < T)
    (s : Fin b → Fin g → FiniteCubeSlice q)
    (w : CubeSliceBlockDomain s Unit → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x)
    (hlen : ∀ a j, (s a j).length ≤ integerAxisSideLength g K L γ)
    {O : ℝ} (hO : 0 ≤ O) (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O*(s a j).length)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    {p t o : ℝ} (hγ : 0 < γ) (hp : 0 ≤ p) (hγp : γ⁻¹ ≤ Real.exp p)
    (hTt : (T : ℝ) ≤ Real.exp t) (ho : 0 ≤ o) (hOo : O ≤ Real.exp o) :
    let A := shortIntegerCubeFourierAxis hg hT hTL hshort s w hw hmass hlen hO hroot J hJ
    let V := shortIntegerFourierLog b g q p t o
    (A.period : ℝ) ≤ Real.exp V ∧
      A.countConstant ≤ Real.exp (J.card*V) ∧ A.coefficientCap ≤ Real.exp (J.card*V) ∧
      ∀ ε, A.denominatorBound ε ≤ Real.exp V := by
  let Q := ⌈blockJetScaleBound q g b ((O+1)^g*(1/(inactiveDenominator γ : ℝ)))⌉₊
  let B := (2*Q+1)*integerAxisShortBound g T γ
  let V := shortIntegerFourierLog b g q p t o
  have hB : (B : ℝ) ≤ Real.exp V :=
    shortIntegerFourierAllowance_le_exp b g q T hγ hp hγp hTt hO ho hOo
  have hcap : (B : ℝ)^Fintype.card J ≤ Real.exp (J.card*V) := by
    calc
      _ ≤ (Real.exp V)^Fintype.card J := pow_le_pow_left₀ (Nat.cast_nonneg B) hB _
      _ = _ := by rw [← Real.exp_nat_mul, Fintype.card_coe]
  refine ⟨?_, hcap, hcap, fun _ => hB⟩
  change (((2*Q+1)*K : ℕ) : ℝ) ≤ _
  apply le_trans _ hB
  exact_mod_cast Nat.mul_le_mul_left (2*Q+1) (integerAxisSideLength_short_scale hg hT hTL hshort)

end Erdos3

end

end OAI
