import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardParameterPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | n + 1 =>
    let P := preparedFiniteForwardParameterPolynomial A stageCountConstant n
    let work := (P + Polynomial.C A) ^ A
    let cap := (4 * P + 4 * work + 16 + Polynomial.C A) ^ A
    let count := P + cap
    let branch := Polynomial.X * cap + (count + 8) ^ 8 +
      (count + Polynomial.C (stageCountConstant n)) ^ stageCountConstant n
    P + cap + branch + 1

noncomputable def preparedFiniteForwardWorkPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  (preparedFiniteForwardParameterPolynomial A stageCountConstant n + Polynomial.C A) ^ A

noncomputable def preparedFiniteForwardCapPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  (4 * preparedFiniteForwardParameterPolynomial A stageCountConstant n +
    4 * preparedFiniteForwardWorkPolynomial A stageCountConstant n + 16 + Polynomial.C A) ^ A

noncomputable def preparedFiniteForwardCountPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  preparedFiniteForwardParameterPolynomial A stageCountConstant n +
    preparedFiniteForwardCapPolynomial A stageCountConstant n

noncomputable def preparedFiniteForwardBranchPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  Polynomial.X * preparedFiniteForwardCapPolynomial A stageCountConstant n +
    (preparedFiniteForwardCountPolynomial A stageCountConstant n + 8) ^ 8 +
    (preparedFiniteForwardCountPolynomial A stageCountConstant n +
      Polynomial.C (stageCountConstant n)) ^ stageCountConstant n

@[simp] theorem preparedFiniteForwardParameterPolynomial_zero (A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    preparedFiniteForwardParameterPolynomial A stageCountConstant 0 = Polynomial.X := rfl

theorem preparedFiniteForwardParameterPolynomial_succ (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) :
    preparedFiniteForwardParameterPolynomial A stageCountConstant (n + 1) =
      preparedFiniteForwardParameterPolynomial A stageCountConstant n +
        preparedFiniteForwardCapPolynomial A stageCountConstant n +
        preparedFiniteForwardBranchPolynomial A stageCountConstant n + 1 := rfl

noncomputable def preparedFiniteForwardParameter (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardParameterPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardWork (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardWorkPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardCap (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardCapPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardCount (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardCountPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardBranch (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardBranchPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

@[simp] theorem preparedFiniteForwardParameter_zero (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant 0 x = x := by
  simp [preparedFiniteForwardParameter]

theorem preparedFiniteForwardWork_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardWork A stageCountConstant n x =
      (preparedFiniteForwardParameter A stageCountConstant n x + A) ^ A := by
  simp [preparedFiniteForwardWork, preparedFiniteForwardWorkPolynomial,
    preparedFiniteForwardParameter, Polynomial.eval₂_pow]

theorem preparedFiniteForwardCap_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardCap A stageCountConstant n x =
      (4 * preparedFiniteForwardParameter A stageCountConstant n x +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 16 + A) ^ A := by
  simp [preparedFiniteForwardCap, preparedFiniteForwardCapPolynomial,
    preparedFiniteForwardParameter, preparedFiniteForwardWork, Polynomial.eval₂_pow]

theorem preparedFiniteForwardCount_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardCount A stageCountConstant n x =
      preparedFiniteForwardParameter A stageCountConstant n x +
        preparedFiniteForwardCap A stageCountConstant n x := by
  simp [preparedFiniteForwardCount, preparedFiniteForwardCountPolynomial,
    preparedFiniteForwardParameter, preparedFiniteForwardCap]

theorem preparedFiniteForwardBranch_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardBranch A stageCountConstant n x =
      x * preparedFiniteForwardCap A stageCountConstant n x +
        (preparedFiniteForwardCount A stageCountConstant n x + 8) ^ 8 +
        (preparedFiniteForwardCount A stageCountConstant n x + stageCountConstant n) ^
          stageCountConstant n := by
  simp [preparedFiniteForwardBranch, preparedFiniteForwardBranchPolynomial,
    preparedFiniteForwardCap, preparedFiniteForwardCount, Polynomial.eval₂_pow]

theorem preparedFiniteForwardParameter_succ (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant (n + 1) x =
      preparedFiniteForwardParameter A stageCountConstant n x +
        preparedFiniteForwardCap A stageCountConstant n x +
        preparedFiniteForwardBranch A stageCountConstant n x + 1 := by
  simp [preparedFiniteForwardParameter, preparedFiniteForwardParameterPolynomial_succ,
    preparedFiniteForwardCap, preparedFiniteForwardBranch]

theorem preparedFiniteForwardParameter_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardParameter A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardWork_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardWork A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardCap_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCap A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardCount_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCount A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardBranch_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardBranch A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardParameter_strictMono (A : ℕ)
    (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    StrictMono (fun n => preparedFiniteForwardParameter A stageCountConstant n x) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [preparedFiniteForwardParameter_succ]
  have := preparedFiniteForwardCap_nonneg A stageCountConstant n hx
  have := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  linarith

theorem preparedFiniteForwardParameter_monotone (A : ℕ)
    (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun n => preparedFiniteForwardParameter A stageCountConstant n x) :=
  (preparedFiniteForwardParameter_strictMono A stageCountConstant hx).monotone

theorem le_preparedFiniteForwardParameter (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ preparedFiniteForwardParameter A stageCountConstant n x := by
  simpa using preparedFiniteForwardParameter_monotone A stageCountConstant hx (Nat.zero_le n)

theorem exists_preparedFiniteForwardSchedule_budget (depth A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ, n ≤ depth →
      preparedFiniteForwardParameter A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardWork A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCap A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCount A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardBranch A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) := by
  let Q : ℕ → Polynomial ℕ := fun n =>
    preparedFiniteForwardParameterPolynomial A stageCountConstant n +
      preparedFiniteForwardWorkPolynomial A stageCountConstant n +
      preparedFiniteForwardCapPolynomial A stageCountConstant n +
      preparedFiniteForwardCountPolynomial A stageCountConstant n +
      preparedFiniteForwardBranchPolynomial A stageCountConstant n
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_eval_budget (∑ n ∈ Finset.range (depth + 1), Q n)
  refine ⟨C, hC, ?_⟩
  intro x hx n hn
  have hentry : (Q n).eval₂ (Nat.castRingHom ℝ) x ≤ (x + C) ^ C := by
    apply le_trans _ (hbudget x hx)
    rw [Polynomial.eval₂_finsetSum]
    exact Finset.single_le_sum (fun i _ => natPolynomial_eval_nonneg (Q i) hx)
      (Finset.mem_range.mpr (by omega))
  have hp := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hcap := preparedFiniteForwardCap_nonneg A stageCountConstant n hx
  have hcount := preparedFiniteForwardCount_nonneg A stageCountConstant n hx
  have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  simp only [Q, Polynomial.eval₂_add] at hentry
  change preparedFiniteForwardParameter A stageCountConstant n x +
      preparedFiniteForwardWork A stageCountConstant n x +
      preparedFiniteForwardCap A stageCountConstant n x +
      preparedFiniteForwardCount A stageCountConstant n x +
      preparedFiniteForwardBranch A stageCountConstant n x ≤ (x + C) ^ C at hentry
  exact ⟨⟨hp, by linarith⟩, ⟨hw, by linarith⟩, ⟨hcap, by linarith⟩,
    ⟨hcount, by linarith⟩, ⟨hbranch, by linarith⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedFiniteStageNative_budget
    {ι : Type*} [Fintype ι]
    (K : ι → PreparedModularCanonicalDetectorResourceConstants)
    (dim : ι → ℕ) (Aprimitive : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ k : ι, ∀ {b P : ℝ},
      0 ≤ b → P ∈ Set.Icc 0 ((b + Aprimitive) ^ Aprimitive) → ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources (K k) (dim k) P L
      r.Pnative ∈ Set.Icc 0 ((b + C) ^ C) ∧
      r.nativeBudget ∈ Set.Icc 0 ((b + C) ^ C) ∧
      r.E ∈ Set.Icc 0 ((b + C) ^ C) := by
  let Ck (k : ι) := Classical.choose
    (exists_preparedModularGeneralDetector_early_native_budget (K k) (dim k))
  let base : Polynomial ℕ := (Polynomial.X + Polynomial.C Aprimitive) ^ Aprimitive
  let poly : Polynomial ℕ := ∑ k : ι, (2 * base + Polynomial.C (Ck k)) ^ Ck k
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro k b P hb hP L r
  let piece (j : ι) : ℝ := (2 * (b + Aprimitive) ^ Aprimitive + Ck j) ^ Ck j
  have hpiece (j : ι) : 0 ≤ piece j := by dsimp only [piece]; positivity
  have hsum : piece k ≤ ∑ j : ι, piece j :=
    Finset.single_le_sum (fun j _ => hpiece j) (Finset.mem_univ k)
  have htotal : (∑ j : ι, piece j) ≤ (b + C) ^ C := by
    simpa [poly, base, piece, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum]
      using hpoly b hb
  have hlocal : (2 * P + Ck k) ^ Ck k ≤ piece k := by
    apply pow_le_pow_left₀ (by have := hP.1; positivity)
    linarith only [hP.2]
  have hraise := hlocal.trans (hsum.trans htotal)
  obtain ⟨hnative, hbudget, hE⟩ :=
    (Classical.choose_spec
      (exists_preparedModularGeneralDetector_early_native_budget (K k) (dim k))).2
        hP.1 L
  exact ⟨⟨hnative.1, hnative.2.trans hraise⟩,
    ⟨hbudget.1, hbudget.2.trans hraise⟩, ⟨hE.1, hE.2.trans hraise⟩⟩

theorem exists_preparedFiniteStageNative_work_budget
    {ι : Type*} [Fintype ι]
    (K : ι → PreparedModularCanonicalDetectorResourceConstants)
    (dim : ι → ℕ) (Aprimitive : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ),
      C ≤ A → ∀ {x : ℝ}, 0 ≤ x → ∀ k : ι, ∀ {P : ℝ},
      P ∈ Set.Icc 0
        ((preparedFiniteForwardParameter A stageCountConstant n x + Aprimitive) ^
          Aprimitive) → ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources (K k) (dim k) P L
      let work := preparedFiniteForwardWork A stageCountConstant n x
      r.Pnative ∈ Set.Icc 0 work ∧
      r.nativeBudget ∈ Set.Icc 0 work ∧ r.E ∈ Set.Icc 0 work := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteStageNative_budget K dim Aprimitive
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n hCA x hx k P hP L r work
  let b := preparedFiniteForwardParameter A stageCountConstant n x
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hCA' : (C : ℝ) ≤ A := Nat.cast_le.mpr hCA
  have hA : (2 : ℝ) ≤ A := Nat.cast_le.mpr (hC.trans hCA)
  have hbase : 1 ≤ b + A := by linarith only [hb, hA]
  have hwork : (b + C) ^ C ≤ work := by
    change (b + C) ^ C ≤ preparedFiniteForwardWork A stageCountConstant n x
    rw [preparedFiniteForwardWork_eq]
    exact (pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg C))
      (add_le_add (le_refl b) hCA') C).trans (pow_le_pow_right₀ hbase hCA)
  obtain ⟨hnative, hbudget, hE⟩ := hbound k hb hP L
  exact ⟨⟨hnative.1, hnative.2.trans hwork⟩,
    ⟨hbudget.1, hbudget.2.trans hwork⟩, ⟨hE.1, hE.2.trans hwork⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
