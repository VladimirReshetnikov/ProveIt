import GowersSzemeredi.Proofs03Equivalences
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Proofs07AdditiveRestriction
import GowersSzemeredi.Sections12_13

/-! Preparing a separately Freiman frequency graph before purification,
and bounding the number of arrangements by the graph's cardinality. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Pointwise ZMod
open Finset
namespace LeanProofs.GowersSzemeredi

private def contextSwapEquiv (N : Nat) : Pair N ≃ Point N 2 where
  toFun z := ![z.2, z.1]
  invFun x := (x 1, x 0)
  left_inv z := by ext <;> simp
  right_inv x := by
    funext i
    fin_cases i <;> simp

private lemma context_cubeDifference_eq {N : Nat}
    (f : ZMod N → Complex) (z : Pair N) :
    cubeDifference f (contextSwapEquiv N z) =
      secondDifference f z.1 z.2 := by
  change cubeDifference f (Fin.cons z.2 (Fin.cons z.1 (fun i ↦ Fin.elim0 i))) =
    secondDifference f z.1 z.2
  rw [cubeDifference_cons, cubeDifference_cons]
  simp only [cubeDifference, List.ofFn_zero, iteratedDifference, secondDifference]

private lemma context_density_moment_identity (K R n : Real) (hn : n ≠ 0) :
    K * (R / n) ^ 1165 * n ^ 2 =
      (K * n) * (R ^ 1165 / n ^ 1164) := by
  field_simp [hn]

private lemma context_sum_vertical_card {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    ∑ x : ZMod N, (verticalSection B x).card = B.card := by
  convert (context_countWhere_prod (fun x y : ZMod N => (x, y) ∈ B)).symm using 1 <;>
    simp [verticalSection, countWhere] <;> congr!

private lemma context_sum_horizontal_card {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    ∑ y : ZMod N, (horizontalSection B y).card = B.card := by
  convert ((context_countWhere_prod (fun y x : ZMod N => (x, y) ∈ B)).symm.trans
      (feature_countWhere_equiv (Equiv.prodComm (ZMod N) (ZMod N))
        (fun z : Pair N => z ∈ B)).symm) using 1 <;>
    simp [horizontalSection, countWhere] <;> congr!

private lemma context_restrict_fibres {N : Nat} [NeZero N]
    (hprime : Nat.Prime N) (a : Real) (ha : 0 < a)
    (S : ZMod N → Finset (ZMod N))
    (g : ZMod N → ZMod N → Complex)
    (psi : ZMod N → ZMod N → ZMod N)
    (hg : ∀ x, DiscValued (g x))
    (hlarge : ∀ x y, y ∈ S x →
      a * N ≤ ‖fourier (difference (g x) y) (psi x y)‖) :
    ∃ T : ZMod N → Finset (ZMod N),
      (∀ x, T x ⊆ S x) ∧
      (∀ x, FreimanHom 8 (T x) (psi x)) ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((∑ x : ZMod N, (S x).card / (N : Real)) / (N : Real)) ^ 1165 *
          (N : Real) ^ 2 ≤
        ∑ x : ZMod N, ((T x).card : Real) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN0 : (N : Real) ≠ 0 := hN.ne'
  let rho : ZMod N → Real := fun x ↦ (S x).card / (N : Real)
  have hrho_nonneg (x : ZMod N) : 0 ≤ rho x := by
    dsimp only [rho]
    positivity
  have hpiece : ∀ x, ∃ T : Finset (ZMod N),
      T ⊆ S x ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          rho x ^ 1165 * (N : Real) ≤ (T.card : Real) ∧
      FreimanHom 8 T (psi x) := by
    intro x
    by_cases hx0 : (S x).card = 0
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp [rho, hx0]
      · simp [FreimanHom]
    · have hrho : 0 < rho x := by
        dsimp only [rho]
        exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hx0) hN
      have hScard : ((S x).card : Real) = rho x * N := by
        dsimp only [rho]
        field_simp [hN0]
      let tau : Real := rho x * a ^ 2
      have htau : 0 < tau := mul_pos hrho (pow_pos ha 2)
      have hsum :
          tau * (N : Real) ^ 3 ≤
            ∑ y ∈ S x, ‖fourier (difference (g x) y) (psi x y)‖ ^ 2 := by
        calc
          tau * (N : Real) ^ 3 =
              (rho x * N) * (a * N) ^ 2 := by
            dsimp only [tau]
            ring
          _ = (S x).card * (a * N) ^ 2 := by rw [← hScard]
          _ = ∑ _y ∈ S x, (a * N) ^ 2 := by simp
          _ ≤ ∑ y ∈ S x,
              ‖fourier (difference (g x) y) (psi x y)‖ ^ 2 := by
            exact Finset.sum_le_sum fun y hy ↦
              pow_le_pow_left₀ (by positivity) (hlarge x y hy) 2
      have hadd := proposition_6_1_holds N tau (g x) (S x) (psi x)
        htau (hg x) hsum
      let gamma : Real := rho x * a ^ 8
      have hgamma : 0 < gamma := mul_pos hrho (pow_pos ha 8)
      have hquad :
          gamma * (rho x * N) ^ 3 ≤ phiAdditiveCount (S x) (psi x) := by
        calc
          gamma * (rho x * N) ^ 3 = tau ^ 4 * (N : Real) ^ 3 := by
            dsimp only [gamma, tau]
            ring
          _ ≤ (phiAdditiveCount (S x) (psi x) : Real) := hadd
      obtain ⟨T, hTsub, hTcard, hTfreiman⟩ :=
        corollary_7_6_holds N (S x) (psi x) (rho x) gamma hprime hrho hgamma
          hScard hquad
      refine ⟨T, hTsub, ?_, hTfreiman⟩
      calc
        (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho x ^ 1165 *
              (N : Real) =
            (2 : Real) ^ (-(1882 : Real)) * gamma ^ 1164 * rho x *
              (N : Real) := by
          dsimp only [gamma]
          ring
        _ ≤ (T.card : Real) := hTcard
  choose T hTsub hTcard hTfreiman using hpiece
  refine ⟨T, hTsub, hTfreiman, ?_⟩
  have hmean := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (ZMod N))) (f := rho)
    (fun x _ ↦ hrho_nonneg x) 1164
  simp only [Finset.card_univ, ZMod.card, Nat.reduceAdd] at hmean
  have hpieces :
      ∑ x : ZMod N,
          (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho x ^ 1165 * N ≤
        ∑ x : ZMod N, ((T x).card : Real) := by
    exact Finset.sum_le_sum fun x _ ↦ hTcard x
  calc
    (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((∑ x : ZMod N, (S x).card / (N : Real)) / (N : Real)) ^ 1165 *
          (N : Real) ^ 2 =
        ((2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * N) *
          ((∑ x : ZMod N, rho x) ^ 1165 / (N : Real) ^ 1164) := by
      have hrhoSum :
          (∑ x : ZMod N, (S x).card / (N : Real)) =
            ∑ x : ZMod N, rho x := by rfl
      rw [hrhoSum]
      exact context_density_moment_identity
        ((2 : Real) ^ (-(1882 : Real)) * a ^ 9312)
        (∑ x : ZMod N, rho x) (N : Real) hN0
    _ ≤ ((2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * N) *
          ∑ x : ZMod N, rho x ^ 1165 := by
      exact mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = ∑ x : ZMod N,
          (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho x ^ 1165 * N := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      ac_rfl
    _ ≤ ∑ x : ZMod N, ((T x).card : Real) := hpieces

private noncomputable def contextVerticalJoin {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) : Finset (Pair N) :=
  Finset.univ.filter fun z ↦ z.2 ∈ T z.1

private noncomputable def contextHorizontalJoin {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) : Finset (Pair N) :=
  Finset.univ.filter fun z ↦ z.1 ∈ T z.2

private lemma context_vertical_join_section {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (x : ZMod N) :
    verticalSection (contextVerticalJoin T) x = T x := by
  ext y
  simp [verticalSection, contextVerticalJoin]

private lemma context_horizontal_join_section {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (y : ZMod N) :
    horizontalSection (contextHorizontalJoin T) y = T y := by
  ext x
  simp [horizontalSection, contextHorizontalJoin]

private lemma context_vertical_join_card {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) :
    (contextVerticalJoin T).card = ∑ x : ZMod N, (T x).card := by
  simpa only [context_vertical_join_section] using
    (context_sum_vertical_card (contextVerticalJoin T)).symm

private lemma context_horizontal_join_card {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) :
    (contextHorizontalJoin T).card = ∑ y : ZMod N, (T y).card := by
  simpa only [context_horizontal_join_section] using
    (context_sum_horizontal_card (contextHorizontalJoin T)).symm

private lemma context_vertical_restriction {N : Nat} [NeZero N]
    (hprime : Nat.Prime N) (a : Real) (ha : 0 < a)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (B : Finset (Pair N)) (phi : Pair N → ZMod N)
    (hlarge : ∀ z, z ∈ B →
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) :
    ∃ B' : Finset (Pair N), B' ⊆ B ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((B.card : Real) / (N : Real) ^ 2) ^ 1165 * (N : Real) ^ 2 ≤
        B'.card ∧
      ∀ x, FreimanHom 8 (verticalSection B' x) (fun y ↦ phi (x, y)) := by
  obtain ⟨T, hTsub, hTfreiman, hTcard⟩ := context_restrict_fibres hprime a ha
    (fun x ↦ verticalSection B x) (fun x ↦ difference f x)
    (fun x y ↦ phi (x, y)) (fun x ↦ difference_discValued hf x) (by
      intro x y hy
      have hxy : (x, y) ∈ B := by simpa [verticalSection] using hy
      simpa only [secondDifferenceFourier, secondDifference] using
        hlarge (x, y) hxy)
  let B' := contextVerticalJoin T
  refine ⟨B', ?_, ?_, ?_⟩
  · intro z hz
    have hzT : z.2 ∈ T z.1 := by simpa [B', contextVerticalJoin] using hz
    simpa [verticalSection] using hTsub z.1 hzT
  · have hsumReal :
        ∑ x : ZMod N, ((verticalSection B x).card : Real) = B.card := by
      exact_mod_cast context_sum_vertical_card B
    have hcardReal : (B'.card : Real) =
        ∑ x : ZMod N, ((T x).card : Real) := by
      exact_mod_cast context_vertical_join_card T
    have hdensity : (B.card : Real) / (N : Real) ^ 2 =
        (∑ x : ZMod N, (verticalSection B x).card / (N : Real)) /
          (N : Real) := by
      rw [← Finset.sum_div, hsumReal]
      field_simp [show (N : Real) ≠ 0 by exact_mod_cast NeZero.ne N]
    simpa only [← hdensity, ← hcardReal] using hTcard
  · intro x
    rw [context_vertical_join_section]
    exact hTfreiman x

private lemma context_horizontal_restriction {N : Nat} [NeZero N]
    (hprime : Nat.Prime N) (a : Real) (ha : 0 < a)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (B : Finset (Pair N)) (phi : Pair N → ZMod N)
    (hlarge : ∀ z, z ∈ B →
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) :
    ∃ B' : Finset (Pair N), B' ⊆ B ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((B.card : Real) / (N : Real) ^ 2) ^ 1165 * (N : Real) ^ 2 ≤
        B'.card ∧
      ∀ y, FreimanHom 8 (horizontalSection B' y) (fun x ↦ phi (x, y)) := by
  obtain ⟨T, hTsub, hTfreiman, hTcard⟩ := context_restrict_fibres hprime a ha
    (fun y ↦ horizontalSection B y) (fun y ↦ difference f y)
    (fun y x ↦ phi (x, y)) (fun y ↦ difference_discValued hf y) (by
      intro y x hx
      have hxy : (x, y) ∈ B := by simpa [horizontalSection] using hx
      have h := hlarge (x, y) hxy
      unfold secondDifferenceFourier secondDifference at h
      rw [difference_comm f x y] at h
      exact h)
  let B' := contextHorizontalJoin T
  refine ⟨B', ?_, ?_, ?_⟩
  · intro z hz
    have hzT : z.1 ∈ T z.2 := by simpa [B', contextHorizontalJoin] using hz
    simpa [horizontalSection] using hTsub z.2 hzT
  · have hsumReal :
        ∑ y : ZMod N, ((horizontalSection B y).card : Real) = B.card := by
      exact_mod_cast context_sum_horizontal_card B
    have hcardReal : (B'.card : Real) =
        ∑ y : ZMod N, ((T y).card : Real) := by
      exact_mod_cast context_horizontal_join_card T
    have hdensity : (B.card : Real) / (N : Real) ^ 2 =
        (∑ y : ZMod N, (horizontalSection B y).card / (N : Real)) /
          (N : Real) := by
      rw [← Finset.sum_div, hsumReal]
      field_simp [show (N : Real) ≠ 0 by exact_mod_cast NeZero.ne N]
    simpa only [← hdensity, ← hcardReal] using hTcard
  · intro y
    rw [context_horizontal_join_section]
    exact hTfreiman y

private lemma context_cor76_constant_lower (a : Real) (ha : 0 ≤ a)
    (haHalf : a ≤ 1 / 2) :
    a ^ 1882 ≤ (2 : Real) ^ (-(1882 : Real)) := by
  calc
    a ^ 1882 ≤ (1 / 2 : Real) ^ 1882 :=
      pow_le_pow_left₀ ha haHalf 1882
    _ = (2 : Real) ^ (-(1882 : Real)) := by
      rw [Real.rpow_neg (by norm_num), one_div, inv_pow]
      exact congrArg (fun x : Real => x⁻¹)
        (Real.rpow_natCast (2 : Real) 1882).symm

private lemma context_restriction_coefficient {a beta : Real} {e : Nat}
    (ha : 0 ≤ a) (haHalf : a ≤ 1 / 2) (hbeta : a ^ e ≤ beta) :
    a ^ (1882 + 9312 + e * 1165) ≤
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * beta ^ 1165 := by
  calc
    _ = a ^ 1882 * a ^ 9312 * (a ^ e) ^ 1165 := by
      rw [pow_add, pow_add, pow_mul]
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_right (context_cor76_constant_lower a ha haHalf)
        (pow_nonneg ha _))
      (pow_le_pow_left₀ (pow_nonneg ha _) hbeta _) (by positivity) (by positivity)

private abbrev contextTailCode {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :=
  (Fin 15 → ↑B) × ZMod N × ZMod N

private def contextEncodeArrangement {N : Nat} [NeZero N]
    (B : Finset (Pair N))
    (R : {R : DArrangement N 8 // R.IsIn B}) : contextTailCode B :=
  (fun i ↦ ⟨(R.1.x i.succ, R.1.y i.succ), (R.2.2 i.succ).1⟩,
    R.1.y 0, R.1.height)

private lemma contextEncodeArrangement_injective {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    Function.Injective (contextEncodeArrangement B) := by
  intro R S hcode
  apply Subtype.ext
  have hfun :
      (fun i : Fin 15 ↦
        (⟨(R.1.x i.succ, R.1.y i.succ), (R.2.2 i.succ).1⟩ : ↑B)) =
        fun i : Fin 15 ↦
          ⟨(S.1.x i.succ, S.1.y i.succ), (S.2.2 i.succ).1⟩ :=
    congrArg Prod.fst hcode
  have hxTail : ∀ i : Fin 15, R.1.x i.succ = S.1.x i.succ := by
    intro i
    exact congrArg (fun q ↦ (q i : Pair N).1) hfun
  have hyTail : ∀ i : Fin 15, R.1.y i.succ = S.1.y i.succ := by
    intro i
    exact congrArg (fun q ↦ (q i : Pair N).2) hfun
  have hx : R.1.x = S.1.x :=
    lemma134_additive_ext R.2.1 S.2.1 hxTail
  have hy0 : R.1.y 0 = S.1.y 0 :=
    congrArg (fun c ↦ c.2.1) hcode
  have hy : R.1.y = S.1.y := by
    funext i
    refine Fin.cases hy0 (fun j ↦ hyTail j) i
  have hh : R.1.height = S.1.height :=
    congrArg (fun c ↦ c.2.2) hcode
  exact Prod.ext hx (Prod.ext hy hh)

theorem context_arrangementCount_le_card_pow {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    arrangementCount 8 B ≤ B.card ^ 15 * N ^ 2 := by
  classical
  unfold arrangementCount countWhere
  calc
    (Finset.univ.filter fun R : DArrangement N 8 ↦ R.IsIn B).card =
        Fintype.card {R : DArrangement N 8 // R.IsIn B} := by
      rw [Finset.filter_congr_decidable]
      exact (Fintype.card_subtype _).symm
    _ ≤ Fintype.card (contextTailCode B) :=
      Fintype.card_le_of_injective (contextEncodeArrangement B)
        (contextEncodeArrangement_injective B)
    _ = B.card ^ 15 * N ^ 2 := by
      simp only [contextTailCode, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, ZMod.card]
      ring

/-- Before purification, retain the exact two-fibre exponent rather than
rounding it to `2^24`. The prime threshold is unnecessary for this preparation. -/
theorem section13_prepared_frequency_graph {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnotUniform : ¬ UniformOfDegree f alpha 3) :
    ∃ A : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      (alpha / 2) ^ (14409429 : Nat) * (N : Real) ^ 2 ≤ A.card ∧
      SeparatelyFreimanEight A phi ∧
      ∀ z, z ∈ A → (alpha / 2) * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  let a : Real := alpha / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have haHalf : a ≤ 1 / 2 := by dsimp only [a]; nlinarith
  have haOne : a ≤ 1 := haHalf.trans (by norm_num)
  have hprime : Nat.Prime N := Fact.out
  have hNreal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos hNreal 2
  obtain ⟨hi_ii, hii_iii, _hii_iv, _hi_v, _hiii_vi, hvi_iii,
      _hvi_vii, hvii_vi⟩ :=
    lemma_3_1_holds N 3 f (by omega) hf alpha a a
      halpha.le halphaOne ha.le haOne ha.le haOne
  have hnotvii : ¬ higherUniformConditionvii f a 3 := by
    intro hvii
    have hvi := hvii_vi (le_refl a) hvii
    have hiii := hvi_iii (by dsimp only [a]; ring_nf; exact le_rfl) hvi
    exact hnotUniform (hi_ii.mpr (hii_iii.mpr hiii))
  let P : Point N 2 → Prop := fun x ↦
    ∃ r : ZMod N, a * N ≤ ‖fourier (cubeDifference f x) r‖
  have hcount : a * (N : Real) ^ 2 < (countWhere P : Real) := by
    unfold higherUniformConditionvii at hnotvii
    simp only [Nat.reduceSub] at hnotvii
    exact lt_of_not_ge hnotvii
  let good : Pair N → Prop := fun z ↦ P (contextSwapEquiv N z)
  let A0 : Finset (Pair N) := Finset.univ.filter good
  have hcountEq : countWhere P = A0.card := by
    calc
      countWhere P = countWhere (fun z : Pair N ↦ P (contextSwapEquiv N z)) :=
        feature_countWhere_equiv (contextSwapEquiv N) P
      _ = A0.card := by
        unfold A0 countWhere
        apply congrArg Finset.card
        ext z
        simp [good]
  have hA0card : a * (N : Real) ^ 2 ≤ A0.card := by
    rw [hcountEq] at hcount
    exact hcount.le
  let phi : Pair N → ZMod N := fun z ↦
    if hz : good z then Classical.choose hz else 0
  have hphi (z : Pair N) (hz : z ∈ A0) :
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
    have hzgood : good z := by simpa [A0] using hz
    have hzlarge := Classical.choose_spec hzgood
    unfold secondDifferenceFourier
    rw [← context_cubeDifference_eq f z]
    simpa only [phi, dif_pos hzgood] using hzlarge
  obtain ⟨B1, hB1sub, hB1raw, hB1vertical⟩ :=
    context_vertical_restriction hprime a ha f hf A0 phi hphi
  have hA0density : a ≤ (A0.card : Real) / (N : Real) ^ 2 :=
    (le_div_iff₀ hN2).2 hA0card
  have hB1coefficient := context_restriction_coefficient (e := 1) ha.le haHalf
    (by simpa only [pow_one] using hA0density)
  have hB1card : a ^ 12359 * (N : Real) ^ 2 ≤ B1.card :=
    (mul_le_mul_of_nonneg_right hB1coefficient hN2.le).trans hB1raw
  have hB1density : a ^ 12359 ≤ (B1.card : Real) / (N : Real) ^ 2 :=
    (le_div_iff₀ hN2).2 hB1card
  have hB1large (z : Pair N) (hz : z ∈ B1) :
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ :=
    hphi z (hB1sub hz)
  obtain ⟨B2, hB2sub, hB2raw, hB2horizontal⟩ :=
    context_horizontal_restriction hprime a ha f hf B1 phi hB1large
  have hB2coefficient := context_restriction_coefficient ha.le haHalf hB1density
  refine ⟨B2, phi, (mul_le_mul_of_nonneg_right hB2coefficient hN2.le).trans hB2raw,
    ⟨?_, hB2horizontal⟩, ?_⟩
  · intro x
    have hsec : (↑(verticalSection B2 x) : Set (ZMod N)) ⊆ ↑(verticalSection B1 x) := by
      intro y hy
      have hyB2 : (x, y) ∈ B2 := by simpa [verticalSection] using hy
      simpa [verticalSection] using hB2sub hyB2
    exact IsAddFreimanHom.subset hsec (hB1vertical x) (Set.mapsTo_univ _ _)
  · intro z hz
    exact hB1large z (hB2sub hz)

end LeanProofs.GowersSzemeredi
