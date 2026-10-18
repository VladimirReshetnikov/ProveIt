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
      secondDifference f z.1 z.2 := by abel

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
  let rho : ZMod N → Real := fun x ↦ (S x).card / (N : Real)
  have hScard (x : ZMod N) : ((S x).card : Real) = rho x * N := (div_mul_cancel₀ _ hN.ne').symm
  -- in each fibre: Proposition 6.1 at density `ρ a²`, then Corollary 7.6 with `γ = ρ a⁸`
  have hpiece (x : ZMod N) : ∃ T : Finset (ZMod N), T ⊆ S x ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho x ^ 1165 * N ≤ T.card ∧
      FreimanHom 8 T (psi x) := by
    rcases Nat.eq_zero_or_pos (S x).card with hx0 | hx0
    · exact ⟨∅, Finset.empty_subset _, by simp [rho, hx0], by simp [FreimanHom]⟩
    have hrho : 0 < rho x := div_pos (by exact_mod_cast hx0) hN
    have hadd := proposition_6_1_holds N (rho x * a ^ 2) (g x) (S x) (psi x)
      (mul_pos hrho (pow_pos ha 2)) (hg x) <| calc
        rho x * a ^ 2 * (N : Real) ^ 3 = ∑ _y ∈ S x, (a * N) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hScard]
          ring
        _ ≤ _ := Finset.sum_le_sum fun y hy ↦ pow_le_pow_left₀ (by positivity) (hlarge x y hy) 2
    obtain ⟨T, hTsub, hTcard, hTfreiman⟩ := corollary_7_6_holds N (S x) (psi x) (rho x)
      (rho x * a ^ 8) hprime hrho (mul_pos hrho (pow_pos ha 8)) (hScard x) (by linarith)
    exact ⟨T, hTsub, hTcard.trans_eq' (by ring), hTfreiman⟩
  choose T hTsub hTcard hTfreiman using hpiece
  refine ⟨T, hTsub, hTfreiman, ?_⟩
  -- average the fibre bounds with the power-mean inequality
  have hmean := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := rho)
    (fun x _ ↦ div_nonneg (Nat.cast_nonneg _) hN.le) 1164
  simp only [Finset.card_univ, ZMod.card, Nat.reduceAdd] at hmean
  calc _ = (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * N *
        ((∑ x, rho x) ^ 1165 / (N : Real) ^ 1164) := context_density_moment_identity _ _ _ hN.ne'
    _ ≤ (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * N * ∑ x, rho x ^ 1165 := by gcongr
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => (hTcard x).trans_eq' (by ring)

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
    (verticalSection B) (difference f) (fun x y ↦ phi (x, y)) (difference_discValued hf)
    fun x y hy => by
      simpa only [secondDifferenceFourier, secondDifference] using
        hlarge (x, y) (by simpa [verticalSection] using hy)
  rw [← Finset.sum_div, div_div, ← sq, ← Nat.cast_sum, context_sum_vertical_card, ← Nat.cast_sum,
    ← context_vertical_join_card] at hTcard
  refine ⟨contextVerticalJoin T, fun z hz => ?_, hTcard, fun x => ?_⟩
  · simpa [verticalSection] using hTsub z.1 (by simpa [contextVerticalJoin] using hz)
  · simpa only [context_vertical_join_section] using hTfreiman x

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
    (horizontalSection B) (difference f) (fun y x ↦ phi (x, y)) (difference_discValued hf)
    fun y x hx => by
      simpa only [secondDifferenceFourier, secondDifference, difference_comm f x y] using
        hlarge (x, y) (by simpa [horizontalSection] using hx)
  rw [← Finset.sum_div, div_div, ← sq, ← Nat.cast_sum, context_sum_horizontal_card,
    ← Nat.cast_sum, ← context_horizontal_join_card] at hTcard
  refine ⟨contextHorizontalJoin T, fun z hz => ?_, hTcard, fun y => ?_⟩
  · simpa [horizontalSection] using hTsub z.2 (by simpa [contextHorizontalJoin] using hz)
  · simpa only [context_horizontal_join_section] using hTfreiman y

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
    exact fun i => congrArg (fun q ↦ (q i : Pair N).1) hfun
  have hyTail : ∀ i : Fin 15, R.1.y i.succ = S.1.y i.succ := by
    exact fun i => congrArg (fun q ↦ (q i : Pair N).2) hfun
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
  have ha : 0 < a := by positivity
  have haHalf : a ≤ 1 / 2 := by dsimp only [a]; linarith
  have haOne : a ≤ 1 := haHalf.trans (by norm_num)
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos (Nat.cast_pos.mpr (NeZero.pos N)) 2
  obtain ⟨hi_ii, hii_iii, -, -, -, hvi_iii, -, hvii_vi⟩ := lemma_3_1_holds N 3 f (by omega) hf
    alpha a a halpha.le halphaOne ha.le haOne ha.le haOne
  have hnotvii : ¬ higherUniformConditionvii f a 3 := fun hvii => hnotUniform
    (hi_ii.mpr (hii_iii.mpr (hvi_iii (by dsimp only [a]; linarith) (hvii_vi le_rfl hvii))))
  -- `A0`: the pairs whose second difference has a large Fourier coefficient
  let P : Point N 2 → Prop := fun x ↦ ∃ r : ZMod N, a * N ≤ ‖fourier (cubeDifference f x) r‖
  let good : Pair N → Prop := fun z ↦ P (contextSwapEquiv N z)
  let A0 : Finset (Pair N) := Finset.univ.filter good
  have hA0card : a * (N : Real) ^ 2 ≤ A0.card := by
    have h : countWhere P = A0.card := by
      rw [feature_countWhere_equiv (contextSwapEquiv N) P, countWhere,
        Finset.filter_congr_decidable]
    rw [← h]
    exact (lt_of_not_ge hnotvii).le
  let phi : Pair N → ZMod N := fun z ↦ if hz : good z then Classical.choose hz else 0
  have hphi (z : Pair N) (hz : z ∈ A0) :
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
    have hzgood : good z := (Finset.mem_filter.mp hz).2
    rw [secondDifferenceFourier, ← context_cubeDifference_eq f z]
    simpa only [phi, dif_pos hzgood] using Classical.choose_spec hzgood
  -- restrict vertically, then horizontally, tracking the density exponent
  obtain ⟨B1, hB1sub, hB1raw, hB1vertical⟩ :=
    context_vertical_restriction Fact.out a ha f hf A0 phi hphi
  have hB1 : a ^ 12359 ≤ (B1.card : Real) / (N : Real) ^ 2 := (le_div_iff₀ hN2).2
    ((mul_le_mul_of_nonneg_right (context_restriction_coefficient (e := 1) ha.le haHalf
      ((pow_one a).trans_le ((le_div_iff₀ hN2).2 hA0card))) hN2.le).trans hB1raw)
  obtain ⟨B2, hB2sub, hB2raw, hB2horizontal⟩ :=
    context_horizontal_restriction Fact.out a ha f hf B1 phi fun z hz => hphi z (hB1sub hz)
  refine ⟨B2, phi, (mul_le_mul_of_nonneg_right (context_restriction_coefficient ha.le haHalf hB1)
    hN2.le).trans hB2raw, ⟨fun x => ?_, hB2horizontal⟩, fun z hz => hphi z (hB1sub (hB2sub hz))⟩
  refine IsAddFreimanHom.subset (fun y hy => ?_) (hB1vertical x) (Set.mapsTo_univ _ _)
  simpa [verticalSection] using hB2sub (by simpa [verticalSection] using hy)

end LeanProofs.GowersSzemeredi
