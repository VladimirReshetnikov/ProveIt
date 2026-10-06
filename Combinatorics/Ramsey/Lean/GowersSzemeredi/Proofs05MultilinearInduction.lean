import GowersSzemeredi.Proofs05MultilinearBudgets

/-! # The complete multilinear height induction on proper boxes -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi

/-- The geometric assertion at a specified number of permitted monomials. -/
def MultilinearHeightAt (k h : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (F : Finset (Finset (Fin k))),
    MonomialFamilyClosed F → F.card = h →
    ∀ (c : Finset (Fin k) → ZMod N) (P : Box N k), P.IsProper →
    ∀ m : Nat, multilinearHeightThreshold k h ≤ m → m ≤ P.width →
      ∃ M : Nat, ∃ Q : Fin M → Box N k,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, (m : Real) ^ multilinearHeightExponent k h ≤ (Q j).width) ∧
        ∀ j, diameterAtMostReal ((Q j).carrier.image (multiaffineEval F c))
          (multilinearHeightCoefficient k h * (m : Real) ^ (-multilinearHeightExponent k h) * N)

private theorem constant_box_partition {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) (f : Point N k → ZMod N) (a : ZMod N)
    (hf : ∀ x, f x = a) (W D : Real) (hW : W ≤ P.width) (hD : 0 ≤ D) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧ (∀ j, W ≤ (Q j).width) ∧
      ∀ j, diameterAtMostReal ((Q j).carrier.image f) D := by
  classical
  refine ⟨1, fun _ => P, ?_, fun _ => hP, fun _ => hW, ?_⟩
  · constructor
    · intro x; simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · intro _
    refine ⟨0, ⟨a, ?_⟩, by simpa using hD⟩
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    simp [hf, modInterval, ModAP.carrier]

private theorem height_constant_partition {N k h m : Nat} [NeZero N]
    (hk : 2 ≤ k) (P : Box N k) (hP : P.IsProper)
    (hm : multilinearHeightThreshold k h ≤ m) (hmP : m ≤ P.width)
    (f : Point N k → ZMod N) (a : ZMod N) (hf : ∀ x, f x = a) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (m : Real) ^ multilinearHeightExponent k h ≤ (Q j).width) ∧
      ∀ j, diameterAtMostReal ((Q j).carrier.image f)
        (multilinearHeightCoefficient k h * (m : Real) ^ (-multilinearHeightExponent k h) * N) := by
  have hm1 : (1 : Real) ≤ m := by
    have := (multilinearHeightThreshold_bounds hk h).1.trans hm
    exact_mod_cast (show 1 ≤ m by omega)
  have hK := multilinearPartitionConstant_eight_le hk
  have hK1 : (1 : Real) ≤ multilinearPartitionConstant k := by exact_mod_cast (show 1 ≤ multilinearPartitionConstant k by omega)
  have hpow1 : (1 : Real) ≤ (multilinearPartitionConstant k : Real) ^ h := one_le_pow₀ hK1
  have he : multilinearHeightExponent k h ≤ 1 := by
    exact (inv_le_one₀ (by positivity)).2 hpow1
  have hwidth : (m : Real) ^ multilinearHeightExponent k h ≤ P.width := by
    calc
      _ ≤ (m : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hm1 he
      _ = m := Real.rpow_one _
      _ ≤ P.width := by exact_mod_cast hmP
  apply constant_box_partition P hP f a hf _ _ hwidth
  unfold multilinearHeightCoefficient
  positivity

/-- Every stage of the height induction, including all integral rounding. -/
theorem multilinearHeightAt_holds (k : Nat) (hk : 2 ≤ k) (h : Nat) :
    MultilinearHeightAt k h := by
  induction h with
  | zero =>
    intro N _ F hF hcard c P hP m hm hmP
    have hFempty : F = ∅ := Finset.card_eq_zero.mp hcard
    apply height_constant_partition hk P hP hm hmP (multiaffineEval F c) 0
    intro x
    simp [hFempty, multiaffineEval]
  | succ h ih =>
    intro N _ F hF hcard c P hP m hm hmP
    have hFnonempty : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨A, hA, hmax⟩ := monomialFamily_exists_maximal F hFnonempty
    by_cases hAempty : A = ∅
    · have hFsingle : F = {∅} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨by simpa [hAempty] using hA, ?_⟩
        intro S hS
        simpa [hAempty] using hmax S hS (by simp [hAempty])
      apply height_constant_partition hk P hP hm hmP (multiaffineEval F c) (c ∅)
      intro x
      simp [hFsingle, multiaffineEval]
    · have hd : 1 ≤ A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAempty)
      have hdk : A.card ≤ k := by simpa using Finset.card_le_univ A
      have hmN : m ≤ N := hmP.trans (P.width_le_modulus hP)
      have hmT : polynomialPartitionThreshold k ≤ m :=
        (multilinearHeightThreshold_bounds hk (h + 1)).2.trans hm
      obtain ⟨p, hp, hp2, hrec⟩ := multilinear_coefficient_recurrence hk hd hdk hmT hmN
        (c A * P.commonDiff ^ A.card)
      obtain ⟨u, hu, hu4, hthreshold, hwidth, hdiam, herror⟩ :=
        multilinear_height_scale_exists hk hm
      have hpu : p * u ^ 2 ≤ P.width := by
        apply le_trans (b := m) _ hmP
        have hsquare : (p * u ^ 2) ^ 2 ≤ m ^ 2 := by
          calc
            _ = p ^ 2 * u ^ 4 := by ring
            _ ≤ m * m := Nat.mul_le_mul hp2 hu4
            _ = m ^ 2 := by ring
        nlinarith
      let W := (m : Real) ^ multilinearHeightExponent k (h + 1)
      let D := multilinearHeightCoefficient k h * (m : Real) ^ (-multilinearHeightExponent k (h + 1)) * N
      let E := (2 : Real) ^ (-(k : Real)) * (m : Real) ^ (-multilinearHeightExponent k (h + 1)) * N
      have hm0 : (0 : Real) < m := by
        have := (multilinearHeightThreshold_bounds hk (h + 1)).1.trans hm
        exact_mod_cast (show 0 < m by omega)
      have hW : 0 < W := Real.rpow_pos_of_pos hm0 _
      have hcoef : (u : Real) ^ A.card *
          centeredAbs (c A * ((p : ZMod N) * P.commonDiff) ^ A.card) ≤ E := by
        have heq : (p : ZMod N) ^ A.card * (c A * P.commonDiff ^ A.card) =
            c A * ((p : ZMod N) * P.commonDiff) ^ A.card := by rw [mul_pow]; ring
        rw [heq] at hrec
        have hu1 : (1 : Real) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
        calc
          _ ≤ (u : Real) ^ k * ((m : Real) ^ (-((k : Real) * 2 ^ (k + 1))⁻¹) * N) :=
            mul_le_mul (pow_le_pow_right₀ hu1 hdk) hrec (by positivity) (by positivity)
          _ = ((u : Real) ^ k * (m : Real) ^ (-((k : Real) * 2 ^ (k + 1))⁻¹)) * N := by ring
          _ ≤ E := mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg N)
      have hchild (B : Box N k) (hB : B.IsProper) (hBlow : u - 1 ≤ B.width)
          (_hBhigh : B.width ≤ u) (c' : Finset (Fin k) → ZMod N) :
          ∃ L : Nat, ∃ R : Fin L → Box N k,
            IsBoxPartition R B ∧ (∀ j, (R j).IsProper) ∧
            (∀ j, W ≤ (R j).width) ∧
            ∀ j, diameterAtMostReal ((R j).carrier.image (multiaffineEval (F.erase A) c')) D := by
        have hcard' : (F.erase A).card = h := by rw [Finset.card_erase_of_mem hA, hcard]; omega
        obtain ⟨L, R, hRpart, hRproper, hRwidth, hRdiam⟩ :=
          ih N (F.erase A) (hF.erase_maximal A hmax) hcard' c' B hB (u - 1) hthreshold hBlow
        refine ⟨L, R, hRpart, hRproper, fun j => hwidth.trans (hRwidth j), ?_⟩
        intro j
        apply diameterAtMostReal_mono (Finset.Subset.refl _) (hRdiam j)
        have hC : 0 ≤ multilinearHeightCoefficient k h := by unfold multilinearHeightCoefficient; positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiam hC) (Nat.cast_nonneg N)
      obtain ⟨M, Q, hQpart, hQproper, hQwidth, hQdiam⟩ :=
        multiaffine_box_height_step (by omega) F hF A hA hmax c P hP p u
          (by omega) (by omega) hpu W D E hW hcoef hchild
      refine ⟨M, Q, hQpart, hQproper, hQwidth, ?_⟩
      have hED : E + D = multilinearHeightCoefficient k (h + 1) *
          (m : Real) ^ (-multilinearHeightExponent k (h + 1)) * N := by
        dsimp [E, D, multilinearHeightCoefficient]
        rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_natCast]
        push_cast
        ring
      intro j
      simpa only [hED] using hQdiam j

end LeanProofs.GowersSzemeredi
