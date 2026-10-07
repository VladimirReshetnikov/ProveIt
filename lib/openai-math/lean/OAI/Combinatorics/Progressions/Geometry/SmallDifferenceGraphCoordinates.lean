import OAI.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery

namespace OAI

section

namespace Erdos3

open scoped Pointwise BigOperators
open CyclicCrootSisask

theorem exists_small_difference_graph_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    let K := (2 ^ 14 : ℝ) * (Real.exp (p + 13 * Fintype.card I)) ^ 6
    let z := roundedModelLogBudget p (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J ⊆ H, J.Nonempty ∧ δ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
          FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x := by
  intro K z δ
  classical
  let A := additiveGraph H b
  have hK : Real.exp p ≤ K := by
    calc
      _ ≤ Real.exp (6 * (p + 13 * Fintype.card I)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
      _ = Real.exp (p + 13 * Fintype.card I) ^ 6 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ K := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hAsmall : ((A - A).card : ℝ) ≤ K * A.card := by
    rw [show A.card = H.card from additiveGraph_card H b]
    exact hsmall.trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))
  obtain ⟨Q, S, B, f, hQ, hS, hSA, hASsize, hB, _, _, hf, hQsize, hdensity⟩ :=
    FreimanModel.exists_variableIntegerGraph_cyclic_model N M A (hH.image _) (by positivity) hAsmall
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hdensity' : Real.exp (-z) * Q ≤ (B.card : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
    exact (exp_neg_roundedModelLogBudget_le_density p (Fintype.card I)).trans hdensity
  obtain ⟨F, hFS, hF, hFsize, r, R, Φ, base, hrank, hbox, hinj, hrepr⟩ :=
    FreimanModel.exists_bounded_affine_box_of_cyclic_model S hS B hB f hf
      (roundedModelLogBudget_nonneg p (Fintype.card I)) hdensity'
  have hboxSize : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
      2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card := by
    have hcast : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ Q := by exact_mod_cast hbox
    exact hcast.trans (by simpa only [A, additiveGraph_card] using hQsize)
  have hFA : F ⊆ A.image (FreimanModel.variableIntegerGraphLift N M) := hFS.trans hSA
  let π : (Option I → ℤ) → ZMod N := fun v => (v none : ZMod N)
  have hback (v : Option I → ℤ) (hv : v ∈ F) :
      π v ∈ H ∧ FreimanModel.variableIntegerGraphLift N M (π v, b (π v)) = v := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hFA hv)
    obtain ⟨hyH, hyb⟩ := (mem_additiveGraph_iff H b y).mp hy
    have hπ : π (FreimanModel.variableIntegerGraphLift N M y) = y.1 := by simp [π]
    rw [hπ]
    exact ⟨hyH, congrArg (FreimanModel.variableIntegerGraphLift N M) (Prod.ext rfl hyb.symm)⟩
  let J := F.image π
  have hπinj : Set.InjOn π (F : Set _) := by
    intro x hx y hy hxy
    calc
      x = FreimanModel.variableIntegerGraphLift N M (π x, b (π x)) := (hback x hx).2.symm
      _ = FreimanModel.variableIntegerGraphLift N M (π y, b (π y)) := by rw [hxy]
      _ = y := (hback y hy).2
  have hFcard : F.card = J.card := (Finset.card_image_of_injOn hπinj).symm
  have hJ : J ⊆ H := by
    intro h hh
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hh
    exact (hback v hv).1
  have hHS : (H.card : ℝ) ≤ 16 ^ (Fintype.card I + 2) * (S.card : ℝ) := by
    exact_mod_cast (show H.card ≤ 16 ^ (Fintype.card I + 2) * S.card by
      simpa only [A, additiveGraph_card] using hASsize)
  have hretain : δ * (S.card : ℝ) ≤ (J.card : ℝ) := by
    simpa only [hFcard] using hFsize
  refine ⟨J, hJ, hF.image _, ?_, r, R, Φ, base, hrank, hboxSize, hinj, ?_⟩
  · calc
      δ * (H.card : ℝ) ≤ δ * (16 ^ (Fintype.card I + 2) * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hHS (Real.exp_nonneg _)
      _ = 16 ^ (Fintype.card I + 2) * (δ * S.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hretain (by positivity)
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hh
    rw [(hback v hv).2]
    exact hrepr v hv

theorem exists_small_difference_graph_proper_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    let K := (2 ^ 14 : ℝ) * (Real.exp (p + 13 * Fintype.card I)) ^ 6
    let z := roundedModelLogBudget p (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J₀ ⊆ H, J₀.Nonempty ∧ δ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
         let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
           ∃ base : Option I → ℤ,
             Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
             ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
               FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x) := by
  intro K z δ
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, base, hrank, hvolume, _, hrepr⟩ :=
    exists_small_difference_graph_coordinates N M H hH b hp hsmall
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  have hall (h : {h // h ∈ J₀}) : ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
      FreimanModel.variableIntegerGraphLift N M (h.val, b h.val) = base + Φ x :=
    hrepr h.val h.property
  choose x hx hgraph using hall
  have hspace (h : {h // h ∈ J₀}) : h.val = (reduce base).1 + η (x h) := by
    change h.val = (reduce base).1 + (reduce (Φ (x h))).1
    have hh := congrArg (fun v => (reduce v).1) (hgraph h)
    simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add,
      Prod.fst_add] using hh
  obtain ⟨J, hJJ₀, hJ, hretain, t, hproper, hsmallBox⟩ :=
    exists_dense_proper_coordinate_restriction J₀ hJ₀ R η (reduce base).1 x hx hspace
  refine ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume, J, hJJ₀,
    hJ, hretain, base + Φ t, hproper, ?_⟩
  intro h hh
  let h₀ : {h // h ∈ J₀} := ⟨h, hJJ₀ hh⟩
  refine ⟨x h₀ - t, hsmallBox ⟨h, hh⟩, ?_⟩
  rw [hgraph h₀, map_sub]
  abel

theorem exists_small_difference_graph_affine_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    ∃ J ⊆ H, J.Nonempty ∧
      Real.exp (-properAffineRecoveryLogLoss p (Fintype.card I)) * H.card ≤ (J.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ properAffineRankBound p (Fintype.card I) ∧
        (let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         Set.InjOn η (centeredIntegerBox R : Set _)) ∧
        ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
          FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x := by
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
      J, hJJ₀, hJ, hretain, base, hproper, hrepr⟩ :=
    exists_small_difference_graph_proper_coordinates N M H hH b hp hsmall
  have hfactor : ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (p + 13 * Fintype.card I))⁻¹ ≤ 1 := by
    calc
      _ ≤ (Real.exp (p + 13 * Fintype.card I))⁻¹ :=
        mul_le_of_le_one_left (by positivity) (by norm_num)
      _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_exp_iff.mpr (by positivity))
  have hweaker : Real.exp (-(quarticBogolyubovProgressionConstant *
      (roundedModelLogBudget p (Fintype.card I) + 1) ^ 8)) *
      ((2 ^ 4 : ℝ)⁻¹ * (Real.exp (p + 13 * Fintype.card I))⁻¹ * H.card) ≤
      16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) := by
    apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hfactor
  have hdense₀ := exp_neg_affineRecoveryLogLoss_card_le p (Fintype.card I) H.card J₀.card hweaker
  have hcost := properAffineSelection_bounds hp (Fintype.card I) r
    (∏ i, (2 * R i + 1)) H.card J₀.card J.card hJ₀.card_pos hrank hvolume hdense₀ hretain
  exact ⟨J, hJJ₀.trans hJ₀H, hJ, hcost.2, r,
    (fun i => R i / (2 * ((2 ^ r * ∏ j, (2 * R j + 1)) / J₀.card + 1))),
    Φ, base, hrank, hproper, hrepr⟩

end Erdos3

end

end OAI
