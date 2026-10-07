/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.ControlledRefilteredCyclicExpansion
import OAI.Combinatorics.Progressions.Estimates.CyclicCellAnchors
import OAI.Combinatorics.Progressions.Estimates.SlowInverseControl

namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_controlled_refiltered_residue_expansion (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      1 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
            (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
          E.filtration = (pi D).filtration.gradedRefiltration W ∧
          E.lattice = (pi D).lattice.comap
            (NilpotentLieBCHGroup.map
              (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
              ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
          E.GeometryComplexityLE ((p + C) ^ C) ∧
          ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
            ∃ Q : RationalFilteredNilmanifold
                (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
              Q.filtration = E.filtration.quotientTop ∧
              Q.lattice = E.lattice.map
                (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE ((p + C) ^ C) ∧
              (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C) ^ C) ∧
              RefilteredResidueExpansionSpec D a W E Q p q r P ((p + C) ^ C) := by
  obtain ⟨k₀, _, hslowValues⟩ := exists_slow_inverse_control (s + 1) r
  let k := max r k₀
  obtain ⟨a₀, _, hreps⟩ := exists_native_residue_representatives (s + 1)
  obtain ⟨b₀, _, hmodels⟩ := exists_controlled_lower_refiltered_reconstruction s k
  obtain ⟨c₀, _, hexpand⟩ := exists_lower_refiltered_cyclic_expansion s k
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C a₀) ^ a₀
  let B := (T + Polynomial.C b₀) ^ b₀
  let F := (T + Polynomial.C c₀) ^ c₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + B + F)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  classical
  let w₁ := fun _ : Unit => 1
  have hp₀ : 0 ≤ p := by linarith
  obtain ⟨P, m, hP, hm, hPb, hmb, hperiod⟩ :=
    hreps (D a) w₁ (fun _ => by decide) p hp₀ (hD a)
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp) q hq hqp
  let t := p + (p + a₀) ^ a₀
  let cost := (p + C) ^ C
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp₀.trans hpt
  have hat : (p + a₀) ^ a₀ ≤ t := le_add_of_nonneg_left hp₀
  have hsum : t + (t + b₀) ^ b₀ + (t + c₀) ^ c₀ ≤ cost := by
    simpa [T, B, F, X, t, cost, Polynomial.eval₂_pow] using hbudget p hp₀
  have hb₀ : 0 ≤ (t + b₀) ^ b₀ := pow_nonneg (by positivity) _
  have hc₀ : 0 ≤ (t + c₀) ^ c₀ := pow_nonneg (by positivity) _
  have htCost : t ≤ cost := by linarith
  have hmodelCost : (t + b₀) ^ b₀ ≤ cost := by linarith
  have hfreezeCost : (t + c₀) ^ c₀ ≤ cost := by linarith
  have hcost : 0 ≤ cost := ht.trans htCost
  obtain ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hrec⟩ :=
    hmodels D a w hF W v₀ hspan ht (hι.trans hpt) (fun i => (hD i).mono (D i) hpt)
      (hκ.trans hpt) (fun i b => (hv i b).trans hpt) m hm
      (hmb.trans (Real.exp_le_exp.mpr hat))
  have hbase := hexpand D a W E Q (hp.trans hpt) hcost hQF
    (LowerRefilteredRecoveryFamily.mono_cost D a W E Q hrec hmodelCost)
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr (hat.trans htCost)), E, hEF, hEL,
    hE.mono E hmodelCost, n, hn, Q, hQF, hQL, hQ.mono Q hmodelCost,
    htarget.mono _ hmodelCost, ?_⟩
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQ'F, hQ'b, hQ'le, hQ', Z, hZF, hZb, hZle, hZ, hbase⟩ := hbase
  refine ⟨Q', hQ'F, hQ'b, hQ'le, hQ', Z, hZF, hZb, hZle, hZ, ?_⟩
  let := Z.metricSpace
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A₁ B₁ label ρ η hρ hη hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant slow middle rat κ₁ g hκ₁ hfactor hslow hrat hmiddle hdiam
  obtain ⟨anchor, hanchor, hnear⟩ := exists_cyclic_cell_anchors N A₁ hρ hcircle
  choose right left hright hvalue using fun h => hperiod (rat h) (hrat h)
  let r₀ := fun i h => right h (fun _ => label i)
  have hrightGrid (i : I) (h : ZMod N) :
      ((D a).basis.baseChange ℝ).equivFun (r₀ i h).coord ∈ realDenominatorGrid m :=
    (hright h _).2.1
  have hclass (i : I) (h x : ZMod N) (_hx : x ∉ cyclicWrapExceptional h ρ) (hAx : 0 < A₁ i x) :
      (QuotientGroup.mk ((D a).filtration.adaptedPolynomialRealValueHom w₁
        (fun _ => (x.val : ℝ)) (rat h)) : (D a).Space) = QuotientGroup.mk (r₀ i h) := by
    obtain ⟨γ, hγ, heq⟩ := (hvalue h (fun _ => (x.val : ℤ))).1
    have hclass' :
        (QuotientGroup.mk ((D a).filtration.adaptedPolynomialRealValueHom w₁
          (fun _ => ((x.val : ℤ) : ℝ)) (rat h)) : (D a).Space) =
          QuotientGroup.mk (right h (fun _ => ((x.val : ℤ) : ZMod P))) := by
      rw [heq]
      exact QuotientGroup.mk_mul_of_mem _ hγ
    simpa only [Int.cast_natCast, r₀, hres i x hAx] using hclass'
  have hpower {j : ℕ} (hj : j ≤ k) : (p + 2) ^ j ≤ (t + 2) ^ k :=
    (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2)
      (by linarith : p + 2 ≤ t + 2) j).trans
        (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t + 2) hj)
  have hslow' (h : ZMod N) : (D a).filtration.PolynomialSlowBound (D a).basis w₁
      (fun _ => (N : ℝ)) (Real.exp ((t + 2) ^ k)) (slow h) :=
    (D a).filtration.polynomialSlowBound_mono (D a).basis w₁
      (fun _ => (N : ℝ)) (fun _ => Nat.cast_pos.mpr (NeZero.pos N))
      (Real.exp_le_exp.mpr (hpower (le_max_left _ _))) (slow h) (hslow h)
  have hleft (i : I) (h : ZMod N) (b : Fin (d a)) :
      |((D a).basis.baseChange ℝ).repr
        ((D a).filtration.adaptedPolynomialRealValueHom w₁ (fun _ => anchor i h) (slow h)).coord b| ≤
          Real.exp ((t + 2) ^ k) := by
    have hinv := ((D a).filtration.polynomialSlowBound_inv_iff (D a).basis w₁
      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)).mpr (hslow h)
    have hval := (hslowValues (D a) w₁ (fun _ => by decide) p hp₀ (hD a)
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp)
      (fun _ => (N : ℝ)) (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (slow h)⁻¹ hinv).1
        (fun _ => anchor i h) (fun _ => hanchor i h) b
    have hval' :
        |((D a).basis.baseChange ℝ).repr
          ((D a).filtration.adaptedPolynomialRealValueHom w₁ (fun _ => anchor i h) (slow h)).coord b| ≤
            Real.exp ((p + 2) ^ k₀) := by
      simpa only [map_inv, inv_inv] using hval
    exact hval'.trans (Real.exp_le_exp.mpr (hpower (le_max_right _ _)))
  obtain ⟨U, hU, hUcomplexity, hUempty, err, herr, hmean⟩ :=
    hbase freq hfreq N A₁ B₁ hρ hη hA hB hAsum hBsum S
      (fun h => (hS h).mono hpt) hpositive hinvariant slow middle rat κ₁ g
      hκ₁ hfactor hslow' hmiddle anchor r₀ hanchor hleft hrightGrid hnear hclass hdiam
  refine ⟨U, hU, hUcomplexity, hUempty, err, herr, ?_⟩
  intro h
  calc
    _ ≤ Real.exp ((t + c₀) ^ c₀) * ρ + Real.exp cost * η + 6 * ρ + 3 / N := hmean h
    _ ≤ Real.exp cost * (ρ + η) + 6 * ρ + 3 / N := by
      have hb := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hfreezeCost) hρ.le
      nlinarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
