/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.ReturnShapeWidthBudget
import OAI.Combinatorics.Progressions.Dynamics.SmallRatioPotential
import OAI.Combinatorics.Progressions.Estimates.SelectedChildBound
import OAI.Combinatorics.Progressions.Nilpotent.MatchedFlatNiltest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixed_center_contraction {ι : Type*} (Z : Finset ι)
    (small : ι → Prop) [DecidablePred small] (P C : ι → ℝ) {Phi rho : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hsmall : (𝔼 z ∈ Z, if small z then P z else 0) ≤ Phi / 2)
    (htotal : (𝔼 z ∈ Z, P z) ≤ Phi)
    (hCsmall : ∀ z ∈ Z, small z → C z ≤ P z)
    (hClarge : ∀ z ∈ Z, ¬ small z → C z ≤ rho * P z) :
    (𝔼 z ∈ Z, C z) ≤ ((1 + rho) / 2) * Phi := by
  let A := 𝔼 z ∈ Z, if small z then P z else 0
  let B := 𝔼 z ∈ Z, if small z then 0 else P z
  have hsplit : A + B = 𝔼 z ∈ Z, P z := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro z _
    split_ifs <;> simp
  have hbound : (𝔼 z ∈ Z, C z) ≤ A + rho * B := by
    calc
      _ ≤ 𝔼 z ∈ Z, ((if small z then P z else 0) + rho * (if small z then 0 else P z)) := by
        apply Finset.expect_le_expect
        intro z hz
        by_cases hs : small z
        · simpa only [ite_eq_left hs, mul_zero, add_zero] using hCsmall z hz hs
        · simpa only [ite_eq_right hs, zero_add] using hClarge z hz hs
      _ = _ := by rw [Finset.expect_add_distrib, ← Finset.mul_expect]
  exact hbound.trans (combine_matched_potential_contractions hrho hrho1 hsmall
    (by simpa only [hsplit] using htotal))

theorem parent_center_potential_contraction
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B L : Finset G) (hB : B.Nonempty) (hL : L.Nonempty)
    (f g : G → ℝ) (Q : G → G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0)
    {c₀ K rho : ℝ} (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hcapf : ∀ x, cellAverage L f x ≤ K * (𝔼 r ∈ B, f r))
    (hcapg : ∀ y, cellAverage L g y ≤ K * (𝔼 r ∈ B, g r))
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hsmall : ∀ x ∈ B, ∀ y ∈ B,
      cellAverage L f x < c₀ * (𝔼 r ∈ B, f r) ∨ cellAverage L g y < c₀ * (𝔼 r ∈ B, g r) →
      Q x y ≤ (cellAverage L f x * cellAverage L g y) ^ (1 / 4 : ℝ))
    (hlarge : ∀ x ∈ B, ∀ y ∈ B,
      ¬ (cellAverage L f x < c₀ * (𝔼 r ∈ B, f r) ∨ cellAverage L g y < c₀ * (𝔼 r ∈ B, g r)) →
      Q x y ≤ rho * (cellAverage L f x * cellAverage L g y) ^ (1 / 4 : ℝ)) :
    (𝔼 x ∈ B, 𝔼 y ∈ B, Q x y) ≤
      ((1 + rho) / 2) * ((𝔼 r ∈ B, f r) * (𝔼 r ∈ B, g r)) ^ (1 / 4 : ℝ) := by
  classical
  have hu : 0 ≤ 𝔼 r ∈ B, f r := Finset.expect_nonneg (fun r _ => hf r)
  have hv : 0 ≤ 𝔼 r ∈ B, g r := Finset.expect_nonneg (fun r _ => hg r)
  have hsmallMean := expect_smallRatioCenterPotential_le B L hB f g hf hg hu hv hc₀ hK
    hcapf hcapg hfactor
  have htotal := parent_cell_potential_le B L hB hL f g hf hg hfsupport hgsupport
  have h := mixed_center_contraction (B ×ˢ B)
    (fun z => cellAverage L f z.1 < c₀ * (𝔼 r ∈ B, f r) ∨
      cellAverage L g z.2 < c₀ * (𝔼 r ∈ B, g r))
    (fun z => (cellAverage L f z.1 * cellAverage L g z.2) ^ (1 / 4 : ℝ))
    (fun z => Q z.1 z.2) hrho hrho1
    (by simpa only [Finset.expect_product, smallRatioCenterPotential] using hsmallMean)
    (by simpa only [Finset.expect_product] using htotal)
    (fun z hz hs => hsmall z.1 (Finset.mem_product.mp hz).1 z.2 (Finset.mem_product.mp hz).2 hs)
    (fun z hz hs => hlarge z.1 (Finset.mem_product.mp hz).1 z.2 (Finset.mem_product.mp hz).2 hs)
  simpa only [Finset.expect_product] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem center_refinement_integral_bound {ι : Type*} (Z : Finset ι) (hZ : Z.Nonempty)
    (active : ι → Prop) [DecidablePred active] (I J P : ι → ℝ)
    {epsilon eta Phi : ℝ} (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hP : ∀ z ∈ Z, 0 ≤ P z) (hmean : (𝔼 z ∈ Z, P z) ≤ Phi)
    (hterminal : ∀ z ∈ Z, ¬ active z → I z ≤ epsilon * P z)
    (hsurviving : ∀ z ∈ Z, active z → |J z - I z| ≤ eta) :
    (𝔼 z ∈ Z, I z) ≤ (𝔼 z ∈ Z, if active z then J z else 0) + epsilon * Phi + eta := by
  have hpoint : ∀ z ∈ Z, I z ≤ (if active z then J z else 0) + epsilon * P z + eta := by
    intro z hz
    by_cases ha : active z
    · rw [ite_eq_left ha]
      have h := (abs_le.mp (hsurviving z hz ha)).1
      have hn := mul_nonneg hepsilon (hP z hz)
      linarith
    · rw [ite_eq_right ha, zero_add]
      exact (hterminal z hz ha).trans (le_add_of_nonneg_right heta)
  calc
    _ ≤ 𝔼 z ∈ Z, ((if active z then J z else 0) + epsilon * P z + eta) :=
      Finset.expect_le_expect hpoint
    _ = (𝔼 z ∈ Z, if active z then J z else 0) + epsilon * (𝔼 z ∈ Z, P z) + eta := by
      rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
        Finset.expect_const hZ]
    _ ≤ _ := by gcongr

theorem parent_and_centers_integral_bound {ι : Type*} (Z : Finset ι) (hZ : Z.Nonempty)
    (active : ι → Prop) [DecidablePred active] (I J P : ι → ℝ)
    {parent epsilon eta matchingError Phi : ℝ}
    (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hP : ∀ z ∈ Z, 0 ≤ P z) (hmean : (𝔼 z ∈ Z, P z) ≤ Phi)
    (hterminal : ∀ z ∈ Z, ¬ active z → I z ≤ epsilon * P z)
    (hsurviving : ∀ z ∈ Z, active z → |J z - I z| ≤ eta)
    (hmatching : |parent - (𝔼 z ∈ Z, I z)| ≤ matchingError) :
    parent ≤ (𝔼 z ∈ Z, if active z then J z else 0) + epsilon * Phi + eta + matchingError := by
  have hcenters := center_refinement_integral_bound Z hZ active I J P hepsilon heta hP hmean
    hterminal hsurviving
  have h := (abs_le.mp hmatching).2
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_center_refinement {ι κ : Type*}
    (Z : Finset ι) (hZ : Z.Nonempty) (small : ι → Prop) [DecidablePred small]
    (Allowed : κ → Prop) (defaultShape : κ) (hdefault : Allowed defaultShape)
    (I P : ι → ℝ) (childIntegral childPotential : ι → κ → ℝ)
    {epsilon eta Phi rho : ℝ} (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hP : ∀ z ∈ Z, 0 ≤ P z) (hmean : (𝔼 z ∈ Z, P z) ≤ Phi)
    (hsmallMean : (𝔼 z ∈ Z, if small z then P z else 0) ≤ Phi / 2)
    (hsmall : ∀ z ∈ Z, small z →
      |childIntegral z defaultShape - I z| ≤ eta ∧ childPotential z defaultShape ≤ P z)
    (hlarge : ∀ z ∈ Z, ¬ small z →
      I z ≤ epsilon * P z ∨ ∃ c, Allowed c ∧
        |childIntegral z c - I z| ≤ eta ∧ childPotential z c ≤ rho * P z) :
    ∃ shape : ι → κ, ∃ active : ι → Bool,
      (∀ z ∈ Z, Allowed (shape z)) ∧
      (∀ z ∈ Z, ¬ active z = true → I z ≤ epsilon * P z) ∧
      (∀ z ∈ Z, active z = true → |childIntegral z (shape z) - I z| ≤ eta) ∧
      (𝔼 z ∈ Z, if active z = true then childPotential z (shape z) else 0) ≤
        ((1 + rho) / 2) * Phi ∧
      (𝔼 z ∈ Z, I z) ≤
        (𝔼 z ∈ Z, if active z = true then childIntegral z (shape z) else 0) + epsilon * Phi + eta := by
  classical
  let Good (z : ι) (d : Bool × κ) : Prop :=
    Allowed d.2 ∧
      (d.1 = true → |childIntegral z d.2 - I z| ≤ eta) ∧
      (¬ d.1 = true → I z ≤ epsilon * P z) ∧
      (small z → (if d.1 = true then childPotential z d.2 else 0) ≤ P z) ∧
      (¬ small z → (if d.1 = true then childPotential z d.2 else 0) ≤ rho * P z)
  have hexists : ∀ z ∈ Z, ∃ d : Bool × κ, Good z d := by
    intro z hz
    by_cases hs : small z
    · obtain ⟨herr, hpot⟩ := hsmall z hz hs
      refine ⟨(true, defaultShape), hdefault, ?_, ?_, ?_, ?_⟩
      · intro _; exact herr
      · simp
      · intro _; simpa only [ite_true] using hpot
      · intro hn; exact False.elim (hn hs)
    · rcases hlarge z hz hs with hflat | ⟨c, hc, herr, hpot⟩
      · refine ⟨(false, defaultShape), hdefault, ?_, ?_, ?_, ?_⟩
        · simp
        · intro _; exact hflat
        · intro ht; exact False.elim (hs ht)
        · intro _
          simpa only [Bool.false_eq_true, ite_false] using mul_nonneg hrho (hP z hz)
      · refine ⟨(true, c), hc, ?_, ?_, ?_, ?_⟩
        · intro _; exact herr
        · simp
        · intro ht; exact False.elim (hs ht)
        · intro _; simpa only [ite_true] using hpot
  let selected (z : ι) : Bool × κ :=
    if hz : z ∈ Z then Classical.choose (hexists z hz) else (false, defaultShape)
  have hselected (z : ι) (hz : z ∈ Z) : Good z (selected z) := by
    dsimp only [selected]
    rw [dite_eq_left hz]
    exact Classical.choose_spec (hexists z hz)
  let shape := fun z => (selected z).2
  let active := fun z => (selected z).1
  refine ⟨shape, active, (fun z hz => (hselected z hz).1),
    (fun z hz => (hselected z hz).2.2.1), (fun z hz => (hselected z hz).2.1), ?_, ?_⟩
  · exact mixed_center_contraction Z small P
      (fun z => if active z = true then childPotential z (shape z) else 0)
      hrho hrho1 hsmallMean hmean
      (fun z hz => (hselected z hz).2.2.2.1)
      (fun z hz => (hselected z hz).2.2.2.2)
  · exact center_refinement_integral_bound Z hZ (fun z => active z = true) I
      (fun z => childIntegral z (shape z)) P hepsilon heta hP hmean
      (fun z hz => (hselected z hz).2.2.1)
      (fun z hz => (hselected z hz).2.1)

end Erdos3

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_admissible_independent_return_shape
    (B L S : CyclicBohr.Set N) (hL : L.IsRankRegular) (hS : S.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hfreq : S.frequencies = L.frequencies) (hwidth : S.radius ≤ L.radius)
    {scale : ℝ≥0} {extra : ℕ} {minimumWidth c p H W Q E : ℝ}
    (hSB : S.carrier ⊆ (B.ndilate scale).carrier) (hrank : S.rank ≤ B.rank + extra)
    (hminimum : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q E))
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B scale extra minimumWidth C ∧
      C.frequencies = S.frequencies ∧ 0 < C.radius ∧ C.radius ≤ 1 ∧
      C.carrier ⊆ (S.ndilate (independentReturnScale S.rank W (Real.exp (-E)))).carrier ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
            bilinearIntegral (C.carrier.image (fun t => z.1 + t))
              (C.carrier.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
          matchedIntegral L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  let zeta := independentReturnScale S.rank W (Real.exp (-E))
  obtain ⟨hzeta, hzeta1, _, _⟩ := independentReturnScale_spec S.rank hW (Real.exp_pos (-E))
  obtain ⟨C, hCfreq, hCreg, hClo, hChi, hCS, _⟩ :=
    S.exists_controlled_regular_subdilate hSpos zeta hzeta hzeta1
  have hzetaR : (0 : ℝ) < zeta := by exact_mod_cast hzeta
  have hzeta1R : (zeta : ℝ) ≤ 1 := by exact_mod_cast hzeta1
  have hCpos : 0 < C.radius := (show 0 < (zeta : ℝ) * S.radius / 2 by positivity).trans_le hClo
  have hCwidth : C.radius ≤ 1 := hChi.trans (by nlinarith [S.radius_nonneg])
  have hCSbase : C.carrier ⊆ S.carrier := by
    have h := hCS.trans (CyclicBohr.Set.carrier_ndilate_mono (B := S) hzeta1)
    simpa only [CyclicBohr.Set.ndilate_one] using h
  have hCrank : C.rank = S.rank := congrArg Finset.card hCfreq
  have hCminimum : minimumWidth ≤ C.radius :=
    hminimum.trans ((unbalanced_return_width_le_regular_return S hc hc1 hp hH hW hWcap hQ hE).trans hClo)
  refine ⟨C, ⟨hCreg, hCSbase.trans hSB, by simpa only [hCrank] using hrank, hCminimum⟩,
    hCfreq, hCpos, hCwidth, hCS, ?_⟩
  intro a f g ha hf hg
  exact bohr_matched_independent_at_return_scale L S hL hS hfreq hwidth C.carrier
    C.carrier_nonempty a f g hW (Real.exp_pos (-E)) hCS ha hf hg

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem exists_refinement_moment_orders {D : ℝ} (hD : 0 ≤ D) :
    ∃ C H : ℝ, 1 ≤ C ∧ 0 ≤ H ∧ ∀ p : ℝ, 1 ≤ p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * p ∧
        (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2 ∧
        ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
          ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
          (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m') := by
  exact exists_joint_moment_orders (by norm_num) (by norm_num) (by linarith)
    (localMomentGain_pos δ) (localMomentExponentFactor δ) (localMomentExponentFactor_pos δ)

theorem matched_refinement_alternatives
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedWidthLoss S.rank γ p H))
    (A B F G f g : ZMod N → ℝ) (x y : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hdomf : ∀ r, f r ≤ F (x + r)) (hdomg : ∀ r, g r ≤ G (y + r))
    (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r)
    (hfsupport : ∀ r, r ∉ L.carrier → f r = 0)
    (hgsupport : ∀ r, r ∉ L.carrier → g r = 0)
    {U V u v M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlowerf : c₀ * U ≤ u) (hlowerg : c₀ * V ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
    (hmeanf : (𝔼 r ∈ L.carrier, f r) = u) (hmeang : (𝔼 r ∈ L.carrier, g r) = v)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hcapf : ∀ r, f r / u ≤ M) (hcapg : ∀ r, g r / v ≤ M)
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m')) :
    matchedIntegral L.carrier S.carrier
        (fun r => A (x + y + r) - (1 + epsilon) * B (x + y + r)) f g ≤
      Real.exp (-(D * p)) * (u * v) ^ (1 / 4 : ℝ) ∨
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B₀ scale extra minimumWidth C ∧
      Peeling.admissibleBohrShape S 1 (unbalancedRankExtra γ p H)
        (S.radius * Real.exp (-unbalancedWidthLoss S.rank γ p H)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ) := by
  have hu : 0 < u := (mul_pos hc₀ hU).trans_le hlowerf
  have hv : 0 < v := (mul_pos hc₀ hV).trans_le hlowerg
  have hdelta := (flatComparisonDelta_spec hepsilon).1
  rcases normalized_local_alternatives_at_scale L hL S.carrier S.carrier_nonempty f g hf hg
      hfsupport hgsupport hu hv hM.le hdelta hmeanf hmeang hcapf hcapg hSLmoment m hm with
    hflat | ⟨h, hchoice, m', hm', hmm', hm'upper, hlarge⟩
  · left
    exact matched_flat_integral_of_niltest_comparison L.carrier S hSreg hSwidth A B f g (x + y)
      hu hv hu1 hv1 hepsilon hp (by norm_num) hD hR hM.le
      (by simpa only [one_mul] using hMcap) hSlog (by omega) horder hA hB hf hg hcapg
      hfsupport hmeanf hflat hcomplexity hprecision hcompare
  · right
    obtain ⟨hqp, hsep⟩ := horders m' hmm' hm'upper
    exact exists_parent_unbalanced_contraction B₀ L S hL hSpos hSwidth hSreg hSrank
      hSL hkappa hSB hrank hwidth F G f g x y hdomf hdomg hf hg hfsupport hgsupport
      hU hV hc₀ hK hlowerf hlowerg hmeanf.le hmeang.le hparentF hparentG hM
      (localMomentGain_pos δ) ((localMomentGain_le_half δ).trans (by norm_num)) hp hH
      hMcap hcapf hcapg herror (2 * m') (by omega) ⟨m', by omega⟩ hqp h hchoice hlarge hsep

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem matched_independent_refinement_alternatives
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (A B F G f g : ZMod N → ℝ) (x y : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hdomf : ∀ r, f r ≤ F (x + r)) (hdomg : ∀ r, g r ≤ G (y + r))
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (hfsupport : ∀ r, r ∉ L.carrier → f r = 0)
    (hgsupport : ∀ r, r ∉ L.carrier → g r = 0)
    {U V u v M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlowerf : c₀ * U ≤ u) (hlowerg : c₀ * V ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
    (hmeanf : (𝔼 r ∈ L.carrier, f r) = u) (hmeang : (𝔼 r ∈ L.carrier, g r) = v)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hcapf : ∀ r, f r / u ≤ M) (hcapg : ∀ r, g r / v ≤ M)
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m')) :
    matchedIntegral L.carrier S.carrier
        (fun r => A (x + y + r) - (1 + epsilon) * B (x + y + r)) f g ≤
      Real.exp (-(D * p)) * (u * v) ^ (1 / 4 : ℝ) ∨
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B₀ scale extra minimumWidth C ∧
      Peeling.admissibleBohrShape S (independentReturnScale S.rank W (Real.exp (-E)))
        (unbalancedRankExtra γ p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      (let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ)) ∧
      ∀ a : ZMod N → ℝ, (∀ r, |a r| ≤ W) →
        |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
            bilinearIntegral (C.carrier.image (fun t => z.1 + t))
              (C.carrier.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
          matchedIntegral L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  have hu : 0 < u := (mul_pos hc₀ hU).trans_le hlowerf
  have hv : 0 < v := (mul_pos hc₀ hV).trans_le hlowerg
  have hdelta := (flatComparisonDelta_spec hepsilon).1
  have hf0 : ∀ r, 0 ≤ f r := fun r => (hf r).1
  have hg0 : ∀ r, 0 ≤ g r := fun r => (hg r).1
  rcases normalized_local_alternatives_at_scale L hL S.carrier S.carrier_nonempty f g hf0 hg0
      hfsupport hgsupport hu hv hM.le hdelta hmeanf hmeang hcapf hcapg hSLmoment m hm with
    hflat | ⟨h, hchoice, m', hm', hmm', hm'upper, hlarge⟩
  · left
    exact matched_flat_integral_of_niltest_comparison L.carrier S hSreg hSwidth A B f g (x + y)
      hu hv hu1 hv1 hepsilon hp (by norm_num) hD hR hM.le
      (by simpa only [one_mul] using hMcap) hSlog (by omega) horder hA hB hf0 hg0 hcapg
      hfsupport hmeanf hflat hcomplexity hprecision hcompare
  · right
    obtain ⟨hqp, hsep⟩ := horders m' hmm' hm'upper
    exact exists_parent_unbalanced_independent_refinement B₀ L S hL hSpos hSwidth hSreg hSrank
      hfreq hlocalWidth
      hSL hkappa hSB hrank hwidth F G f g x y hdomf hdomg hf hg hfsupport hgsupport
      hU hV hc₀ hK hlowerf hlowerg hmeanf.le hmeang.le hparentF hparentG hM
      (localMomentGain_pos δ) ((localMomentGain_le_half δ).trans (by norm_num)) hp hH
      hMcap hcapf hcapg herror (2 * m') (by omega) ⟨m', by omega⟩ hqp h hchoice hlarge hsep hW hWcap hQ hE

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

theorem unbalanced_factor_bounds {c M : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    3 / 4 ≤ 1 - c / (128 * (1 + Real.sqrt M) ^ 2) ∧
      1 - c / (128 * (1 + Real.sqrt M) ^ 2) < 1 := by
  have h := quarter_contraction_factor_bounds (M := M)
    (show 0 < c / 32 by positivity) (show c / 32 ≤ 1 by linarith)
  have heq : c / 32 / (4 * (1 + Real.sqrt M) ^ 2) = c / (128 * (1 + Real.sqrt M) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  simpa only [heq] using h

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem capped_center_alternatives
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (A B F G : ZMod N → ℝ) (origin x y : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    {U V M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlowerF : c₀ * U ≤ cellAverage L.carrier F x)
    (hlowerG : c₀ * V ≤ cellAverage L.carrier G y)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMU : 1 ≤ M * (c₀ * U)) (hMV : 1 ≤ M * (c₀ * V))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m')) :
    let a := fun r => A (origin + r) - (1 + epsilon) * B (origin + r)
    centerMatchedIntegral L.carrier S.carrier a F G (x, y) ≤
      Real.exp (-(D * p)) * centerPotential L.carrier F G (x, y) ∨
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B₀ scale extra minimumWidth C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      |centerChildIntegral L.carrier S.carrier a F G (x, y) C.carrier -
        centerMatchedIntegral L.carrier S.carrier a F G (x, y)| ≤ Real.exp (-E) ∧
      centerChildPotential L.carrier S.carrier F G (x, y) C.carrier ≤
        (1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)) * centerPotential L.carrier F G (x, y) := by
  intro a
  have hF0 : ∀ r, 0 ≤ F r := fun r => (hF r).1
  have hG0 : ∀ r, 0 ≤ G r := fun r => (hG r).1
  have hu : 0 < cellAverage L.carrier F x := (mul_pos hc₀ hU).trans_le hlowerF
  have hv : 0 < cellAverage L.carrier G y := (mul_pos hc₀ hV).trans_le hlowerG
  have hf := centerSlice_bounds L.carrier F hF x
  have hg := centerSlice_bounds L.carrier G hG y
  have hfs := centerSlice_supported L.carrier F x
  have hgs := centerSlice_supported L.carrier G y
  have hmf := centerSlice_mean L.carrier F x
  have hmg := centerSlice_mean L.carrier G y
  have hcf := centerSlice_normalized_cap L.carrier F hF x hU hc₀ hM.le hMU hlowerF
  have hcg := centerSlice_normalized_cap L.carrier G hG y hV hc₀ hM.le hMV hlowerG
  rcases normalized_local_alternatives_at_scale L hL S.carrier S.carrier_nonempty
      (centerSlice L.carrier F x) (centerSlice L.carrier G y)
      (fun r => (hf r).1) (fun r => (hg r).1) hfs hgs hu hv hM.le
      (flatComparisonDelta_spec hepsilon).1 hmf hmg hcf hcg hSLmoment m hm with
    hflat | ⟨h, hchoice, m', hm', hmm', hm'upper, hlarge⟩
  · left
    have hflatI := matched_flat_integral_of_niltest_comparison L.carrier S hSreg hSwidth
      A B (centerSlice L.carrier F x) (centerSlice L.carrier G y) (origin + (x + y))
      hu hv (cellAverage_le L.carrier_nonempty F (fun r => (hF r).2) x)
      (cellAverage_le L.carrier_nonempty G (fun r => (hG r).2) y)
      hepsilon hp (by norm_num) hD hR hM.le
      (by simpa only [one_mul] using hMcap) hSlog (by omega) horder hA hB
      (fun r => (hf r).1) (fun r => (hg r).1) hcg hfs hmf hflat hcomplexity hprecision hcompare
    simpa only [centerMatchedIntegral, centerPotential, a, add_assoc] using hflatI
  · right
    obtain ⟨hqp, hsep⟩ := horders m' hmm' hm'upper
    obtain ⟨C, hparent, _, hCpos, hCwidth, hcontract, hintegral⟩ :=
      exists_parent_unbalanced_independent_refinement B₀ L S hL hSpos hSwidth hSreg hSrank
        hfreq hlocalWidth hSL hkappa hSB hrank hwidth
        F G (centerSlice L.carrier F x) (centerSlice L.carrier G y) x y
        (translated_slice_le L.carrier F hF0 x) (translated_slice_le L.carrier G hG0 y)
        hf hg hfs hgs hU hV hc₀ hK hlowerF hlowerG hmf.le hmg.le hparentF hparentG
        hM (localMomentGain_pos δ) ((localMomentGain_le_half δ).trans (by norm_num)) hp hH
        hMcap hcf hcg herror (2 * m') (by omega) ⟨m', by omega⟩ hqp h hchoice hlarge hsep
        hW hWcap hQ hE
    obtain ⟨_, _, hpotential⟩ := hcontract
    exact ⟨C, hparent, hCpos, hCwidth,
      hintegral (fun r => a (x + y + r)) (fun r => ha (origin + (x + y + r))), hpotential⟩

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem exists_capped_parent_refinement
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B F G : ZMod N → ℝ) (origin : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hFsupport : ∀ r, r ∉ B₀.carrier → F r = 0)
    (hGsupport : ∀ r, r ∉ B₀.carrier → G r = 0)
    {U V M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hmeanF : (𝔼 r ∈ B₀.carrier, F r) = U) (hmeanG : (𝔼 r ∈ B₀.carrier, G r) = V)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMU : 1 ≤ M * (c₀ * U)) (hMV : 1 ≤ M * (c₀ * V))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : |bilinearIntegral B₀.carrier B₀.carrier (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G -
      parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m')) :
    let a := fun r => A (origin + r) - (1 + epsilon) * B (origin + r)
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    ∃ shape : ZMod N × ZMod N → CyclicBohr.Set N,
      ∃ active : ZMod N × ZMod N → Bool,
      (∀ z ∈ B₀.carrier ×ˢ B₀.carrier,
        Peeling.admissibleBohrShape B₀ scale extra minimumWidth (shape z) ∧
          0 < (shape z).radius ∧ (shape z).radius ≤ 1) ∧
      (∀ z ∈ B₀.carrier ×ˢ B₀.carrier, ¬ active z = true →
        centerMatchedIntegral L.carrier S.carrier a F G z ≤
          Real.exp (-(D * p)) * centerPotential L.carrier F G z) ∧
      (∀ z ∈ B₀.carrier ×ˢ B₀.carrier, active z = true →
        |centerChildIntegral L.carrier S.carrier a F G z (shape z).carrier -
          centerMatchedIntegral L.carrier S.carrier a F G z| ≤ Real.exp (-E)) ∧
      (𝔼 z ∈ B₀.carrier ×ˢ B₀.carrier,
        if active z = true then centerChildPotential L.carrier S.carrier F G z (shape z).carrier else 0) ≤
          ((1 + rho) / 2) * (U * V) ^ (1 / 4 : ℝ) ∧
      bilinearIntegral B₀.carrier B₀.carrier a F G ≤
        (𝔼 z ∈ B₀.carrier ×ˢ B₀.carrier,
          if active z = true then centerChildIntegral L.carrier S.carrier a F G z (shape z).carrier else 0) +
          Real.exp (-(D * p)) * (U * V) ^ (1 / 4 : ℝ) + Real.exp (-E) + matchingError := by
  classical
  intro a rho
  let small := fun z : ZMod N × ZMod N =>
    cellAverage L.carrier F z.1 < c₀ * U ∨ cellAverage L.carrier G z.2 < c₀ * V
  let Allowed := fun C : CyclicBohr.Set N =>
    Peeling.admissibleBohrShape B₀ scale extra minimumWidth C ∧ 0 < C.radius ∧ C.radius ≤ 1
  have hF0 : ∀ r, 0 ≤ F r := fun r => (hF r).1
  have hG0 : ∀ r, 0 ≤ G r := fun r => (hG r).1
  have hgamma : 0 < γ := localMomentGain_pos δ
  have hgamma1 : γ ≤ 1 := (localMomentGain_le_half δ).trans (by norm_num)
  obtain ⟨hrho, hrho1⟩ := unbalanced_factor_bounds (M := K / c₀) hgamma hgamma1
  have hmean : (𝔼 z ∈ B₀.carrier ×ˢ B₀.carrier, centerPotential L.carrier F G z) ≤
      (U * V) ^ (1 / 4 : ℝ) := by
    have h := centerPotential_mean_le B₀.carrier L.carrier B₀.carrier_nonempty L.carrier_nonempty
      F G hF0 hG0 hFsupport hGsupport
    simpa only [hmeanF, hmeanG] using h
  have hsmallMean :
      (𝔼 z ∈ B₀.carrier ×ˢ B₀.carrier, if small z then centerPotential L.carrier F G z else 0) ≤
        (U * V) ^ (1 / 4 : ℝ) / 2 := by
    have h := expect_smallRatioCenterPotential_le B₀.carrier L.carrier B₀.carrier_nonempty
      F G hF0 hG0 hU.le hV.le hc₀.le hK (hparentF L hLshape) (hparentG L hLshape) hfactor
    simpa only [Finset.expect_product, small, centerPotential, smallRatioCenterPotential] using h
  obtain ⟨C₀, hC₀shape, _, hC₀pos, hC₀width, _, hC₀error⟩ :=
    exists_admissible_independent_return_shape (extra := extra) B₀ L S hL hSreg hSpos hSwidth hfreq hlocalWidth
      hSB (by omega) hwidth hgamma hgamma1 (by linarith) hH hW hWcap hQ hE
  have hdefault : Allowed C₀ := ⟨hC₀shape, hC₀pos, hC₀width⟩
  have hsmallCase : ∀ z ∈ B₀.carrier ×ˢ B₀.carrier, small z →
      |centerChildIntegral L.carrier S.carrier a F G z C₀.carrier -
        centerMatchedIntegral L.carrier S.carrier a F G z| ≤ Real.exp (-E) ∧
      centerChildPotential L.carrier S.carrier F G z C₀.carrier ≤ centerPotential L.carrier F G z := by
    intro z _ _
    refine ⟨?_, centerChildPotential_le L.carrier S.carrier C₀.carrier
      L.carrier_nonempty S.carrier_nonempty C₀.carrier_nonempty F G hF hG z⟩
    exact hC₀error (fun r => a (z.1 + z.2 + r))
      (centerSlice L.carrier F z.1) (centerSlice L.carrier G z.2)
      (fun r => ha (origin + (z.1 + z.2 + r))) (centerSlice_bounds L.carrier F hF z.1)
      (centerSlice_bounds L.carrier G hG z.2)
  have hlargeCase : ∀ z ∈ B₀.carrier ×ˢ B₀.carrier, ¬ small z →
      centerMatchedIntegral L.carrier S.carrier a F G z ≤
        Real.exp (-(D * p)) * centerPotential L.carrier F G z ∨
      ∃ C, Allowed C ∧
        |centerChildIntegral L.carrier S.carrier a F G z C.carrier -
          centerMatchedIntegral L.carrier S.carrier a F G z| ≤ Real.exp (-E) ∧
        centerChildPotential L.carrier S.carrier F G z C.carrier ≤ rho * centerPotential L.carrier F G z := by
    intro z _ hz
    have hlowerF : c₀ * U ≤ cellAverage L.carrier F z.1 := le_of_not_gt (not_or.mp hz).1
    have hlowerG : c₀ * V ≤ cellAverage L.carrier G z.2 := le_of_not_gt (not_or.mp hz).2
    have h := capped_center_alternatives B₀ L S hL hSpos hSwidth hSreg hSrank hfreq hlocalWidth
      hepsilon hp hD hR hH hSL hkappa hSB hrank hwidth A B F G origin z.1 z.2 hA hB hF hG
      hU hV hc₀ hK hlowerF hlowerG hparentF hparentG hM hMcap hMU hMV hSLmoment herror
      hSlog hcomplexity hprecision hcompare hW hWcap hQ hE ha m hm horder horders
    rcases h with hflat | ⟨C, hC, hCpos, hCwidth, herr, hpot⟩
    · exact Or.inl hflat
    · exact Or.inr ⟨C, ⟨hC, hCpos, hCwidth⟩, herr, hpot⟩
  obtain ⟨shape, active, hallowed, hterminal, hactive, hpotential, hintegral⟩ :=
    exists_center_refinement (B₀.carrier ×ˢ B₀.carrier) (B₀.carrier_nonempty.product B₀.carrier_nonempty)
      small Allowed C₀ hdefault (centerMatchedIntegral L.carrier S.carrier a F G)
      (centerPotential L.carrier F G)
      (fun z C => centerChildIntegral L.carrier S.carrier a F G z C.carrier)
      (fun z C => centerChildPotential L.carrier S.carrier F G z C.carrier)
      (Real.exp_nonneg _) (Real.exp_nonneg _) (by linarith) hrho1.le
      (fun z _ => centerPotential_nonneg L.carrier F G hF0 hG0 z) hmean hsmallMean hsmallCase hlargeCase
  refine ⟨shape, active, hallowed, hterminal, hactive, hpotential, ?_⟩
  rw [centerMatchedIntegral_mean] at hintegral
  have hmatch := (abs_le.mp hmatching).2
  linarith only [hmatch, hintegral]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem capped_parent_bound_of_children
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B F G : ZMod N → ℝ) (origin : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hFsupport : ∀ r, r ∉ B₀.carrier → F r = 0)
    (hGsupport : ∀ r, r ∉ B₀.carrier → G r = 0)
    {U V M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hmeanF : (𝔼 r ∈ B₀.carrier, F r) = U) (hmeanG : (𝔼 r ∈ B₀.carrier, G r) = V)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMU : 1 ≤ M * (c₀ * U)) (hMV : 1 ≤ M * (c₀ * V))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : |bilinearIntegral B₀.carrier B₀.carrier (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G -
      parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    bilinearIntegral B₀.carrier B₀.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G ≤
      (T * ((1 + rho) / 2) + Real.exp (-(D * p))) * (U * V) ^ (1 / 4 : ℝ) +
        Real.exp (-E) + matchingError := by
  intro rho
  obtain ⟨shape, active, hallowed, _, _, hpotential, hintegral⟩ :=
    exists_capped_parent_refinement B₀ L S hL hSpos hSwidth hSreg hSrank hfreq hlocalWidth
      hepsilon hp hD hR hH hSL hkappa hSB hrank hwidth hLshape A B F G origin hA hB hF hG
      hFsupport hGsupport hU hV hc₀ hK hmeanF hmeanG hfactor hparentF hparentG hM hMcap hMU hMV
      hSLmoment herror hSlog hcomplexity hprecision hcompare hW hWcap hQ hE ha hmatching
      m hm horder horders
  have h := parent_bound_of_selected_children (B₀.carrier ×ˢ B₀.carrier) L.carrier S.carrier
    (fun r => A r - (1 + epsilon) * B r) F G origin (fun z => (shape z).carrier) active hT hF hG
    (fun z hz _ => hchildren (shape z) (hallowed z hz).1) hpotential
    (by simpa only [add_assoc] using hintegral)
  nlinarith only [h]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem bilinear_refinement_step
    (B₀ L S : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hscale : scale ≤ 1 / (100 * (2 * max B₀.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B F G : ZMod N → ℝ) (origin : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hFsupport : ∀ r, r ∉ B₀.carrier → F r = 0)
    (hGsupport : ∀ r, r ∉ B₀.carrier → G r = 0)
    {M K c₀ cutoff : ℝ} (hc₀ : 0 < c₀) (hK : 0 < K) (hcutoff : 0 < cutoff)
    (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMcutoff : 1 ≤ M * (c₀ * cutoff))
    (htiny : W * cutoff ^ (3 / 4 : ℝ) ≤ Real.exp (-(D * p)))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : ∀ f g : ZMod N → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      |bilinearIntegral B₀.carrier B₀.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g -
        parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    let Phi := ((𝔼 r ∈ B₀.carrier, F r) * (𝔼 r ∈ B₀.carrier, G r)) ^ (1 / 4 : ℝ)
    bilinearIntegral B₀.carrier B₀.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G ≤
      (T * ((1 + rho) / 2) + Real.exp (-(D * p))) * Phi + Real.exp (-E) + matchingError +
        (W * (400 * (max B₀.rank 1 : ℕ) * (scale : ℝ))) *
          (((𝔼 r ∈ B₀.carrier, F r) + 𝔼 r ∈ B₀.carrier, G r) / (K * cutoff)) := by
  intro rho Phi
  have hgamma : 0 < γ := localMomentGain_pos δ
  have hgamma1 : γ ≤ 1 := (localMomentGain_le_half δ).trans (by norm_num)
  have hrho := (unbalanced_factor_bounds (M := K / c₀) hgamma hgamma1).1
  have hmatching0 : 0 ≤ matchingError := (abs_nonneg _).trans (hmatching F G hF hG)
  have hcapped : ∀ f g : ZMod N → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      (∀ r, r ∉ B₀.carrier → f r = 0) → (∀ r, r ∉ B₀.carrier → g r = 0) →
      cutoff ≤ (𝔼 r ∈ B₀.carrier, f r) → cutoff ≤ (𝔼 r ∈ B₀.carrier, g r) →
      (∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C → ∀ z,
        cellAverage C.carrier f z ≤ K * (𝔼 r ∈ B₀.carrier, f r)) →
      (∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C → ∀ z,
        cellAverage C.carrier g z ≤ K * (𝔼 r ∈ B₀.carrier, g r)) →
      bilinearIntegral B₀.carrier B₀.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g ≤
        (T * ((1 + rho) / 2) + Real.exp (-(D * p))) *
          ((𝔼 r ∈ B₀.carrier, f r) * (𝔼 r ∈ B₀.carrier, g r)) ^ (1 / 4 : ℝ) +
          (Real.exp (-E) + matchingError) := by
    intro f g hf hg hfs hgs hlu hlv hfcap hgcap
    have hMu : 1 ≤ M * (c₀ * (𝔼 r ∈ B₀.carrier, f r)) := hMcutoff.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlu hc₀.le) hM.le)
    have hMv : 1 ≤ M * (c₀ * (𝔼 r ∈ B₀.carrier, g r)) := hMcutoff.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlv hc₀.le) hM.le)
    have h := capped_parent_bound_of_children B₀ L S hL hSpos hSwidth hSreg hSrank
      hfreq hlocalWidth hepsilon hp hD hR hH hSL hkappa hSB hrank hwidth hLshape
      A B f g origin hA hB hf hg hfs hgs (hcutoff.trans_le hlu) (hcutoff.trans_le hlv)
      hc₀ hK.le rfl rfl hfactor hfcap hgcap hM hMcap hMu hMv hSLmoment herror hSlog
      hcomplexity hprecision hcompare hW hWcap hQ hE ha (hmatching f g hf hg)
      m hm horder horders hT hchildren
    simpa only [add_assoc] using h
  have h := bohr_parent_bound_from_capped B₀ hB₀ hscale extra minimumWidth hK hcutoff hKfactor
    hT (by linarith : 1 / 2 ≤ (1 + rho) / 2) (Real.exp_nonneg _) (by positivity) hW htiny
    (fun r => A r - (1 + epsilon) * B r) F G origin ha hF hG hFsupport hGsupport hchildren hcapped
  simpa only [add_assoc] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem admissible_child_bound_of_bounded_shapes
    (B₀ : CyclicBohr.Set N) {scale : ℝ≥0} {extra : ℕ} {minimumWidth T : ℝ}
    {a : ZMod N → ℝ} (hminimumWidth : 0 < minimumWidth)
    (hminimumWidth1 : minimumWidth ≤ 1) (hrank : 1 ≤ B₀.rank + extra)
    (hbounded : ∀ C : CyclicBohr.Set N, C.IsRankRegular → 0 < C.radius →
      1 ≤ C.rank → C.rank ≤ B₀.rank + extra → minimumWidth ≤ C.radius → C.radius ≤ 2 →
      CellBilinearBound C.carrier a T) :
    ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier a T := by
  intro C hC
  obtain ⟨hCreg, _, hCrank, hCwidth⟩ := hC
  obtain ⟨C', hcarrier, hreg, hpos, hrank1, hrankMax, hwidthMin, hwidthMax⟩ :=
    CyclicBohr.Set.exists_bounded_presentation C hCreg (hminimumWidth.trans_le hCwidth)
      hrank hCrank hminimumWidth1 hCwidth
  rw [← hcarrier]
  exact hbounded C' hreg hpos hrank1 hrankMax hwidthMin hwidthMax

theorem normalized_bilinear_refinement_step
    (B₀ L S : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hscale : scale ≤ 1 / (100 * (2 * max B₀.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B : ZMod N → ℝ)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    {M K c₀ cutoff : ℝ} (hc₀ : 0 < c₀) (hK : 0 < K) (hcutoff : 0 < cutoff)
    (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMcutoff : 1 ≤ M * (c₀ * cutoff))
    (htiny : W * cutoff ^ (3 / 4 : ℝ) ≤ Real.exp (-(D * p)))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : ∀ origin : ZMod N, ∀ f g : ZMod N → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      |bilinearIntegral B₀.carrier B₀.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g -
        parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
      (T * ((1 + rho) / 2) + Real.exp (-(D * p)) +
        (Real.exp (-E) + matchingError) / cutoff ^ 2 +
        2 * (W * (400 * (max B₀.rank 1 : ℕ) * (scale : ℝ))) / (K * cutoff ^ 3)) := by
  intro rho
  have hgamma : 0 < γ := localMomentGain_pos δ
  have hgamma1 : γ ≤ 1 := (localMomentGain_le_half δ).trans (by norm_num)
  have hrho := (unbalanced_factor_bounds (M := K / c₀) hgamma hgamma1).1
  have hmatching0 : 0 ≤ matchingError := (abs_nonneg _).trans
    (hmatching 0 (fun _ => 0) (fun _ => 0) (by intro r; norm_num) (by intro r; norm_num))
  apply cellBilinearBound_of_refinement B₀.carrier B₀.carrier_nonempty
    (fun r => A r - (1 + epsilon) * B r) hW
    (fun r => (le_abs_self _).trans (ha r)) hcutoff hK
    (mul_nonneg hT (by linarith : 0 ≤ (1 + rho) / 2))
    (add_nonneg (Real.exp_nonneg _) hmatching0) (by positivity) htiny
  intro origin f g hf hg hfs hgs _ _
  have h := bilinear_refinement_step B₀ L S hB₀ hL hSpos hSwidth hSreg hSrank
    hfreq hlocalWidth hepsilon hp hD hR hH hSL hkappa hscale hSB hrank hwidth hLshape
    A B f g origin hA hB hf hg hfs hgs hc₀ hK hcutoff hKfactor hfactor hM hMcap hMcutoff
    htiny hSLmoment herror hSlog hcomplexity hprecision hcompare hW hWcap hQ hE ha
    (hmatching origin) m hm horder horders hT hchildren
  simpa only [add_assoc] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem fixed_refinement_thresholds :
    2 ≤ (1 / 4 : ℝ) * (16 : ℝ) ^ (3 / 4 : ℝ) ∧
      ((1 / 256 : ℝ) * 16) ^ (1 / 4 : ℝ) ≤ 1 / 2 := by
  have hK := Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 4 (3 / 4 : ℝ)
  have hc := Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) 4 (1 / 4 : ℝ)
  norm_num at hK hc ⊢

noncomputable def refinementContraction (epsilon : ℝ) : ℝ :=
  1 - localMomentGain (flatComparisonDelta epsilon) / 1081600

theorem refinementContraction_eq (epsilon : ℝ) :
    refinementContraction epsilon =
      (1 + (1 - localMomentGain (flatComparisonDelta epsilon) /
        (128 * (1 + Real.sqrt ((16 : ℝ) / (1 / 256))) ^ 2))) / 2 := by
  norm_num [refinementContraction]
  ring

theorem refinementContraction_bounds (epsilon : ℝ) :
    0 ≤ refinementContraction epsilon ∧ refinementContraction epsilon < 1 := by
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := localMomentGain_le_half (flatComparisonDelta epsilon)
  unfold refinementContraction
  constructor <;> linarith

theorem refinement_cap_cutoff {p : ℝ} (hp : 512 ≤ p) :
    1 ≤ Real.exp p * ((1 / 256 : ℝ) * Real.exp (-p / 2)) := by
  have h : 256 ≤ Real.exp (p / 2) := by
    linarith [Real.add_one_le_exp (p / 2)]
  calc
    1 ≤ Real.exp (p / 2) / 256 := by linarith
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      ring_nf

theorem refinement_tiny_cutoff {p W : ℝ} (hW : W ≤ Real.exp (p / 8)) :
    W * (Real.exp (-p / 2)) ^ (3 / 4 : ℝ) ≤ Real.exp (-((1 / 4 : ℝ) * p)) := by
  calc
    _ ≤ Real.exp (p / 8) * (Real.exp (-p / 2)) ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg (Real.exp_nonneg _) _)
    _ = _ := by
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring

theorem refinement_return_error {p : ℝ} (hp : 0 ≤ p) :
    (Real.exp (-(2 * p)) + Real.exp (-(2 * p))) / (Real.exp (-p / 2)) ^ 2 ≤
      2 * Real.exp (-p / 4) := by
  have heq : (Real.exp (-(2 * p)) + Real.exp (-(2 * p))) / (Real.exp (-p / 2)) ^ 2 =
      2 * Real.exp (-p) := by
    rw [← Real.exp_nat_mul]
    rw [show Real.exp (-(2 * p)) + Real.exp (-(2 * p)) = 2 * Real.exp (-(2 * p)) by ring]
    rw [mul_div_assoc, ← Real.exp_sub]
    congr 2
    norm_num
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

theorem refinement_peeling_error {p loss : ℝ} (hp : 0 ≤ p)
    (hloss : loss ≤ Real.exp (-(3 * p))) :
    2 * loss / (16 * (Real.exp (-p / 2)) ^ 3) ≤ Real.exp (-p / 4) := by
  calc
    _ ≤ 2 * Real.exp (-(3 * p)) / (16 * (Real.exp (-p / 2)) ^ 3) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hloss (by norm_num))
        (by positivity)
    _ = Real.exp (-(3 * p / 2)) / 8 := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show 2 * Real.exp (-(3 * p)) / (16 * Real.exp (3 * (-p / 2))) =
        (Real.exp (-(3 * p)) / Real.exp (3 * (-p / 2))) / 8 by ring]
      rw [← Real.exp_sub]
      congr 2
      ring
    _ ≤ Real.exp (-(3 * p / 2)) := by nlinarith [Real.exp_pos (-(3 * p / 2))]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem refinement_total_error {p loss : ℝ} (hp : 0 ≤ p)
    (hloss : loss ≤ Real.exp (-(3 * p))) :
    Real.exp (-((1 / 4 : ℝ) * p)) +
      (Real.exp (-(2 * p)) + Real.exp (-(2 * p))) / (Real.exp (-p / 2)) ^ 2 +
      2 * loss / (16 * (Real.exp (-p / 2)) ^ 3) ≤ 4 * Real.exp (-p / 4) := by
  have hreturn := refinement_return_error hp
  have hpeeling := refinement_peeling_error hp hloss
  rw [show -((1 / 4 : ℝ) * p) = -p / 4 by ring]
  linarith

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

theorem refinement_enlargement_bounds {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 512 ≤ A) :
    512 ≤ (A : ℝ) * (p + 1) ∧ p ≤ (A : ℝ) * (p + 1) ∧
      (A : ℝ) ≤ (A : ℝ) * (p + 1) := by
  have hAR : (512 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem refinement_enlargement_amplitude {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 40 ≤ A) :
    2 * Real.exp p ≤ Real.exp (((A : ℝ) * (p + 1)) / 8) := by
  have hAR : (40 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  calc
    _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (1 + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem refinement_enlargement_error {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 40 ≤ A) :
    2 * Real.exp (-((A : ℝ) * (p + 1)) / 8) ≤ Real.exp (-4 * p) := by
  have hAR : (40 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  calc
    _ ≤ Real.exp 1 * Real.exp (-((A : ℝ) * (p + 1)) / 8) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (1 + -((A : ℝ) * (p + 1)) / 8) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem signed_comparison_amplitude {a b p epsilon : ℝ}
    (ha : 0 ≤ a ∧ a ≤ Real.exp p) (hb : 0 ≤ b ∧ b ≤ Real.exp p)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    |a - (1 + epsilon) * b| ≤ 2 * Real.exp p := by
  have hlo := mul_nonneg (show 0 ≤ 1 + epsilon by linarith) hb.1
  have hhi := mul_le_mul_of_nonneg_right (show 1 + epsilon ≤ 2 by linarith) hb.1
  exact abs_le.mpr ⟨by nlinarith, by nlinarith [Real.exp_pos p]⟩

end Erdos3.CellRefinement

end

end OAI
