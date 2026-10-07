/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Linear.ProjectedBasisSpan

namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate Set Module Submodule

theorem exists_integral_spanning_product_certificate :
    ∀ {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)),
      ∃ C : SuccessiveProductCertificate
        (span ℤ (Set.range b)).toAddSubgroup (fun _ ↦ 1)
        (minkowskiSecondConstant n * |(Matrix.of b).det|),
      span ℤ (Set.range C.point) = span ℤ (Set.range b) := by
  intro n
  induction n with
  | zero =>
      intro b
      refine ⟨{
        scale := fun i ↦ Fin.elim0 i
        point := fun i ↦ Fin.elim0 i
        scale_nonneg := fun i ↦ Fin.elim0 i
        point_mem := fun i ↦ Fin.elim0 i
        independent := linearIndependent_empty_type
        mem_scaledBox := fun i ↦ Fin.elim0 i
        product_le := ?_ }, ?_⟩
      · simp [minkowskiSecondConstant]
      · simp
  | succ n ih =>
      intro b
      classical
      let L : Submodule ℤ (Fin (n + 1) → ℝ) := span ℤ (Set.range b)
      obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_nonzero_of_basis b
      let vL : L := ⟨v, hvL⟩
      have hvL0 : vL ≠ 0 := by
        intro h
        apply hv0
        exact congrArg Subtype.val h
      have hμpos : ∀ x : L, x ≠ 0 → 0 < ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact norm_pos_iff.mpr (by
          intro h
          apply hx
          exact Subtype.ext h)
      have hμhom : ∀ (c : ℤ), 0 < c → ∀ x : L,
          ‖((c • x : L) : Fin (n + 1) → ℝ)‖ =
            (c : ℝ) * ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro c hc x
        have hcast : (((c • x : L) : Fin (n + 1) → ℝ)) =
            (c : ℝ) • (x : Fin (n + 1) → ℝ) := by
          ext i
          simp
        rw [hcast]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos]
        exact_mod_cast hc
      have hμmin : ∀ x : L, x ≠ 0 →
          ‖(vL : Fin (n + 1) → ℝ)‖ ≤ ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact hvmin x x.property (by
          intro h
          apply hx
          exact Subtype.ext h)
      obtain ⟨-, Bz, hBz0⟩ :=
        Erdos3.BohrLattice.PrimitiveExtension.shortest_zspan_vector_primitive_and_extends
          (Nat.succ_pos n) b vL hvL0
          (fun x : L ↦ ‖(x : Fin (n + 1) → ℝ)‖) hμpos hμhom hμmin
      let b' : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ) :=
        Bz.ofZLatticeBasis ℝ L
      have hb'0 : b' 0 = v := by
        rw [show b' 0 = ((Bz 0 : L) : Fin (n + 1) → ℝ) by
          exact Basis.ofZLatticeBasis_apply ℝ L Bz 0]
        exact congrArg Subtype.val (by simpa using hBz0)
      have hb'span : span ℤ (Set.range b') = L := by
        exact Bz.ofZLatticeBasis_span ℝ L
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (Matrix.of b')ᵀ
      have hMdet : M.det ≠ 0 := by
        have hbdet : (Pi.basisFun ℝ (Fin (n + 1))).det b' ≠ 0 :=
          (AlternatingMap.map_basis_ne_zero_iff b'
            (Pi.basisFun ℝ (Fin (n + 1))).det).mpr
              (Pi.basisFun ℝ (Fin (n + 1))).det_ne_zero
        rw [Pi.basisFun_det_apply] at hbdet
        simpa [M] using hbdet
      obtain ⟨h, hh⟩ := exists_abs_apply_eq_norm v
      have hvh : v h ≠ 0 := by
        intro hz
        have : ‖v‖ = 0 := by simpa [hz] using hh.symm
        exact hv0 (norm_eq_zero.mp this)
      have hMh0 : M h 0 ≠ 0 := by
        simpa [M, Matrix.of_apply, hb'0] using hvh
      let Q : Matrix (Fin n) (Fin n) ℝ := projectedTail h M
      have hQdet : Q.det ≠ 0 := projectedTail_det_ne_zero h M hMdet hMh0
      let qB : Basis (Fin n) ℝ (Fin n → ℝ) := projectedTailBasis h M hMdet hMh0
      obtain ⟨cq, hcqspan⟩ := ih qB
      have hQpoint : ∀ j, ∃ z : Fin n → ℤ,
          Matrix.mulVec Q (intCastVec z) = cq.point j := by
        intro j
        have hm := cq.point_mem j
        change cq.point j ∈ span ℤ (Set.range qB) at hm
        rw [Submodule.mem_span_range_iff_exists_fun] at hm
        obtain ⟨z, hz⟩ := hm
        refine ⟨z, ?_⟩
        rw [← hz]
        ext i
        simp [Q, qB, Matrix.mulVec, dotProduct, intCastVec, mul_comm]
      choose z hz using hQpoint
      let raw : Fin n → Fin (n + 1) → ℝ := fun j ↦ rawTailLift M (z j)
      let a : Fin n → ℤ := fun j ↦ -roundedCoefficient (raw j h / v h)
      let lift : Fin n → Fin (n + 1) → ℝ :=
        fun j ↦ raw j + (a j) • v
      let scale : Fin (n + 1) → ℝ := Fin.cons ‖v‖ (fun j ↦ 2 * cq.scale j)
      let point : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons v lift
      have hraw_eq : ∀ j, raw j = ∑ k, (z j k) • b' k.succ := by
        intro j
        ext i
        simp [raw, rawTailLift, M, Matrix.mulVec, dotProduct, intCastVec,
          Fin.sum_univ_succ, mul_comm]
      have hrawL : ∀ j, raw j ∈ L := by
        intro j
        rw [hraw_eq]
        rw [← hb'span]
        apply sum_mem
        intro k hk
        exact smul_mem _ _ (subset_span (Set.mem_range_self k.succ))
      have hliftL : ∀ j, lift j ∈ L := by
        intro j
        change raw j + (a j) • v ∈ L
        exact add_mem (hrawL j) (smul_mem L (a j) hvL)
      have hcol0 : (fun i ↦ M i 0) = v := by
        funext i
        simp [M, Matrix.of_apply, hb'0]
      have hproj_raw : ∀ j, deleteProjection h v (raw j) = cq.point j := by
        intro j
        rw [← hcol0]
        rw [deleteProjection_rawTailLift]
        exact hz j
      have hproj_lift : ∀ j, deleteProjection h v (lift j) = cq.point j := by
        intro j
        change deleteProjection h v (raw j + (a j) • v) = cq.point j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        rw [hcast, deleteProjection_add_smul h v (raw j) (a j : ℝ) hvh]
        exact hproj_raw j
      have hqnorm : ∀ j, ‖cq.point j‖ ≤ cq.scale j := by
        intro j
        apply (mem_realBox_const_iff_norm_le (cq.scale_nonneg j) _).mp
        rw [← realBox_smul_one_eq_const]
        exact cq.mem_scaledBox j
      have ha : ∀ j, |raw j h / v h + (a j : ℝ)| ≤ (1 : ℝ) / 2 := by
        intro j
        simpa [a, sub_eq_add_neg] using
          abs_sub_roundedCoefficient_le_half (raw j h / v h)
      have hlift_upper : ∀ j, ‖lift j‖ ≤ cq.scale j + ‖v‖ / 2 := by
        intro j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        change ‖raw j + (a j) • v‖ ≤ cq.scale j + ‖v‖ / 2
        rw [hcast]
        exact reducedLift_apply_le h v (raw j) (cq.scale j) (a j : ℝ)
          hh hvh (ha j) ((congrArg norm (hproj_raw j)).le.trans (hqnorm j))
      have hlift0 : ∀ j, lift j ≠ 0 := by
        intro j hj
        apply cq.independent.ne_zero j
        rw [← hproj_lift j, hj]
        ext i
        simp [deleteProjection]
      have hshortlift : ∀ j, ‖v‖ ≤ ‖lift j‖ := by
        intro j
        exact hvmin (lift j) (hliftL j) (hlift0 j)
      have hliftnorm : ∀ j, ‖lift j‖ ≤ 2 * cq.scale j := by
        intro j
        have hu := hlift_upper j
        have hs := hshortlift j
        linarith
      have hind : LinearIndependent ℝ point := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hprojrel : ∑ j, g j.succ • cq.point j = 0 := by
          have hm := congrArg (deleteProjectionLinear h v) hg
          rw [map_sum] at hm
          rw [Fin.sum_univ_succ] at hm
          simp only [point, Fin.cons_zero, Fin.cons_succ] at hm
          rw [map_smul, deleteProjectionLinear_apply,
            deleteProjection_self h v hvh, smul_zero, zero_add] at hm
          simp only [map_smul, deleteProjectionLinear_apply, map_zero] at hm
          simp_rw [hproj_lift] at hm
          exact hm
        have htail : ∀ j : Fin n, g j.succ = 0 :=
          (Fintype.linearIndependent_iff.mp cq.independent) _ hprojrel
        refine Fin.cases ?_ htail i
        rw [Fin.sum_univ_succ] at hg
        simp only [point, Fin.cons_zero, Fin.cons_succ] at hg
        simp_rw [htail] at hg
        simp only [zero_smul, Finset.sum_const_zero, add_zero] at hg
        exact (smul_eq_zero.mp hg).resolve_right hv0
      have hqdet : |(Matrix.of qB).det| = |Q.det| := by
        have hmat : Matrix.of qB = Qᵀ := by
          ext i j
          simp [qB, Q, Matrix.of_apply, Matrix.col]
        rw [hmat, Matrix.det_transpose]
      have hMabs : |M.det| = |(Matrix.of b).det| := by
        have hchange := abs_det_zspan_basis_eq b Bz
        have hmat : Matrix.of (((↑) : L → (Fin (n + 1) → ℝ)) ∘ Bz) =
            Matrix.of b' := by
          ext i j
          simp [b', Matrix.of_apply]
        rw [hmat] at hchange
        simpa [M] using hchange
      have hfactor : |(Matrix.of b).det| = ‖v‖ * |Q.det| := by
        rw [← hMabs]
        have hd := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h M hMh0
        have hentry : M h 0 = v h := congrFun hcol0 h
        rw [hentry, hh] at hd
        simpa [Q] using hd
      have hspan : span ℤ (Set.range point) = L := by
        have hz : deleteProjectionLinear h v (b' 0) = 0 := by
          rw [hb'0, deleteProjectionLinear_apply, deleteProjection_self h v hvh]
        have ht : ∀ j, deleteProjectionLinear h v (b' j.succ) = qB j := by
          intro j
          ext i
          simp [qB, projectedTail, M, deleteProjection, hb'0]
        have hw : ∀ j, lift j ∈ span ℤ (Set.range b') := by
          intro j
          rw [hb'span]
          exact hliftL j
        have hs : span ℤ (Set.range (fun j => deleteProjectionLinear h v (lift j))) =
            span ℤ (Set.range qB) := by
          simpa only [deleteProjectionLinear_apply, hproj_lift] using hcqspan
        have hhspan := span_fin_cons_of_projected_span b' qB
          (deleteProjectionLinear h v) hz ht lift hw hs
        simpa only [hb'0, hb'span] using hhspan
      refine ⟨{
        scale := scale
        point := point
        scale_nonneg := ?_
        point_mem := ?_
        independent := hind
        mem_scaledBox := ?_
        product_le := ?_ }, hspan⟩
      · intro i
        refine Fin.cases (norm_nonneg v) (fun j ↦ ?_) i
        exact mul_nonneg (by norm_num) (cq.scale_nonneg j)
      · intro i
        refine Fin.cases hvL (fun j ↦ hliftL j) i
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rw [realBox_smul_one_eq_const]
          apply (mem_realBox_const_iff_norm_le (norm_nonneg v) v).mpr
          simp
        · have hm := (mem_realBox_const_iff_norm_le
              (mul_nonneg (by norm_num) (cq.scale_nonneg j)) (lift j)).mpr
              (hliftnorm j)
          rw [realBox_smul_one_eq_const]
          simpa [scale, point] using hm
      · have hcq : ∏ j, cq.scale j ≤ minkowskiSecondConstant n * |Q.det| := by
          simpa [hqdet] using cq.product_le
        calc
          ∏ i, scale i = ‖v‖ * ((2 : ℝ) ^ n * ∏ j, cq.scale j) := by
            simp [scale, Fin.prod_univ_succ, Finset.prod_mul_distrib,
              Finset.prod_const]
          _ ≤ ‖v‖ * ((2 : ℝ) ^ n *
              (minkowskiSecondConstant n * |Q.det|)) := by
            gcongr
          _ = minkowskiSecondConstant (n + 1) * |(Matrix.of b).det| := by
            rw [minkowskiSecondConstant_succ, hfactor]
            ring

theorem exists_same_lattice_basis_norm_product_le {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    ∃ c : Basis (Fin n) ℝ (Fin n → ℝ),
      span ℤ (Set.range c) = span ℤ (Set.range b) ∧
      (∏ i, ‖c i‖) ≤ minkowskiSecondConstant n * |(Matrix.of b).det| := by
  obtain ⟨C, hspan⟩ := exists_integral_spanning_product_certificate b
  let c := basisOfLinearIndependentOfCardEqFinrank' C.point C.independent (by simp)
  have hc : ∀ i, c i = C.point i := by intro i; simp [c]
  refine ⟨c, ?_, ?_⟩
  · simpa only [show (c : Fin n → Fin n → ℝ) = C.point from funext hc] using hspan
  · apply le_trans (b := ∏ i, C.scale i) _ C.product_le
    apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
    rw [hc]
    apply (mem_realBox_const_iff_norm_le (C.scale_nonneg i) _).mp
    simpa only [realBox_smul_one_eq_const] using C.mem_scaledBox i

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
