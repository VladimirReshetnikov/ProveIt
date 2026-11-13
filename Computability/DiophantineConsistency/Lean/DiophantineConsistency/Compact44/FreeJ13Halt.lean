import DiophantineConsistency.Compact44.FreeJ13
import DiophantineConsistency.Compact44.FreeJGraphAuxiliary
import DiophantineConsistency.Compact44.QCube92Halt

/-! # The 13-positive, 87-operation graph halts exactly when machine 215 does

`positive_zero_iff` holds in every model of `𝗜𝚺₁`: the 87-operation graph has
a positive zero iff the 95-operation free-J literal has one, at the compact44
ports. The halting calibration of the literal then gives `positive_model_iff`.

* **13 → 12.** The four factors are units (`FreeJ13.factor_units`). The
  12-variable witness takes `t = f − 1` and `n = i + u`; `t > 0` because
  `Q = 0` would force `c²i = 0`. The ordinary residual then vanishes by
  `FreeJ13.tail_forward`.
* **12 → 13.** `FreeJGraphAuxiliary.graph_positive_auxiliary` supplies `i`,
  `Z` and `y` with `(icc)² = Q` and `Q·Z² = (Q−1)·y² + 1`, where `Z` is the
  value of `V`. Since `Z > c ≥ 1`, the second equation forces `y > Z`, so
  `u = y − Z` is positive. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJ13Halt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ ModelDifferenceRing
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactSymbolicModelIff FreeJOrdinaryTransport FreeJ13 FreeJQCube92Halt
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem eval_one_add {σ : Type*} (e : Expr σ) (w : σ → DiffRing V) :
    (1 + e).evalRing w = 1 + e.evalRing w := by
  simp [Expr.evalRing_add, Expr.evalRing_ofNat]

private theorem ι_pos {a : V} (h : 0 < a) : (0 : DiffRing V) < ι a := by
  simpa using (ι_lt_ι (V := V)).mpr h

/-- If `q ≥ 1`, `z > 1` and `q·z² = (q−1)·y² + 1` with `y ≥ 0`, then `y > z`. -/
private theorem aux_root_gt {q z y : DiffRing V} (hq : 1 ≤ q) (hz : 1 < z) (hy : 0 ≤ y)
    (h : q * (z * z) = (q - 1) * (y * y) + 1) : z < y := by
  by_contra hlt
  have hle : y ≤ z := le_of_not_gt hlt
  have hm : (q - 1) * (y * y) ≤ (q - 1) * (z * z) :=
    mul_le_mul_of_nonneg_left (mul_self_le_mul_self hy hle) (sub_nonneg.mpr hq)
  have hzz : 1 < z * z := by nlinarith
  nlinarith

/-- 13 → 12, for arbitrary integer ports. -/
theorem forward (p : Fin 4 → ℤ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph p).output v) :
    ∃ x : Fin 12 → V, (∀ j, 0 < x j) ∧ InternalZero (literal p) x := by
  obtain ⟨h0, h1, ha, hs⟩ := factor_units p v hz
  rw [unit_iff_one] at h0 h1 ha hs
  obtain ⟨t, ht⟩ : ∃ t : V, v 3 = 1 + t :=
    ⟨v 3 - 1, (add_tsub_cancel_of_le (pos_iff_one_le.mp (hv 3))).symm⟩
  let x : Fin 12 → V := ![v 0, v 1, v 2, t, v 5, v 6, v 7, v 8, v 9, v 10, v 4 + v 11, v 12]
  let x' : Fin 12 → DiffRing V := fun j => ι (x j)
  have hw : (fun j => ι (v j)) = embed x' (ι (v 4)) (ι (v 11)) := by
    funext j
    fin_cases j <;> simp [embed, x', x, ht]
  rw [hw] at h0 h1 ha hs
  rw [eval_one_add, first_eval] at h0
  rw [eval_one_add, main_eval] at h1
  rw [aux_eval] at ha
  rw [strong_eval] at hs
  have hA0 : (FreeJSumSquares.firstResidual p).evalRing x' = 0 := by linear_combination h0
  have hA1 : (FreeJSumSquares.mainResidual p).evalRing x' = 0 := by linear_combination h1
  let c : DiffRing V := x' 8 + x' 6 * (x' 8 + x' 9)
  have hc : 0 < c := by
    have h8 : 0 < x' 8 := ι_pos (by simpa [x] using hv 9)
    have h6 : 0 ≤ x' 6 := ι_nonneg _
    have h9 : 0 ≤ x' 9 := ι_nonneg _
    dsimp only [c]
    positivity
  have hi : (0 : DiffRing V) < ι (v 4) := ι_pos (hv 4)
  have hQ : (parts p).q.evalRing x' = (parts p).d.evalRing x' * (ι (v 4) * ι (v 4)) := by
    rw [d_eval]
    linear_combination -hs
  have htpos : 0 < t := by
    rcases (Arithmetic.zero_le t).lt_or_eq with h | h
    · exact h
    · exfalso
      have hx3 : x' 3 = 0 := by simp [x', x, ← h]
      have hq0 : (parts p).q.evalRing x' = 0 := by rw [q_eval, hx3]; ring
      rw [hq0, d_eval] at hQ
      have hprod : (c * c * ι (v 4)) * (c * c * ι (v 4)) = 0 := by
        dsimp only [c]; linear_combination -hQ
      have hcc : 0 < c * c * ι (v 4) := by positivity
      exact hcc.ne' (mul_self_eq_zero.mp hprod)
  have hn : (parts p).n.evalRing x' = ι (v 4) + ι (v 11) := by
    rw [n_eval]; simp [x', x]
  have hord : (FreeJSumSquares.ordinaryResidual p).evalRing x' = 0 := by
    rw [ordinary_eval]
    dsimp only
    rw [hn]
    exact tail_forward _ _ _ _ _ hQ ha
  refine ⟨x, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [x, hv, htpos]
  · rw [FreeJCompletenessFactorBridge.zero_iff_factor_units]
    refine ⟨?_, ?_, ?_⟩
    · rw [FreeJSumSquares.first_decompose, unit_iff_one, eval_one_add]
      change 1 + (FreeJSumSquares.firstResidual p).evalRing x' = 1
      rw [hA0]; simp
    · rw [FreeJSumSquares.main_decompose, unit_iff_one, eval_one_add]
      change 1 + (FreeJSumSquares.mainResidual p).evalRing x' = 1
      rw [hA1]; simp
    · rw [FreeJSumSquares.ordinary_decompose, unit_iff_one, eval_one_add]
      change 1 + (FreeJSumSquares.ordinaryResidual p).evalRing x' = 1
      rw [hord]; simp

/-- 12 → 13 at symbolic ports with the compact44 masks, as in
`FreeJGraphCongruenceExplore.symbolic_aligned`: the masks enter only through
`hL` and `hH`, never by unfolding. -/
theorem backward_ports (B K L H : ℕ)
    (hB : (B:V)+1 = Exp.exp ((67:V)*8807)) (hL : L = lowNat) (hH : H = highNat)
    (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (literal (fun j => (ports B K L H j : ℤ))) v) :
    ∃ w : Fin 13 → V, (∀ j, 0 < w j) ∧
      InternalZero (graph (fun j => (ports B K L H j : ℤ))).output w := by
  obtain ⟨hb', hl', hh', _⟩ := CompactMaskBoundFinish.bounds (B:V) (v 0) hB (hv 0)
  have hb : 0 < (ports B K L H 0 : V) := by change 0 < (B:V); exact hb'
  have hl : (ports B K L H 2 : V) < (ports B K L H 0 : V) := by
    change (L:V) < (B:V)
    rw [hL]
    exact hl'
  have hh : (ports B K L H 3 : V) < 2 * (ports B K L H 0 : V) := by
    change ((B+H:ℕ):V) < 2*(B:V)
    rw [Nat.cast_add, hH]
    exact hh'
  obtain ⟨_, i, Z, y, hipos, _, _, hstrong, hcZ, hzval, hypos, _, haux⟩ :=
    FreeJGraphAuxiliary.graph_positive_auxiliary (ports B K L H) v hb hl hh hv hz
  obtain ⟨h0, h1, _⟩ := literal_factor_units _ v hz
  rw [FreeJSumSquares.first_decompose, unit_iff_one, eval_one_add] at h0
  rw [FreeJSumSquares.main_decompose, unit_iff_one, eval_one_add] at h1
  let x' : Fin 12 → DiffRing V := fun j => ι (v j)
  have hA0 : (FreeJSumSquares.firstResidual (fun j => (ports B K L H j : ℤ))).evalRing x' = 0 := by
    linear_combination h0
  have hA1 : (FreeJSumSquares.mainResidual (fun j => (ports B K L H j : ℤ))).evalRing x' = 0 := by
    linear_combination h1
  let cV : V := v 8 + v 6 * (v 8 + v 9)
  let QV : V := ((3 + 4*(v 5*v 6+v 6)) + (v 5*v 6+v 6)*(v 5*v 6+v 6)) * ((1+v 3)*(1+v 3) - 1)
  have hstrong' : (i*cV*cV)*(i*cV*cV) = QV := hstrong
  have haux' : QV*(Z*Z) = (QV-1)*(y*y)+1 := haux
  have hzval' : (parts (fun j => (ports B K L H j : ℤ))).z.evalRing x' = ι Z := hzval
  have hcpos : 0 < cV := add_pos_of_pos_of_nonneg (hv 8) (Arithmetic.zero_le _)
  have hQpos : 1 ≤ QV := by
    rw [← hstrong']
    exact pos_iff_one_le.mp (mul_pos (mul_pos (mul_pos hipos hcpos) hcpos)
      (mul_pos (mul_pos hipos hcpos) hcpos))
  have hf1 : 1 ≤ (1+v 3)*(1+v 3) :=
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (Arithmetic.zero_le _))
      (le_add_of_nonneg_right (Arithmetic.zero_le _))
  have hsub : ∀ a : V, 1 ≤ a → ι (a - 1) = ι a - 1 := by
    intro a ha
    rw [eq_sub_iff_add_eq, ← map_one ι, ← map_add, tsub_add_cancel_of_le ha]
  have hQcast : (parts (fun j => (ports B K L H j : ℤ))).q.evalRing x' = ι QV := by
    rw [q_eval]
    simp only [QV, x', map_mul, map_add, hsub _ hf1, map_one, map_ofNat]
  have hauxD : ι QV * (ι Z * ι Z) = (ι QV - 1) * (ι y * ι y) + 1 := by
    have h := congrArg ι haux'
    simpa only [map_mul, map_add, map_one, hsub _ hQpos] using h
  have hZ1 : 1 < Z := lt_of_le_of_lt (pos_iff_one_le.mp hcpos) hcZ
  have hyZ : Z < y := by
    apply (ι_lt_ι (V := V)).mp
    have hZ1' : (1 : DiffRing V) < ι Z := by simpa using (ι_lt_ι (V := V)).mpr hZ1
    have hq1 : (1 : DiffRing V) ≤ ι QV := by simpa using (ι_le_ι (V := V)).mpr hQpos
    exact aux_root_gt hq1 hZ1' (ι_nonneg y) hauxD
  let u : V := y - Z
  have hupos : 0 < u := tsub_pos_of_lt hyZ
  have hucast : ι u = ι y - ι Z := by
    rw [eq_sub_iff_add_eq, ← map_add, tsub_add_cancel_of_le hyZ.le]
  let w : Fin 13 → V := ![v 0, v 1, v 2, 1 + v 3, i, v 4, v 5, v 6, v 7, v 8, v 9, u, v 11]
  have hw : (fun j => ι (w j)) = embed x' (ι i) (ι u) := by
    funext j
    fin_cases j <;> simp [embed, w, x']
  have hcx : x' 8 + x' 6 * (x' 8 + x' 9) = ι cV := by simp [x', cV, map_add, map_mul]
  have hsD : (ι cV * ι cV * ι i) * (ι cV * ι cV * ι i) = ι QV := by
    have h := congrArg ι hstrong'
    simp only [map_mul] at h
    linear_combination h
  have hF0 : (graph (fun j => (ports B K L H j : ℤ))).A0.evalRing (embed x' (ι i) (ι u)) = 0 := by
    rw [first_eval]; exact hA0
  have hF1 : (graph (fun j => (ports B K L H j : ℤ))).A1.evalRing (embed x' (ι i) (ι u)) = 0 := by
    rw [main_eval]; exact hA1
  have hFa : (graph (fun j => (ports B K L H j : ℤ))).aux.evalRing (embed x' (ι i) (ι u)) = 1 := by
    rw [aux_eval, hQcast, hzval', hucast]
    exact tail_backward _ _ _ hauxD
  have hFs : (graph (fun j => (ports B K L H j : ℤ))).strong.evalRing (embed x' (ι i) (ι u)) = 1 := by
    rw [strong_eval, hQcast, hcx]
    linear_combination hsD
  refine ⟨w, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [w, hv, hipos, hupos]
  · rw [internalZero_iff, hw, output_eq]
    simp only [Expr.evalRing_sub, Expr.evalRing_mul, eval_one_add, hF0, hF1, hFa, hFs]
    simp [Expr.evalRing_ofNat]

/-- 12 → 13 at the compact44 ports. -/
theorem backward (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (literal CompactSymbolicModelIff.p) v) :
    ∃ w : Fin 13 → V, (∀ j, 0 < w j) ∧ InternalZero (graph CompactSymbolicModelIff.p).output w :=
  backward_ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    (CompactFixedBeta.beta_identity (V := V)) rfl rfl v hv hz

theorem positive_zero_iff :
    (∃ v : Fin 13 → V, (∀ j, 0 < v j) ∧ InternalZero (graph CompactSymbolicModelIff.p).output v) ↔
      (∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ InternalZero (literal CompactSymbolicModelIff.p) v) := by
  constructor
  · rintro ⟨v, hv, hz⟩
    exact forward _ v hv hz
  · rintro ⟨v, hv, hz⟩
    exact backward v hv hz

theorem positive_model_iff :
    (∃ v : Fin 13 → V, (∀ j, 0 < v j) ∧ InternalZero (graph CompactSymbolicModelIff.p).output v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :=
  positive_zero_iff.trans (CompactSymbolicModelUnconditionalIff.model_iff (V := V))

#print axioms FreeJ13Halt.forward
#print axioms FreeJ13Halt.backward_ports
#print axioms FreeJ13Halt.backward
#print axioms FreeJ13Halt.positive_zero_iff
#print axioms FreeJ13Halt.positive_model_iff

end FreeJ13Halt