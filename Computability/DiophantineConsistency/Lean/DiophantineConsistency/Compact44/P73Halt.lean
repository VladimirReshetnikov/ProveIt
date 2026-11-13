import DiophantineConsistency.Compact44.P73Graph
import DiophantineConsistency.Compact44.FreeJ13Halt

/-! # A positive zero of package 73's equation gives a free-J literal zero

At a positive zero all four residuals vanish. Take the 12-variable valuation
`x = ![3j+1, F, α, f−1, T, X, Y, r, η, ζ, Δi + u, γ]`. Then:

* its first and main residuals are 73's `A0` and `A1` (`P73Graph.first_lift`,
  `main_lift`);
* `As = 0` gives `Q = Δ(f²−1) = c⁴·(Δi)²`, the ordinary strong norm with
  index `Δi`. So `Aa = 0` and `FreeJ13.tail_forward` make the literal's polar
  residual vanish;
* `f − 1 > 0`, because `f = 1` would force `Δ(c²i)² = 0`.

`CompactSymbolicModelUnconditionalIff.model_iff` then gives an internal halt
of machine 215. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P73Halt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ ModelDifferenceRing P73Graph
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem eval_one_add {σ : Type*} (e : Expr σ) (w : σ → DiffRing V) :
    (1 + e).evalRing w = 1 + e.evalRing w := by
  simp [Expr.evalRing_add, Expr.evalRing_ofNat]

private theorem ι_pos {a : V} (h : 0 < a) : (0 : DiffRing V) < ι a := by
  simpa using (ι_lt_ι (V := V)).mpr h

/-- 13 → 12, for arbitrary integer ports. -/
theorem forward (p : Fin 4 → ℤ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph p).output v) :
    ∃ x : Fin 12 → V, (∀ j, 0 < x j) ∧ InternalZero (literal p) x := by
  obtain ⟨h0, h1, ha, hs⟩ := (zero_iff p v).mp hz
  rw [internalZero_iff] at h0 h1 ha hs
  set w : Fin 13 → DiffRing V := fun j => ι (v j) with hwdef
  rw [As_eval] at hs
  rw [Aa_eval] at ha
  obtain ⟨t, ht⟩ : ∃ t : V, v 3 = 1 + t :=
    ⟨v 3 - 1, (add_tsub_cancel_of_le (pos_iff_one_le.mp (hv 3))).symm⟩
  set ΔV : V := (3 + 4 * (v 6 * v 7 + v 7)) + (v 6 * v 7 + v 7) * (v 6 * v 7 + v 7) with hΔV
  let x : Fin 12 → V := ![1 + 3 * v 0, v 1, v 2, t, v 5, v 6, v 7, v 8, v 9, v 10, ΔV * v 4 + v 11, v 12]
  have hΔ : (vals p w).Delta = ι ΔV := by
    simp only [vals, hwdef, hΔV, map_add, map_mul, map_ofNat]
  have hw : (fun j => ι (x j)) = lift p w := by
    funext j
    fin_cases j
    · simp [x, lift, hwdef, map_add, map_mul, map_ofNat]
    · rfl
    · rfl
    · show ι t = w 3 - 1
      rw [hwdef]; simp [ht, map_add]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · show ι (ΔV * v 4 + v 11) = (vals p w).Delta * w 4 + w 11
      rw [hΔ]; simp [hwdef, map_add, map_mul]
    · rfl
  -- Q = c⁴(Δi)²
  have hc : 0 < (vals p w).c := by
    have h : (vals p w).c = ι (v 9 + v 7 * (v 9 + v 10)) := by
      simp only [vals, hwdef, map_add, map_mul]
    rw [h]; exact ι_pos (add_pos_of_pos_of_nonneg (hv 9) (Arithmetic.zero_le _))
  have hΔpos : 0 < (vals p w).Delta := by
    rw [hΔ]; exact ι_pos (add_pos_of_pos_of_nonneg (by norm_num) (Arithmetic.zero_le _))
  have hKaux : (vals p w).Kaux = (vals p w).Delta * (w 3 * w 3 - 1) := rfl
  have hQ : (vals p w).Kaux = ((vals p w).c * (vals p w).c) * ((vals p w).c * (vals p w).c) *
      (((vals p w).Delta * w 4) * ((vals p w).Delta * w 4)) := by
    rw [hKaux]; linear_combination (vals p w).Delta * hs
  have htpos : 0 < t := by
    rcases (Arithmetic.zero_le t).lt_or_eq with h | h
    · exact h
    · exfalso
      have hw3 : w 3 = 1 := by rw [hwdef]; simp [ht, ← h]
      rw [hw3] at hs
      have hi : (0 : DiffRing V) < w 4 := ι_pos (hv 4)
      have hpos : 0 < (vals p w).Delta *
          ((((vals p w).c * (vals p w).c) * w 4) * (((vals p w).c * (vals p w).c) * w 4)) := by
        positivity
      linarith
  have hA : ((vals p w).V + w 11) * ((vals p w).V + w 11) -
      (vals p w).Kaux * (((vals p w).V + w 11) * ((vals p w).V + w 11) - (vals p w).V * (vals p w).V) = 1 := by
    linear_combination ha
  have hord : (FreeJSumSquares.ordinaryResidual p).evalRing (fun j => ι (x j)) = 0 := by
    rw [hw, FreeJ13.ordinary_eval]
    dsimp only
    rw [q_lift, d_lift, z_lift, n_lift]
    exact FreeJ13.tail_forward _ _ _ _ _ hQ hA
  refine ⟨x, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [x, hv, htpos]
  · rw [FreeJCompletenessFactorBridge.zero_iff_factor_units]
    refine ⟨?_, ?_, ?_⟩
    · rw [FreeJSumSquares.first_decompose, FreeJ13.unit_iff_one, eval_one_add, hw, first_lift, h0]
      simp
    · rw [FreeJSumSquares.main_decompose, FreeJ13.unit_iff_one, eval_one_add, hw, main_lift, h1]
      simp
    · rw [FreeJSumSquares.ordinary_decompose, FreeJ13.unit_iff_one, eval_one_add, hord]
      simp

/-- A positive zero at the compact44 ports gives an internal halt of machine 215. -/
theorem halts (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph CompactSymbolicModelIff.p).output v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 :=
  (CompactSymbolicModelUnconditionalIff.model_iff (V := V)).mp (forward _ v hv hz)

end P73Halt

#print axioms P73Halt.forward
#print axioms P73Halt.halts
