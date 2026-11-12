import P81NaturalForcedJ
import P82NaturalForced
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only 81-to-82 J-shift proposal. All declarations and imports are
unelaborated; the strict represented K0 premise is explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural81JShiftDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing

def down {R : Type*} [Sub R] [One R] (v : Fin 14 → R) : Fin 14 → R :=
  fun j => if j = 0 then v j - 1 else v j

/-- Ring identity with one changed coordinate, not a same-valuation claim. -/
theorem output_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P81NaturalForcedJ.graph p).output.evalRing v =
      (P82NaturalForced.graph p).output.evalRing (down v) := by
  simp [P81NaturalForcedJ.graph, P82NaturalForced.graph, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, down]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Literal guard cut at J=0; K0 must be represented by `κ` in the model. -/
theorem guard_zero_cut (p : Fin 4 → ℤ) (κ : V) (v : Fin 14 → V)
    (hK : (p 1 : DiffRing V) = ι κ) (hJ : v 0 = 0) :
    (P81NaturalForcedJ.graph p).guardFactor.evalRing (fun j => ι (v j)) =
      -(ι (v 1) + ι (v 2) + 1) * (ι (v 6) + 1 + ι κ) - ι (v 1) := by
  simp [P81NaturalForcedJ.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    hK, hJ, map_zero] <;> ring

/-- Strict K0 makes the guard at J=0 at most −2 in the difference ring. -/
theorem guard_at_most_negative_two (p : Fin 4 → ℤ) (κ : V) (v : Fin 14 → V)
    (hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ) (hJ : v 0 = 0) :
    (P81NaturalForcedJ.graph p).guardFactor.evalRing (fun j => ι (v j)) ≤ -2 := by
  rw [guard_zero_cut p κ v hK hJ]
  have h1 := ι_nonneg (v 1)
  have h2 := ι_nonneg (v 2)
  have h6 := ι_nonneg (v 6)
  have hkpos : (0 : DiffRing V) < ι κ := by
    simpa only [map_zero] using (ι_lt_ι.mpr hκ)
  have hkone : (1 : DiffRing V) ≤ ι κ :=
    ModelDifferenceRing.one_le_of_pos (fun x hx => pos_iff_one_le.mp hx) hkpos
  have hm : 0 ≤ (ι (v 1) + ι (v 2)) * (ι (v 6) + ι κ - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hm]

/-- Zero forces slot J positive; all factor-unit work is local to the guard. -/
theorem J_pos_of_zero (p : Fin 4 → ℤ) (κ : V) (v : Fin 14 → V)
    (hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)
    (hz : InternalZero (P81NaturalForcedJ.graph p).output v) : 0 < v 0 := by
  apply pos_iff_ne_zero.mpr
  intro hJ
  have hg := guard_at_most_negative_two p κ v hK hκ hJ
  have hzring := (ModelDifferenceRing.internalZero_iff _ _).mp hz
  rw [P81NaturalForcedJ.output_shape] at hzring
  simp only [Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Expr.evalRing_constant, Int.cast_one, Nat.cast_one] at hzring
  let P : DiffRing V := (P81NaturalForcedJ.graph p).first.evalRing (fun j => ι (v j)) *
    (P81NaturalForcedJ.graph p).main.evalRing (fun j => ι (v j)) *
    (P81NaturalForcedJ.graph p).aux.evalRing (fun j => ι (v j)) *
    (P81NaturalForcedJ.graph p).strong.evalRing (fun j => ι (v j))
  let G : DiffRing V := (P81NaturalForcedJ.graph p).guardFactor.evalRing (fun j => ι (v j))
  have hp : P*G = 1 := by dsimp [P,G]; exact sub_eq_zero.mp hzring
  have hG : G ≤ -2 := hg
  have hpneg : P < 0 := by
    by_contra h
    have hp0 : 0 ≤ P := le_of_not_gt h
    have hn := mul_nonpos_of_nonneg_of_nonpos hp0 (show G ≤ 0 by linarith)
    linarith
  have hpone : (1 : DiffRing V) ≤ -P :=
    ModelDifferenceRing.one_le_of_pos (fun x hx => pos_iff_one_le.mp hx) (neg_pos.mpr hpneg)
  have hm : 0 ≤ (-P-1)*(-G-2) := mul_nonneg (by linarith) (by linarith)
  nlinarith [hm]

def Related (v81 v82 : Fin 14 → V) : Prop :=
  v81 0 = v82 0 + 1 ∧ ∀ j, j ≠ 0 → v81 j = v82 j
def lift (v : Fin 14 → V) : Fin 14 → V :=
  fun j => if j = 0 then v j + 1 else v j

theorem related_lift (v : Fin 14 → V) : Related (lift v) v := by
  constructor
  · simp [lift]
  · intro j hj; simp [lift, hj]

theorem related_embedding {v81 v82 : Fin 14 → V} (h : Related v81 v82) :
    down (fun j => ι (v81 j)) = (fun j => ι (v82 j)) := by
  funext j
  fin_cases j <;> simp_all [Related, down, map_add, map_one]

theorem internalZero_iff_related (p : Fin 4 → ℤ) {v81 v82 : Fin 14 → V}
    (h : Related v81 v82) :
    InternalZero (P81NaturalForcedJ.graph p).output v81 ↔
      InternalZero (P82NaturalForced.graph p).output v82 := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    output_eval, related_embedding h]

/-- Proposed zero-existence transport, with represented positive K0 explicit. -/
theorem exists_zero_iff (p : Fin 4 → ℤ) (κ : V)
    (hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ) :
    (∃ v, InternalZero (P81NaturalForcedJ.graph p).output v) ↔
      ∃ w, InternalZero (P82NaturalForced.graph p).output w := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨j, hj⟩ := exists_add_of_le (pos_iff_one_le.mp (J_pos_of_zero p κ v hK hκ hv))
    let w : Fin 14 → V := fun t => if t = 0 then j else v t
    have hw : Related v w := by
      constructor
      · simpa [w] using hj
      · intro t ht; simp [w, ht]
    exact ⟨w, (internalZero_iff_related p hw).mp hv⟩
  · rintro ⟨w, hw⟩
    exact ⟨lift w, (internalZero_iff_related p (related_lift w)).mpr hw⟩

end DiophantineConsistency.Natural81JShiftDraft
